Attach("compute_corrections.m");
Attach("count_plane_model.m");
import "correctness_checks.m": CheckAgreementInExtension;

function OptimisedComputeZetaFunctionNumerator(F)
  ResetMaximumMemoryUsage();
  overall_time := Cputime();
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  base_field := BaseRing(Rxy);
  
  if IsFinite(base_field) eq false then
    error "Polynomial is not defined over a finite field";
  end if;
  if IsPrimeField(base_field) eq false then
    error "Cannot handle non-prime fields yet";
  end if;
  if IsIrreducible(F) eq false then
    error "Input polynomial is not absolutely irreducible";
  end if;
  
  Rx1<x_1> := PolynomialRing(base_field);
  Rx2<x_2> := PolynomialRing(Rx1);
  x_coord_map := hom< Rxy-> Rx1 | [x_1, 1]>;
  coefficients_y := Coefficients(F, y); n := Degree(F,y);
  F_univariate := &+[x_coord_map(coefficients_y[i])*x_2^(i-1): i in [1..(n+1)] ];
  function_field_F_univariate := FunctionField(F_univariate);
  
  if ExactConstantField(function_field_F_univariate) ne base_field then
    error "Input polynomial is not absolutely irreducible";
  end if;
  if Degree(F) le 2 then
    //genus is definitely zero
    return 1, 0, 0, 0, Cputime(overall_time), GetMaximumMemoryUsage() div (1024^2);
  end if;

  p := Characteristic(base_field);
  g := Genus(function_field_F_univariate);
  print "Genus is", g;
  if g eq 0 then
    return 1, 0, 0, 0, Cputime(overall_time), GetMaximumMemoryUsage() div (1024^2);
  end if;
  //lambda determines the precision of all matrix entries in the trace formula.
  lambda := Floor(g/2+Log(p,4*g)) + 1;
  
  plane_model_counts, polynomial_time, matrix_time := CountPlaneModel(F, g, lambda, g);

  corrections_time := Cputime();
  corrections := ComputeCorrections(F, g);
  corrections_time := Cputime(corrections_time);

  nonsingular_point_counts := [*plane_model_counts[i] + corrections[i] : i in [1..g] *];
  
  hasse_weil_errors := [0 : _ in [1..g]];
  lift_error := func<x, r, prec | (Integers()!x le 2*g*p^(r/2)) select Integers()!x else (Integers()!x - p^(prec))>;
  for r:=1 to g do
    prec := Floor(r/2 + Log(p, 4*g)) + 1;
    hasse_weil_error := lift_error(nonsingular_point_counts[r] - (p^r+1), r, prec);
    hasse_weil_errors[r] := (-1)*hasse_weil_error;
  end for;
  //hasse weil errors are power sums of the alpha_i, where numerator has form (1-alpha_1 T)...(1- alpha_2g T).

  elementary_symmetric := [1] cat [0 : _ in [1..g]];
  for i := 1 to g do
    //using newton girard identities (relations between power sum and elementary symmetric polynomials)
    e := 0;
    for j:=1 to i do
      e +:= (-1)^(j-1) * elementary_symmetric[(i-j)+1] * hasse_weil_errors[j];
    end for;
    e := e div i;
    elementary_symmetric[i+1] := e;
  end for; 

  //correcting the signs 
  coefficients := elementary_symmetric;
  for i := 2 to #coefficients by 2 do
    coefficients[i] := (-1)*coefficients[i];
  end for;

  //using functional equation to obtain remaining coefficients
  coefficients cat:= [0 : _ in [g+1..2*g]];
  for i := 0 to (g-1) do
    coefficients[2*g-i+1] := p^(g-i)*coefficients[i+1];
  end for;

  Rt<t> := PolynomialRing(Integers());
  numerator := Rt!coefficients;

  overall_time := Cputime(overall_time);
  max_mem_megabytes := GetMaximumMemoryUsage() div (1024^2);
  return numerator, polynomial_time, matrix_time, corrections_time, overall_time, max_mem_megabytes;
end function;

procedure runtime_in_genus(p, trials)
  R<x,y> := PolynomialRing(GF(p),2);
  P<x_0,x_1,x_2> := ProjectiveSpace(GF(p),2);
  for d:=6 to trials do
    lower_genus_limit := 1 + Ceiling(d*(d-6)/3);
    upper_genus_limit := Ceiling((d+1)*((d+1)-6)/3);
    for g := lower_genus_limit to upper_genus_limit do
      found := false;
      while found eq false do
        C := RandomNodalCurve(d, g, P);
        if IsIrreducible(C) then
          found := true;
        end if;
      end while;
      F := DefiningPolynomial(C);
      F := Evaluate(F, [x,y,1]);
      res, t_0, t_1, t_2, t_3, mem := OptimisedComputeZetaFunctionNumerator(F);
      print d, ",", g, ",", t_0, ",",  t_1, ",", t_2, ",",  t_3, ",", mem;
    end for;
  end for;
end procedure;

