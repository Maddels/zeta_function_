Attach("compute_corrections.m");
Attach("count_plane_model.m");
import "count_plane_model.m": ConvexHullMonomials, ComputeMatrix, make_bivariate_univariate;

//the following functions are for checking correctness of the implementation of the main algorithm.

//this function returns the point counts in extensions of degree 1 up to r
//for a nonsingular curve whose zeta function has zeta_numerator as the numerator
function PointCountsFromNumerator(zeta_numerator, p, r)
  coefficients := Coefficients(zeta_numerator);
  elementary_symmetric := coefficients;
  for i:= 2 to #coefficients by 2 do
    elementary_symmetric[i] := (-1)*elementary_symmetric[i];
  end for;

  power_sums := [0 : _ in [1..r]];
  zeta_numerator_degree := #coefficients-1;
  for i := 1 to Minimum(r, zeta_numerator_degree) do;
    power_sum := (-1)^(i-1)*i*elementary_symmetric[i+1]; 
    for j := 1 to (i-1) do 
      power_sum +:= (-1)^(i-1+j)*elementary_symmetric[i-j+1]*power_sums[j];
    end for;
    power_sums[i] := power_sum;
  end for;

  for i := (zeta_numerator_degree+1) to r do 
    power_sum := 0;
    for j := (i-zeta_numerator_degree) to (i-1) do
      power_sum +:= (-1)^(i-1+j)*elementary_symmetric[j-i+1]*power_sums[j];
    end for;
    power_sums[i] := power_sum;
  end for;

  point_counts := [(p^i+1) - power_sums[i] : i in [1..r]];
  return point_counts;
end function;

//this function counts the points on the projective plane curve defined by F
//either naively by enumeration, or by using the trace formula
function PlaneModelPointCountInExtension(F, p, g, r, use_trace_formula)
  lambda := Floor(r/2 + Log(p, 4*g)) + 1;
  if use_trace_formula eq false then
    count := 0;
    //count in affine space naively
    field_ext := GF(p^r);
    poly_ring<t> := PolynomialRing(field_ext);
    for a in field_ext do
      F_eval := Evaluate(F, [a,t]);
      factors := Factorisation(F_eval);
      for factor in factors do
        fac := factor[1];
        if Degree(fac) eq 1 then
          count := count+1;
        end if;
      end for;
    end for;
    //count points in P^2\A^2 on X
    F_infinity := HomogeneousComponent(F, Degree(F));
    F_infinity := ChangeRing(F_infinity, field_ext);
    factors := Factorisation(F_infinity);
    for factor in factors do
      fac := factor[1];
      if Degree(fac) eq 1 then
        count := count+1;
      end if;
    end for;
    //reduce to hasse-weil precisiion
    count := Integers(p^lambda)!count;
    return count;
  end if;
  //in this case, we use trace formula
  non_torus_count := 0;
  Rt<t> := PolynomialRing(GF(p^r)); 
  F_infinity := HomogeneousComponent(F, Degree(F));
  f_0 := Evaluate(F_infinity, [t, 1]);
  f_1 := Evaluate(F, [0,t]);
  f_2 := ReciprocalPolynomial(Evaluate(F, [t,0]));
  affine_line_polynomials := [f_0, f_1, f_2];
  for i:=1 to 3 do
    f := affine_line_polynomials[i];
    factorisation := Factorisation(f);
    for factor in factorisation do
      fac := factor[1];
      if Degree(fac) eq 1 then
        non_torus_count +:= 1;
      end if;
    end for;
  end for; 
  lambda := Floor(r/2 + Log(p, 4*g)) + 1;
  N := ConvexHullMonomials(F);  
  F_lift := ChangeRing(F, Integers());
  F_lift := ChangeRing(F_lift, Integers(p^lambda));
  F_lift := make_bivariate_univariate(F_lift, p, lambda);
  // Rxy := Parent(F_lift); x:=Rxy.1; y := Rxy.2;
  tau := Ceiling(lambda/((p-1))*r);
  S := (lambda + tau -1);
  traces := [Integers(p^lambda)!0: _ in [1..S]];
  alpha := func<lambda, tau, s | (-1)^s * &+[Binomial(-lambda, t)*Binomial(lambda, s-t) : t in [0..(tau-1)]]>;
  //computing all required traces
  for s := 1 to S do
    M_s := ComputeMatrix(F_lift, N, s, p);
    traces[s] := Trace(M_s^r);
  end for;
  //evaluating trace formula for r from 1 to D
  torus_count := Integers(p^lambda)!alpha(lambda, tau, 0);
  for s:=1 to S do
    torus_count +:= alpha(lambda, tau, s)*traces[s];
  end for;
  torus_count := torus_count*(p^r-1)^2;
  count := torus_count + non_torus_count;
  return count;
end function;  

//this function checks that an extension GF(p^r) point-count predicted by 
//a zeta numerator computed using our method agrees with the point-count
//predicted by counting in that extension naively or by trace formula
function CheckAgreementInExtension(zeta_numerator, F, r, use_trace_formula)
  g := Degree(zeta_numerator) div 2;
  p := Characteristic(Parent(F));
  lambda := Floor(r/2 + Log(p, 4*g)) + 1;
  output_nonsingular_point_counts := PointCountsFromNumerator(zeta_numerator, p, r);
  output_count := output_nonsingular_point_counts[r];
  //using optimised version of ComputeCorrections
  corrections := ComputeCorrections(F, r, true);
  count := PlaneModelPointCountInExtension(F, p, g, r, use_trace_formula);
  check_count := count + corrections[r];
  if Integers(p^lambda)!output_count eq Integers(p^lambda)!check_count then
    return true;
  end if;
  return false;
end function;

function CheckTorusPointCounts(F, p, g)
  counts := [**];
  for r:=1 to g do
    lambda := Floor(r/2+Log(p, 4*g)) + 1;
    precision_ring := Integers(p^lambda);
    ring := GF(p^r);
    ct := precision_ring!0;
    for a in ring do
      if a ne 0 then
        for b in ring do
          if b ne 0 then
            ct := ct + 1;
          end if;
        end for;
      end if;
    end for;
    Append(~counts, ct);
  end for;
  return counts;
end function;





    


