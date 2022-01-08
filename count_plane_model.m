freeze;

declare verbose Kyng, 2;

function ConvexHullMonomials(F)
  monomials := Monomials(F);
  points := [];
  for mon in monomials do
    i := Degree(mon, Parent(F).1);
    j := Degree(mon, Parent(F).2);
    Append(~points, [i,j]);
  end for;
  N := Polytope(points);
  return N;
end function;

function largest_power(s, upper_limits)
  D := #upper_limits;
  largest_pow := 1;
  for r:=1 to D do
    if upper_limits[r] ge s then
      //this means that matrix M_s occurs in the 
      //sum for the trace formula for |X(F_{p^r})|
      //meaning that the power M_s^r will be required
      largest_pow := r;
    end if;
  end for;
  return largest_pow;
end function;

function smallest_power(s, upper_limits)
  D := #upper_limits;
  smallest_pow := D;
  for r:=0 to (D-1) do
    if upper_limits[D-r] ge s then
      //this means that matrix M_s occurs in the 
      //sum for the trace formula for |X(F_{p^(D-r)})|
      //meaning that the power M_s^(D-r) will be required
      smallest_pow := D-r;
    end if;
  end for;
  return smallest_pow;
end function;

function make_bivariate_univariate(F, p, lambda)
  R<x> := PolynomialRing(Integers(p^lambda));
  bivariate_hom := hom<Parent(F) -> R | x, 0>;
  S<y> := PolynomialRing(R);
  d_y := Degree(F, 2);
  return &+[bivariate_hom(Coefficient(F, 2, i))*y^i : i in [0..d_y]];
end function;

intrinsic CountPointsOffTorus(F::RngMPolElt, p::RngIntElt, D::RngIntElt, lambda::RngIntElt, opt::BoolElt) -> SeqEnum
{Counts points on the projective closure of the curve defined by F, outside of T^2.}
  Rxy := Parent(F); x:=Rxy.1; y := Rxy.2;
  Rt<t> := PolynomialRing(GF(p)); 
  F_infinity := HomogeneousComponent(F, Degree(F));
  f_0 := Evaluate(F_infinity, [t, 1]);
  f_1 := Evaluate(F, [0,t]);
  ms:=Monomials(Coefficient(F,2,0));  cs:=Coefficients(Coefficient(F,2,0)); f_2 := &+[t^(Degree(F) - Degree(ms[i]))*cs[i] : i in [1..#ms]];
  affine_line_polynomials := [f_0, f_1, f_2];
  counts := [*0 : _ in [1..D]*];
  //counting points on X \cap U_i for i=0,1,2
  for i:=1 to 3 do
    f := affine_line_polynomials[i];
    factorisation := Factorisation(f);
    for factor in factorisation do
      closed_point_degree := Degree(factor[1]);
      for r := closed_point_degree to D by closed_point_degree do
        counts[r] +:= closed_point_degree;
      end for;
    end for;
  end for;
  return counts;
end intrinsic;

function ComputeMatrix(F_lift, N, s, p)
  t := Cputime();
  basis := IndexedSetToSequence(SetToIndexedSet(Points(s*N)));
  basis := [[w.1, w.2] : w in basis];
  F_lift_power := F_lift^((p-1)*s);
  // y_coeffs := AssociativeArray();
  t := Cputime(t);
  M := ZeroMatrix(BaseRing(BaseRing(Parent(F_lift))), #basis, #basis);
  for i:=1 to #basis do
    u := basis[i];
    for j :=1 to #basis do 
      v := basis[j];
      w_2 := p*v[2]-u[2]; 
      w_1 := p*v[1]-u[1];
      if w_2 ge 0 and w_1 ge 0 then
        y_coeff := Coefficient(F_lift_power, w_2);
        M[i, j] := Coefficient(y_coeff, w_1);
      end if;
    end for;
  end for;
  // function extract_coefficient(G, u, v) w_1 := p*v[1]-u[1]; w_2 := p*v[2]-u[2]; return w_1 ge 0 and w_2 ge 0 select Coefficient(y_coeffs[w_2], w_1) else 0; end function;
  // return Matrix([[extract_coefficient(F_lift_power, u, v): v in basis] : u in basis ]), t;
  return M, t;
end function;




intrinsic CountPointsOnTorus(F::RngMPolElt, p::RngIntElt, D::RngIntElt, lambda::RngIntElt, g::RngIntElt) -> List, FldReElt, FldReElt
{Counts the points on the curve defined by F inside the torus}
  N := ConvexHullMonomials(F);
  F_lift := ChangeRing(F, Integers());
  F_lift := ChangeRing(F_lift, Integers(p^lambda));
  F_lift := make_bivariate_univariate(F_lift, p, lambda);
  local_hasse_weil_bound := func<r | Floor(r/2 + Log(p, 4*g)) + 1>;
  required_precisions := [local_hasse_weil_bound(r) : r in [1..D]];
  hasse_weil_bound_tau := func<r | Ceiling(required_precisions[r]/((p-1)*r) )  >; 
  trace_formula_upper_limits := [required_precisions[r] + hasse_weil_bound_tau(r) - 1 : r in [1..D]];
  S := Maximum(trace_formula_upper_limits);
  traces := [[0 : _ in [1..D]] : _ in [1..S] ];
  //for each M_s, find the smallest power of it that we ever need to compute
  lower_limits := [smallest_power(s, trace_formula_upper_limits) : s in [1..S]];
  //for each M_s, find the largest power of it that we ever need to compute
  upper_limits := [largest_power(s, trace_formula_upper_limits) : s in [1..S]];
  cumulative_power_time := [];
  cumulative_matrix_time := [];
  for s := 1 to S do
    vprint Kyng, 2: "s is", s;
    matrix_time := Cputime();
    M_s, power_time := ComputeMatrix(F_lift, N, s, p);
    vprint Kyng, 2: "BaseRing of M_s", BaseRing(M_s);
    vprint Kyng, 2: "Build matrix", Cputime(matrix_time)-power_time;
    lower_limit := lower_limits[s]; upper_limit := upper_limits[s];
    curr_power := M_s^lower_limit;
    traces[s][lower_limit] := Trace(curr_power);
    for r := (lower_limit + 1) to upper_limit do 
      curr_power := curr_power * M_s;
      traces[s][r] := Trace(curr_power);
    end for;
    matrix_time := Cputime(matrix_time) - power_time;
    vprint Kyng, 2: "Build matrix + powers of matrix", matrix_time;
    Append(~cumulative_matrix_time, matrix_time);
    Append(~cumulative_power_time, power_time);
  end for;
  counts := [* *];
  alpha_s := func<s,tau,lambda | (-1)^s*(&+[Binomial(-lambda, t)*Binomial(lambda, s-t) : t in [0..tau-1]])>;
  for r := 1 to D do
    lambda_r := required_precisions[r];
    tau_r := hasse_weil_bound_tau(r);
    upper_limit := trace_formula_upper_limits[r];
    count := alpha_s(0, tau_r, lambda_r);
    count +:= &+[alpha_s(s, tau_r, lambda_r)*traces[s][r] : s in [1..upper_limit]];
    count := (p^r-1)^2*count;
    count := Integers(p^lambda_r)!count;
    Append(~counts, count);
  end for;
  return counts, &+cumulative_power_time, &+cumulative_matrix_time;
end intrinsic;

intrinsic CountPlaneModel(F::RngMPolElt, D::RngIntElt, lambda::RngIntElt, g::RngIntElt) -> List, FldReElt, FldReElt
{Counts points on the projective closure of the curve defined by F. 
If opt=true, then use the optimised torus point-counting function.}
  p := Characteristic(BaseRing(Parent(F)));
  torus_counts, polynomial_time, matrix_time := CountPointsOnTorus(F, p, D, lambda, g);
  non_torus_counts := CountPointsOffTorus(F, p, D, lambda, true);
  counts := [**];
  for r:=1 to D do
    torus_count := torus_counts[r];
    non_torus_count := non_torus_counts[r];
    Append(~counts, torus_count+non_torus_count);
  end for;
  return counts, polynomial_time, matrix_time;
end intrinsic;






