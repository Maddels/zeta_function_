freeze; 

intrinsic ComputeY(F::RngMPolElt) -> SeqEnum
{Computes the scheme Y_0 defined in the paper}
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  Rt<t> := PolynomialRing(BaseRing(Rxy));
  x_coord_map := hom< Rxy-> Rt | [t, 1]>;
  a_n := x_coord_map(Coefficient(F, y, Degree(F, y)));
  Fx := Derivative(F,x);
  Fy := Derivative(F,y);
  r_1 := Resultant(Fx, F, y);
  r_2 := Resultant(Fy, F, y);
  H := GCD([x_coord_map(r_1), x_coord_map(r_2)]);
  L_1 := Factorisation(a_n);
  L_2 := Factorisation(H);
  L := [l[1] : l in L_1 cat L_2];
  L := SetToSequence(Seqset(L));
  return L;
end intrinsic;

intrinsic CountPointsOnZ(F::RngMPolElt, L::SeqEnum, D::RngIntElt) -> SeqEnum
{Counts the points on subscheme Z = Z_0 union (X\X_0) of the projective curve X defined by F
in extensions of degree 1 up to D}
  counts := [0 : _ in [1..D]];
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  base_field := BaseRing(Rxy);
  Rs<s> := PolynomialRing(BaseRing(Rxy));
  
  //counting points on Z_0 = phi^{-1}(Y_0)
  for h in L do
    h_extension := ext<base_field | Degree(h)>;
    _, a := HasRoot(h, h_extension);
    F_mod_h := Evaluate(F, [a, ChangeRing(s, Parent(a))]);
    F_mod_h_factors := Factorisation(F_mod_h);
    F_mod_h_factors := [l[1] : l in F_mod_h_factors];
    for l in F_mod_h_factors do
      closed_point_degree := Degree(h)*Degree(l);
      for r := closed_point_degree to D by closed_point_degree do
        counts[r] +:= closed_point_degree;
      end for;
    end for;
  end for;

  //counting points on X\X_0, i.e. points on X on the line at infinity
  F_infinity := HomogeneousComponent(F, Degree(F));
  F_infinity_factors := Factorisation(F_infinity);
  F_infinity_factors := [l[1] : l in F_infinity_factors];
  for l in F_infinity_factors do
    closed_point_degree := Degree(l);
    for r := closed_point_degree to D by closed_point_degree do
      counts[r] +:= closed_point_degree;
    end for;
  end for;
  return counts;
end intrinsic;

intrinsic CountPointsAboveZ(F::RngMPolElt, L::SeqEnum, D::RngIntElt) -> SeqEnum
{Counts the points on the nonsingular curve defined by F that 
lie above points on subscheme Y of the projective line, in extensions of degree 1 up to D}
  counts := [0 : _ in [1..D]];
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  
  base_field := BaseRing(Rxy);
  Rx1<x_1> := PolynomialRing(base_field);
  Rx2<x_2> := PolynomialRing(Rx1);
  x_coord_map := hom< Rxy-> Rx1 | [x_1, 1]>;
 
  coefficients_y := Coefficients(F, y);
  n := Degree(F, y); a_n := coefficients_y[n+1];
  F_prime := x_2^n + &+[x_coord_map(coefficients_y[i])*x_coord_map(a_n)^(n-i)*x_2^(i-1): i in [1..n] ];
  function_field_F_prime := FunctionField(F_prime);

  //counting points above Y_0
  for h in L do 
    h_x_1 := Evaluate(h, x_1);
    Montes(function_field_F_prime, h_x_1);
    prime_ideal_factors := function_field_F_prime`PrimeIdeals[h_x_1];
    for factor in prime_ideal_factors do
      closed_point_degree := Degree(factor);
      for r := closed_point_degree to D by closed_point_degree do
        counts[r] +:= closed_point_degree;
      end for; 
    end for;
  end for;

  //counting points above infinity
  closed_pts_above_infty := InfinitePlaces(function_field_F_prime);
  for closed_pt in closed_pts_above_infty do
    closed_point_degree := Degree(closed_pt);
    for r := closed_point_degree to D by closed_point_degree do
      counts[r] +:= closed_point_degree;
    end for;
  end for;

  return counts;
end intrinsic;

intrinsic ComputeCorrections(F::RngMPolElt, D::RngIntElt) -> SeqEnum
{Computes the difference between point-counts in extensions from 1 up to D
for the nonsingular curve defined by F versus the projective plane curve defined by F}
  L := ComputeY(F);
  count_on_Z := CountPointsOnZ(F, L, D);
  count_above_Z := CountPointsAboveZ(F, L, D);
  corrections := [count_above_Z[i] - count_on_Z[i] : i in [1..D]];
  return corrections;
end intrinsic;



//below are optimised versions of functions: optimised to avoid counting points above infinity
//when it is unnecessary to do so.
intrinsic CountPointsOnZ(F::RngMPolElt, L::SeqEnum, D::RngIntElt, no_infty::BoolElt) -> SeqEnum
{Counts the points on subscheme Z = Z_0 union (X\X_0) of the projective curve X defined by F
in extensions of degree 1 up to D. Avoids counting points on (X\X_0) if no_infty is set to true.}
  if no_infty eq false then
    return CountPointsOnZ(F,L,D);
  end if;

  counts := [0 : _ in [1..D]];
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  base_field := BaseRing(Rxy);
  Rs<s> := PolynomialRing(BaseRing(Rxy));
  
  //counting points on Z_0 = phi^{-1}(Y_0)
  for h in L do
    h_extension := ext<base_field | Degree(h)>;
    _, a := HasRoot(h, h_extension);
    F_mod_h := Evaluate(F, [a, ChangeRing(s, Parent(a))]);
    F_mod_h_factors := Factorisation(F_mod_h);
    F_mod_h_factors := [l[1] : l in F_mod_h_factors];
    for l in F_mod_h_factors do
      closed_point_degree := Degree(h)*Degree(l);
      for r := closed_point_degree to D by closed_point_degree do
        counts[r] +:= closed_point_degree;
      end for;
    end for;
  end for;

  return counts;
end intrinsic;

intrinsic CountPointsAboveZ(F::RngMPolElt, L::SeqEnum, D::RngIntElt, no_infty::BoolElt) -> SeqEnum
{Counts the points on the nonsingular curve defined by F that 
lie above points on subscheme Y of the projective line, in extensions of degree 1 up to D.
Avoids counting points above infinity if no_infty is set to true.}
  if no_infty eq false then
    return CountPointsAboveZ(F,L,D);
  end if;
  
  counts := [0 : _ in [1..D]];
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  
  base_field := BaseRing(Rxy);
  Rx1<x_1> := PolynomialRing(base_field);
  Rx2<x_2> := PolynomialRing(Rx1);
  x_coord_map := hom< Rxy-> Rx1 | [x_1, 1]>;
 
  coefficients_y := Coefficients(F, y);
  n := Degree(F, y); a_n := coefficients_y[n+1];
  F_prime := x_2^n + &+[x_coord_map(coefficients_y[i])*x_coord_map(a_n)^(n-i)*x_2^(i-1): i in [1..n] ];
  function_field_F_prime := FunctionField(F_prime);

  //counting points above Y_0
  for h in L do 
    h_x_1 := Evaluate(h, x_1);
    Montes(function_field_F_prime, h_x_1);
    prime_ideal_factors := function_field_F_prime`PrimeIdeals[h_x_1];
    for factor in prime_ideal_factors do
      closed_point_degree := Degree(factor);
      for r := closed_point_degree to D by closed_point_degree do
        counts[r] +:= closed_point_degree;
      end for; 
    end for;
  end for;

  return counts;
end intrinsic;


intrinsic ComputeCorrections(F::RngMPolElt, D::RngIntElt, opt::BoolElt) -> SeqEnum
{Computes the difference between point-counts in extensions from 1 up to D
for the nonsingular curve defined by F versus the projective plane curve defined by F.
If opt = true, checks if we need to bother counting points above infinity or not.}
  if opt eq false then 
    return ComputeCorrections(F, D);
  end if;
  //check if there are any corrections that need to be made above pt [1:0] on P^1
  //if so, we resort to the usual ComputeCorrections
  //if not, we use optimised compute corrections that does not count pts above infinity
  Rxy := Parent(F);  x:=Rxy.1; y := Rxy.2;
  n := Degree(F, y); d := Degree(F);
  singular_special_pt := false;
  //first check the special case of [0:1:0]
  if (d-n) ge 2 then
    //this means [0:1:0] is on X, and is singular
    //but it may be possible that [0:1:0] does not "lie over" [1:0] on P^1
    //i.e. it may be possible that *all* the points on \tilde{X} lying over
    //[0:1:0] have their x-coordinate in (P^1 \ [1:0]) = A^1
    //this happens if and only if a_n(x) has degree equal to d-n
    //so if a_n(x) has degree smaller than d-n, then we will have to correct for
    //points over infinity
    a_n := Coefficient(F, y, n);
    if Degree(a_n) lt (d-n) then 
      return ComputeCorrections(F, D);
    end if;
    //recording that [0:1:0] is singular
    singular_special_pt := true;
  end if;
  //now check the points of the form [1:t:0], i.e. the points where we *know* Z/X = (1/x) = 0 on X
  F_infinity := HomogeneousComponent(F, Degree(F));
  //finding points of the form [1:a:0] on X and checking if singular
  base_field := BaseRing(Rxy); Rt<t> := PolynomialRing(base_field);
  F_infinity_affine_line := Evaluate(F_infinity,[1,t]);
  factors := Factorisation(F_infinity_affine_line);
  //homogenising a_n(x) y^n + ... + a_0(x) by Z, then dehomogenising by X 
  //gives a polynomial of the form F_yz(y,z) = b_n(z) y^n + ... + b_1(z) y + b_0(z),
  //where if a_i(x) = c_0 + ... + c_m x^m, then b_i(z) = c_0 z^(d-i) + ... + c_m z^(d-i-m)
  //for the purpose of computing first order partial derivatives, 
  //we only need the constant and linear term of each b_i.
  extract_constant_term := func<a, i, d | MonomialCoefficient(a, x^(d-i))>;
  extract_linear_term := func<a, i, d | (d-i-1) ge 0 select MonomialCoefficient(a, x^(d-i-1)) else 0>;
  constant_terms := [extract_constant_term(Coefficient(F, y, i), i, d) : i in [0..n]];
  linear_term_coefficients := [extract_linear_term(Coefficient(F,y,i), i, d) : i in [0..n]];
  for factor in factors do
    fac := factor[1];
    factor_extension := ext<base_field | Degree(fac)>;
    _, a := HasRoot(fac, factor_extension);
    //check if relevant derivatives are both zero at [1:a:0]
    F_yz_y := &+[constant_terms[i+1]*i*a^(i-1) : i in [1..n]];
    F_yz_z := &+[linear_term_coefficients[i+1]*a^i : i in [0..n] ];
    if F_yz_y eq 0 and F_yz_z eq 0 then
      //[1:a:0] is singular, so compute corrections the usual way
      return ComputeCorrections(F,D);
    end if;
  end for;

  //at this point we know that none of the singular points on X lie over [1:0]
  //so we can avoid computing corrections over [1:0] on P^1
  L := ComputeY(F);
  count_on_Z := CountPointsOnZ(F, L, D, true);
  if singular_special_pt eq true then
    //add 1 to the count for each extension, to account for [0:1:0] being singular
    count_on_Z := [count_on_Z[i] + 1 : i in [1..D]];
  end if;
  count_above_Z := CountPointsAboveZ(F, L, D, true);
  corrections := [count_above_Z[i] - count_on_Z[i] : i in [1..D]];
  return corrections;  
end intrinsic;






      






















  






  


    