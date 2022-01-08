import "coho_p.m": mat_W0, mat_Winf, con_mat, jordan_0, jordan_inf, ram, basis_coho, ddx_mat;
import "auxpolys_p.m": auxpolys, genus, smooth, is_integral;

//we have some f(x,y) \in F_p[x,y] monic in y, with y-degree n, total degree m
//f(x,y) = y^n + a_{n-1}(x) y^{n-1} + ... + a_0(x)
//homogenising gives F(X,Y,Z) = Y^N Z^{m-n} + Y^{n-1} a_{n-1}(X,Z)+ ... + a_0(X,Z)
//we have a node (a:b:c) with field of definition F_{p^r}
//want to find f'(x,y) \in Z[x,y] with a node (a':b':c') where f'(x,y) mod p = f(x,y)
//and where (a':b':c') mod p = (a:b:c)


//given a,b,c in F_{p^r}, and F_{p^r}
//compute the number field to lift to, and choose a lift of a,b,c to this number field
function lift_node(a,b,c, field_of_defn)
  extension_poly := DefiningPolynomial(field_of_defn);
  lift_extension_poly := ChangeRing(extension_poly, Integers());
  r := Degree(field_of_defn);
  if r gt 1 then 
    L<t> := NumberField(lift_extension_poly);
    lift := func<x,t,r|&+[(Integers()!coeffs[i])*t^(i-1) : i in [1..r]] where coeffs:=Eltseq(x)>;
    lift_a := lift(field_of_defn!a,t,r);
    lift_b := lift(field_of_defn!b,t,r);
    lift_c := lift(field_of_defn!c,t,r);
  else 
    L := RationalField();
    lift_a := Integers()!a;
    lift_b := Integers()!b;
    lift_c := Integers()!c;
  end if;
  return lift_a, lift_b, lift_c, L;
end function;

//a,b,c are the node coordinates (in L). 
//L is the number field.
//output block matrix consisting of matrices M_0, ..., M_{r-1} stacked on top of each other
//where M=M_0 + tM_1 + ... + t^{r-1} M_{r-1} is the matrix in M_{4, dimension}(L)
//that specifies that the curve defined by f(x,y) has a singular point at (a:b:c)
function matrix_of_block_matrices_linear_conditions_node(a,b,c, y_degree, tot_degree, L, dimension)
  //this homomorphism just casts integer elements of L as magma integers
  r := Degree(L);
  if r gt 1 then
    H := hom< L -> Integers() | 0 >;
  else 
    H := hom< RationalField() -> Integers() | >;
  end if;
  pwr := func<x, k | x eq 0 and k lt 0 select 0 else x^k>;
  //each 4 rows are one block matrix. r block matrices since [L:Q] = r
  rows := [[0 : _ in [1..dimension]] : _ in [1..4*r]];
  ctr := 1;
  for j := 0 to (y_degree-1) do
    for i:= 0 to (tot_degree - j) do
      //getting coefficients for coefficient of x^i*y^j for the 4 linear equations
      k := tot_degree-(i+j);
      //this is condition F(a,b,c) = 0
      condition_1 := Eltseq(pwr(a,i)*pwr(b,j)*pwr(c,k));
      //this is condition F_x(a,b,c) = 0
      condition_2 := Eltseq(i*pwr(a,i-1)*pwr(b,j)*pwr(c,k)); 
      //this is condition F_y(a,b,c) = 0
      condition_3 := Eltseq(j*pwr(a,i)*pwr(b,j-1)*pwr(c,k)); 
      //this is condition F_z(a,b,c) = 0
      condition_4 := Eltseq(k*pwr(a,i)*pwr(b,j)*pwr(c,k-1)); 
      //putting the right Q-rational entries into the block matrices
      for l := 0 to (r-1) do
        rows[1+4*l][ctr] := H(condition_1[l+1]);
        rows[2+4*l][ctr] := H(condition_2[l+1]);
        rows[3+4*l][ctr] := H(condition_3[l+1]);
        rows[4+4*l][ctr] := H(condition_4[l+1]);
      end for;
      ctr +:= 1;
    end for;
  end for;
  //final condition, on coefficient of y^(y_degree)
  i := 0;
  j := y_degree;
  k := tot_degree-y_degree;
  condition_1 := Eltseq(pwr(a,i)*pwr(b,j)*pwr(c,k));
  condition_2 := Eltseq(i*pwr(a,i-1)*pwr(b,j)*pwr(c,k)); 
  condition_3 := Eltseq(j*pwr(a,i)*pwr(b,j-1)*pwr(c,k)); 
  condition_4 := Eltseq(k*pwr(a,i)*pwr(b,j)*pwr(c,k-1)); 
  //putting the right Q-rational entries into the block matrices
  for l := 0 to (r-1) do
    rows[1+4*l][ctr] := H(condition_1[l+1]);
    rows[2+4*l][ctr] := H(condition_2[l+1]);
    rows[3+4*l][ctr] := H(condition_3[l+1]);
    rows[4+4*l][ctr] := H(condition_4[l+1]);
  end for;
  M := Matrix(rows);
  return M;
end function;

//given a vector specifying the coefficients of a polynomial f(x,y) with the given y_degree and total_degree
//where the coefficients are given in the order: {1,x,...,x^m, y, yx, ..., yx^{m-1}, ..., y^n}
//create the associated polynomial defined with integer coefficients
function generate_polynomial_from_integer_vec(vec, y_degree, tot_degree)
  R<x,y> := PolynomialRing(Integers(), 2);
  poly := 0;
  ctr := 1;
  for j := 0 to (y_degree-1) do
    for i := 0 to (tot_degree-j) do
      coeff := vec[ctr];
      poly +:= coeff*x^i*y^j;
      ctr +:= 1;
    end for;
  end for;
  poly +:= vec[ctr]*y^(y_degree);
  return poly;
end function;

//given a vector specifying the coefficients of a polynomial f(x,y) with the given y_degree and total_degree
//where the coefficients are given in the order: {1,x,...,x^m, y, yx, ..., yx^{m-1}, ..., y^n}
//create the associated MONIC polynomial h(x,y) defined with integer coefficients. 
//i.e. the one obtained by doing h(x,a_n y) = a_n^{n-1} f(x, y), i.e. h(x,y) = a_n^{n-1} f(x,y/a_n)
function generate_monic_in_y_polynomial_from_integer_vec(vec, y_degree, tot_degree)
  R<x,y> := PolynomialRing(Integers(), 2);
  poly := 0;
  leading_coeff := vec[Ncols(vec)];
  ctr := 1;
  for j := 0 to (y_degree-1) do
    leading_coeff_factor := leading_coeff^(y_degree-1-j);
    for i := 0 to (tot_degree-j) do
      coeff := leading_coeff_factor*vec[ctr];
      poly +:= coeff*x^i*y^j;
      ctr +:= 1;
    end for;
  end for;
  poly +:= y^(y_degree);
  return poly;
end function;


//given a,b,c in a number field L=Q(t) (t here is root of some irreducible poly over Q) of degree r
//and given a MONIC in y f(x,y) in F_p[x,y], we want to create the matrix equation Au = -w
//so that v=v_0 + pu represents a lift of f(x,y) to Q that has a singular point at (a:b:c)
//note by MONIC in y we really need f(x,y) = a_0(x) + a_1(x) y + ... + a_{n-1}(x)y^{n-1} + y^n over F_p,
//specifically with the coefficient of y^n equal to 1
function lifted_curve_node_solns(f, a, b, c, L, p)
  r := Degree(L);
  x := Name(Parent(f),1);
  y := Name(Parent(f),2);
  y_degree := Degree(f, y);
  tot_degree := Degree(f);
  dimension := 1+Binomial(tot_degree+2, 2)-Binomial((tot_degree-y_degree)+2,2);
  // print(dimension);
  naive_lift_f :=  Matrix(Integers(), dimension, 1, [0 : _ in [1..dimension]]);
  //coefficients of f will be represented by a vector in space Q^(dimension), basis of this space
  //is {1, x,..., x^d, y, ..., yx^{d-1}, ..., y^n}
  ctr := 1;
  for j := 0 to (y_degree-1) do
    for i:= 0 to (tot_degree - j) do
      naive_lift_f[ctr][1] := Integers()!MonomialCoefficient(f, x^i*y^j);
      ctr +:= 1;
    end for;
  end for;
  naive_lift_f[ctr][1] := Integers()!MonomialCoefficient(f, y^y_degree);
  //compute matrix of size (4r)*(dimension) representing block matrices M_0, ..., M_{r-1}
  M := matrix_of_block_matrices_linear_conditions_node(a,b,c, y_degree, tot_degree, L, dimension);
  //we want to solve (M_0+tM_1+...+t^{r-1}M_{r-1})u = -(w_0+tw_1+...+t^{r-1}w_{r-1}) for u in Q^{dimension}
  //i.e. simultaneously solve systems M_i u = -w_i for i=0,...,r-1
  //w = M*v_0, where v_0 = naive_lift_f, M = M_0 + ... + t^{r-1}M_{r-1} 
  //compute vector constructed by stacking w_0, w_1, ..., w_{r-1} vertically
  // print(Parent(naive_lift_f));
  // print(Parent(M));
  w := M*naive_lift_f;
  for i := 1 to 4*r do
    w[i] := w[i] div p;
  end for;
  w := -1*w;
  has_soln := IsConsistent(Transpose(M), Transpose(w));
  if has_soln eq true then 
    //here we should be getting the space of solutions as well as a particular solution
    u := Solution(Transpose(M), Transpose(w));
    u := Transpose(u);
    lifted_vec := naive_lift_f + p*u;
    lifted_vec := Transpose(lifted_vec)[1];
    lifted_poly := generate_monic_in_y_polynomial_from_integer_vec(lifted_vec, y_degree, tot_degree);
  else 
    lifted_poly := -1;
  end if;
  return naive_lift_f, M, w, lifted_poly;
end function;



function create_w_vector_for_node(naive_lift_f, node_matrix, r, p)
  w := node_matrix*naive_lift_f;
  for i := 1 to 4*r do
    w[i] := w[i] div p;
  end for;
  w := -1*w;
  return w;
end function;



//input is a (MONIC in y) f in F_p[x,y], a list of pairs of nodes (a:b:c) on the projective curve defined by f
//and fields of definition of these nodes, where each pair is the representative of an orbit
//works as follows: 
//for each node (a:b:c) belonging to an orbit of nodes
//compute lift (lift_a:lift_b:lift_c) to a number field L
//compute matrix equations over Z which force (f') mod p = f, 
//and force f' to have a singular point at (lift_a:lift_b:lift_c)
//for each node i we get a system M_i u = -w_i over Z
//putting all of these systems together gives one big system  of the form Mu = w 
//which forces f' to have a singular point at all nodes in the list
function lift_curve_and_nodes(f, nodes_orbit_list, p)
  //replace the nodes in the orbit list with lifted versions
  x := Name(Parent(f),1);
  y := Name(Parent(f),2);
  y_degree := Degree(f,y);
  tot_degree := Degree(f);
  dimension := 1+Binomial(tot_degree+2, 2)-Binomial((tot_degree-y_degree)+2,2);
  M := Matrix(Integers(), 0, dimension, [] );
  w := Matrix(Integers(), 0,1, []);
  //naively lift f
  naive_lift_f :=  Matrix(Integers(), dimension, 1, [0 : _ in [1..dimension]]);
  //coefficients of f will be represented by a vector in space Q^(dimension), basis of this space
  //is {1, x,..., x^d, y, ..., yx^{d-1}, ..., y^n}
  ctr := 1;
  for j := 0 to (y_degree-1) do
    for i:= 0 to (tot_degree - j) do
      naive_lift_f[ctr][1] := Integers()!MonomialCoefficient(f, x^i*y^j);
      ctr +:= 1;
    end for;
  end for;
  naive_lift_f[ctr][1] := Integers()!MonomialCoefficient(f, y^y_degree);
  //go through all nodes in list
  for pair in nodes_orbit_list do
    // print pair;
    node := pair[1];
    field_of_defn := pair[2];
    a := node[1];
    b := node[2];
    c := node[3];
    a,b,c,L := lift_node(a,b,c,field_of_defn);
    // print a,b,c;
    r := Degree(L);
    node_matrix := matrix_of_block_matrices_linear_conditions_node(a,b,c,y_degree,tot_degree, L, dimension);
    // print node_matrix;
    M := VerticalJoin(M, node_matrix);
    //compute the relevant vector w for this matrix 
    node_w_vector := create_w_vector_for_node(naive_lift_f, node_matrix, r, p);
    w := VerticalJoin(w, node_w_vector);
  end for;
  //we now have the whole system and we can solve for u
  has_soln := IsConsistent(Transpose(M), Transpose(w));
  if has_soln eq true then 
    //here we should be getting the space of solutions as well as a particular solution
    u := Solution(Transpose(M), Transpose(w));
    u := Transpose(u);
    lifted_vec := naive_lift_f + p*u;
    lifted_vec := Transpose(lifted_vec)[1];
    lifted_poly := generate_monic_in_y_polynomial_from_integer_vec(lifted_vec, y_degree, tot_degree);
  else 
    lifted_poly := -1;
  end if;
  return naive_lift_f, M, w, lifted_poly;
end function;

//given f in F_p[x,y], make it monic and find node orbits
function make_monic_and_find_node_orbits(f)
  base_field := BaseRing(Parent(f));
  p := Characteristic(base_field);
  x := Name(Parent(f),1);
  y := Name(Parent(f),2);
  y_degree := Degree(f,y);
  //making the polynomial monic
  leading_coeff := Coefficient(f, y, y_degree);
  if leading_coeff eq MonomialCoefficient(f, y^y_degree) then
    //if the leading coefficient is just an element of F_p, just force it to be equal to 1
    g := MonomialCoefficient(f, y^y_degree)^(-1)*f;
  else
    g := 0;
    for j := 0 to (y_degree-1) do
      leading_coeff_factor := leading_coeff^(y_degree-1-j);
      g +:= Coefficient(f, y, j)*leading_coeff_factor*y^j;
    end for;
    g +:= y^(y_degree);
  end if;
  tot_degree := Degree(g);
  //now g is monic in y, defines plane curve birational to f=0
  //find the nodes on projective curve defined by g
  gx := Derivative(g, x);
  gy := Derivative(g, y);
  Re1 := Resultant(gx, gy, y);
  Re2 := Resultant(gx, g, y);
  Re3 := Resultant(gy, g, y);
  R1<x1> := PolynomialRing(base_field);
  proj1 := hom< Parent(f) -> R1 | [x1, 1]>;
  H := GCD([proj1(elt) : elt in [Re1, Re2, Re3]]);
  singular_point_orbits := [];
  if H ne 1 then
    // the curve is not smooth in the affine coordinate z = 1
    x_factors := Factorisation(H);
    for fac_x in x_factors do
      pol_x := fac_x[1];
      deg_x := Degree(pol_x);
      K<a> := GF(p^deg_x);
      Ku<u> := PolynomialRing(K);
      //one of the roots of irreducible factor pol
      xroot := Roots(Evaluate(pol_x, u))[1][1];
      y_factors := Factorisation(Evaluate(g, [xroot, u]));
      for fac_y in y_factors do
        pol_y := fac_y[1];
        deg_y := Degree(pol_y);
        L<b> := GF(p^(deg_x*deg_y));
        Lv<v> := PolynomialRing(L);
        yroot := Roots(Evaluate(pol_y, v))[1][1];
        // print xroot, yroot;
        g_x_value := Evaluate(gx, [xroot, yroot]);
        g_y_value := Evaluate(gy, [xroot, yroot]);
        // print g_x_value, g_y_value;
        if g_x_value eq 0 and g_y_value eq 0 then
          // print "found a point";
          sing_pt_pair := [* [xroot, yroot, 1], L *];
          Append(~singular_point_orbits, sing_pt_pair);
        end if;
      end for;
    end for;
  end if;
  // now deal with singularities at infinity
  // X := 1
  // Z := 0
  // so switch to other affine piece h(y,z) 
  // (but for us z is x; avoiding creating a new variable)
  h := 0;
  for j := 0 to (y_degree-1) do
    for i := 0 to tot_degree - j do
      k := tot_degree-i-j;
      h +:= MonomialCoefficient(g, x^i*y^j)*y^j*x^k;
    end for;
  end for;
  h +:= y^(y_degree)*x^(tot_degree-y_degree);
  // check if there are any singular points of the form h(0,y)
  y_factors := Factorisation(Evaluate(h, [0, x1]));
  //each factor is a point on h(y,z)
  for fac in y_factors do
    pol := fac[1];
    deg := Degree(pol);
    K<a> := GF(p^deg);
    Ku<u> := PolynomialRing(K);
    yroot := Roots(Evaluate(pol, u))[1][1];
    h_x_value := Evaluate(Derivative(h,x), [0, yroot]);
    h_y_value := Evaluate(Derivative(h,y), [0, yroot]);
    if h_x_value eq 0 and h_y_value eq 0 then
      sing_pt_pair := [* [1,yroot,0], K *];
      Append(~singular_point_orbits, sing_pt_pair);
    end if;
  end for;
  // check if (0:1:0) is a singular point
  // switch to affine piece s(x,z) where Y := 1
  // (but for us z is y; avoiding creating a new variable)
  h := y^(tot_degree-y_degree);
  for j := 0 to (y_degree-1) do
    for i := 0 to tot_degree - j do
      k := tot_degree - i - j;
      h +:= MonomialCoefficient(g, x^i*y^j)*x^i*y^k;
    end for;
  end for;
  h_x_value := Evaluate(Derivative(h,x), [0, 0]);
  h_y_value := Evaluate(Derivative(h,y), [0, 0]);
  if h_x_value eq 0 and h_y_value eq 0 then
    sing_pt_pair := [* [base_field!0,base_field!1,base_field!0], base_field *];
    Append(~singular_point_orbits, sing_pt_pair);
  end if;
  return g, singular_point_orbits;
end function;

//input is polynomial in Z[x,y]. output is polynomial in (Q[x])[y]
function change_poly_for_rational_function_field(poly)
  poly := ChangeRing(poly, RationalField());
  old_y := Parent(poly).2;
  y_degree := Degree(poly, old_y);
  R1<x> := PolynomialRing(RationalField());
  R<y> := PolynomialRing(R1);
  proj1 := hom< Parent(poly) -> R1 | [x, 1]>;
  res_poly := 0;
  // print Parent(poly);
  for j := 0 to y_degree do
    res_poly +:= y^j*proj1(Coefficient(poly, old_y, j));
  end for;
  return res_poly;
end function;

function change_poly_for_finite_field_function_field(poly)
  base_field := BaseRing(Parent(poly));
  old_y := Parent(poly).2;
  y_degree := Degree(poly, old_y);
  R1<x> := PolynomialRing(base_field);
  R<y> := PolynomialRing(R1);
  proj1 := hom< Parent(poly) -> R1 | [x, 1]>;
  res_poly := 0;
  // print Parent(poly);
  for j := 0 to y_degree do
    res_poly +:= y^j*proj1(Coefficient(poly, old_y, j));
  end for;
  return res_poly;
end function;

function make_homogeneous(poly)
  base_field := BaseRing(Parent(poly));
  R<x,y,z> := PolynomialRing(base_field, 3);
  d := Degree(poly);
  H := hom< Parent(poly) -> R | [x,y]>;
  poly := H(poly);
  hom_pol := 0;
  for k := 0 to d do
    hom_pol +:= HomogeneousComponent(poly, k)*z^(d-k);
  end for;
  return hom_pol;
end function;

    





function good_model(Q,p : N:=0, exactcoho:=false, W0:=0, Winf:=0)
  g:=genus(Q,p);
  r,Delta,s:=auxpolys(Q);

  if W0 eq 0 then
    // print "Computing basis matrix W_0";
    t := Cputime(); 
    W0:=mat_W0(Q);
    // print "Done computing, took ", Cputime(t), "seconds";
  end if;
  if Winf eq 0 then
    // print "Computing basis matrix W_inf";
    t := Cputime(); 
    Winf:=mat_Winf(Q);
    // print "Done computing, took ", Cputime(t), "seconds";
  end if;
  // print "Computing inverses of the matrices";
  t := Cputime(); 
  W0inv:=W0^(-1); 
  Winfinv:=Winf^(-1); 
  // print "Done computing, took ", Cputime(t), "seconds";

  if (Degree(r) lt 1) or (not smooth(r,p)) or (not (is_integral(W0,p) and is_integral(W0inv,p) and is_integral(Winf,p) and is_integral(Winfinv,p))) then
    // print "Bad model!";
    return false;
  end if;

  return true;
end function;


  

// R<x,y> := PolynomialRing(GF(7),2);
// f := 2*x^6 + 2*x^5*y + 6*x^5 + 4*x^4*y^2 + 4*x^4*y + 3*x^4 + 5*x^3*y^3 + 4*x^3*y^2 + 5*x^3*y + 2*x^3 + 6*x^2*y^4 + 5*x^2*y^2 + 2*x^2*y + 6*x^2 + 6*x*y^4 + 3*x + 5*y^6 + y^5 + y^4 + 5*y^3 + y^2 + 4*y+5;
// //make f monic in y
// // f := 3*f;
// // f := x+x^3+y^2;
// a := GF(7^3).1^266;
// b := a;
// c := 1;

// // a,b,c,L := lift_node(a,b,c,GF(7^3));
// // lifted_curve_node_solns(f, a,b,c,L, 7);
// nodes_orbit_list := [[*[a,b,c], GF(7^3)*]];

function test_random_genus_g_example(g, p)
  C := RandomCurveByGenus(g, GF(p));
  F := DefiningPolynomial(C);
  R<u,v> := PolynomialRing(GF(p),2);
  f := Evaluate(F, [u,v,1]);
  g, orbs := make_monic_and_find_node_orbits(f);
  //check if g defines nodal curve
  P<x,y,z> := ProjectiveSpace(GF(p), 2);
  G := make_homogeneous(g);
  bool := IsNodalCurve(Curve(P, G));
  print "Nodal curve:", bool;
  if bool eq false then
    return "exited because curve isn't nodal";
  end if;
  _,_,_,h := lift_curve_and_nodes(g, orbs, p);
  if h cmpeq -1 then
    return false, "couldn't lift";
  end if;
  Q := change_poly_for_rational_function_field(h);
  G := change_poly_for_finite_field_function_field(g);
  L_1 := FunctionField(Q);
  L_2 := FunctionField(G);
  print "Genus of lift", Genus(L_1);
  print "Genus of original", Genus(L_2);
  bool := good_model(Q,p);
  return bool, C;
end function;

// primes := PrimesInInterval(10, 50);
// gen := 6;
// curve_primes := [* *];
// curve_polynomials_mine := [* *];
// curve_polynomials_good_model := [* *];
// for p in primes do
//   R<u,v> := PolynomialRing(GF(p),2);
//   //100 trials
//   //exit early if we hit 10 curves for this prime
//   curves_found_curr_prime := 0;
//   for i := 0 to 100 do
//     C := RandomCurveByGenus(gen, GF(p));
//     F := DefiningPolynomial(C);
//     f := Evaluate(F, [u,v,1]);
//     g, orbs := make_monic_and_find_node_orbits(f);
//     P<x,y,z> := ProjectiveSpace(GF(p), 2);
//     G := make_homogeneous(g);
//     bool := IsNodalCurve(Curve(P, G));
//     print "Nodal curve:", bool;
//     if bool then
//       _,_,_,h := lift_curve_and_nodes(g, orbs, p);
//       if h cmpeq -1 then
//         print "Couldn't lift";
//       else 
//         Q := change_poly_for_rational_function_field(h);
//         bool := good_model(Q,p);
//         if bool then
//           curves_found_curr_prime +:= 1;
//           Append(~curve_primes, p);
//           Append(~curve_polynomials_mine, f);
//           Append(~curve_polynomials_good_model, Q);
//           if curves_found_curr_prime eq 10 then
//             break;
//           end if;
//         end if;
//       end if;
//     end if;
//   end for;
// end for;
// Write("examples_good_model_genus_6.m", "genus := ");
// Write("examples_good_model_genus_6.m", gen);
// Write("examples_good_model_genus_6.m", ";");
// Write("examples_good_model_genus_6.m", "curve_primes cat:= ");
// Write("examples_good_model_genus_6.m", curve_primes);
// Write("examples_good_model_genus_6.m", ";");
// Write("examples_good_model_genus_6.m", "curve_polynomials_mine cat:= ");
// Write("examples_good_model_genus_6.m", curve_polynomials_mine);
// Write("examples_good_model_genus_6.m", ";");
// Write("examples_good_model_genus_6.m", "curve_polynomials_good_model cat:= ");
// Write("examples_good_model_genus_6.m", curve_polynomials_good_model);
// Write("examples_good_model_genus_6.m", ";");

function generate_curves_examples(g, p_min, p_max, num_examples, num_trials, create_file)
  file_str := "examples_good_model_genus_" cat IntegerToString(g) cat ".m";
  primes := PrimesInInterval(p_min, p_max);
  gen := g;
  curve_primes := [* *];
  curve_polynomials_mine := [* *];
  curve_polynomials_good_model := [* *];
  for p in primes do
    R<u,v> := PolynomialRing(GF(p),2);
    curves_found_curr_prime := 0;
    for i := 0 to num_trials do
      C := RandomCurveByGenus(gen, GF(p));
      F := DefiningPolynomial(C);
      f := Evaluate(F, [u,v,1]);
      g, orbs := make_monic_and_find_node_orbits(f);
      P<x,y,z> := ProjectiveSpace(GF(p), 2);
      G := make_homogeneous(g);
      bool := IsNodalCurve(Curve(P, G));
      print "Nodal curve:", bool;
      if bool then
        _,_,_,h := lift_curve_and_nodes(g, orbs, p);
        if h cmpeq -1 then
          print "Couldn't lift";
        else 
          Q := change_poly_for_rational_function_field(h);
          bool := good_model(Q,p);
          if bool then
            curves_found_curr_prime +:= 1;
            Append(~curve_primes, p);
            Append(~curve_polynomials_mine, f);
            Append(~curve_polynomials_good_model, Q);
            if curves_found_curr_prime eq num_examples then
              break;
            end if;
          end if;
        end if;
      end if;
    end for;
  end for;
  if create_file eq true then
    //create the lists in the file
    Write(file_str, "genus := ");
    Write(file_str, gen);
    Write(file_str, ";");
    Write(file_str, "curve_primes:= ");
    Write(file_str, curve_primes);
    Write(file_str, ";");
    Write(file_str, "curve_polynomials_mine:= ");
    Write(file_str, curve_polynomials_mine);
    Write(file_str, ";");
    Write(file_str, "curve_polynomials_good_model:= ");
    Write(file_str, curve_polynomials_good_model);
    Write(file_str, ";");
  else 
    //concatenate the lists in the file
    Write(file_str, "curve_primes cat:= ");
    Write(file_str, curve_primes);
    Write(file_str, ";");
    Write(file_str, "curve_polynomials_mine cat:= ");
    Write(file_str, curve_polynomials_mine);
    Write(file_str, ";");
    Write(file_str, "curve_polynomials_good_model cat:= ");
    Write(file_str, curve_polynomials_good_model);
    Write(file_str, ";");
  end if;
  return 0;
end function;


procedure lifting_curves_trials(gen, p, num_trials)
  R<u,v> := PolynomialRing(GF(p),2);
  num_successes := 0;
  // gen_time := 0;
  // lift_time := 0;
  // check_time := 0;
  for i := 1 to num_trials do
    // if i in [Ceiling(0.1*j*num_trials) : j in [1..10]] then
    //   print "On trial", i;
    //   print "gen_time so far", gen_time;
    //   print "lift_time so far", lift_time;
    //   print "check_time so far", check_time;
    // end if;
    // trial_time := Cputime();
    // print "trial_time", trial_time, "before generating";
    // t := Cputime();
    C := RandomCurveByGenus(gen, GF(p));
    // t_1 := Cputime(t);
    // print "trial_time", trial_time, "after generating";
    // gen_time +:= t_1;
    F := DefiningPolynomial(C);
    f := Evaluate(F, [u,v,1]);
    g, orbs := make_monic_and_find_node_orbits(f);
    P<x,y,z> := ProjectiveSpace(GF(p), 2);
    G := make_homogeneous(g);
    bool := IsNodalCurve(Curve(P, G));
    if bool eq false then
      continue;
    end if;
    // print "trial_time", trial_time, "before lifting";
    // t := Cputime();
    _,_,_,h := lift_curve_and_nodes(g, orbs, p);
    // t_1 := Cputime(t);
    // print "trial_time", trial_time, "after lifting";
    // lift_time +:= t_1;
    if h cmpeq -1 then
      continue;
    end if;
    Q := change_poly_for_rational_function_field(h);
    // t := Cputime();
    // print "trial_time", trial_time, "before checking lift";
    bool := good_model(Q,p);
    // print "trial_time", trial_time, "after checking lift";
    // t_1 := Cputime(t);
    // check_time +:= t_1;
    if bool then
      num_successes +:= 1;
    end if;
  end for;
  print gen, ",", p, ",", num_trials, ",", num_successes, "\n";
end procedure;

procedure lifting_curves_trials_prime_interval(gen, p_min, p_max, num_trials)
  primes := PrimesInInterval(p_min, p_max);
  print "START OUTPUT";
  for p in primes do
    print "On prime", p;
    lifting_curves_trials(gen, p, num_trials);
  end for;
  print "END OUTPUT";
end procedure;



// t := Cputime();
// lifting_curves_trials(4, 31, 2663);
// t_1 := Cputime(t);
// print t_1;







  










  


