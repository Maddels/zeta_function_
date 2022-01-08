import "count_plane_model.m": ConvexHullMonomials;
import "lifting_nodes.m": make_monic_and_find_node_orbits, make_homogeneous, lift_curve_and_nodes, change_poly_for_rational_function_field, good_model;
import "castryck_lifting_code.m": lift_gonality_3, lift_gonality_4, lift_gonality_5;

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

function birational_transform(F)
  x := Parent(F).1;
  y := Parent(F).2;
  a_n := LeadingCoefficient(F, y);
  if a_n eq 1 then
    return F;
  end if;
  y_degree := Degree(F, y);
  coefficients_x := Coefficients(F, y);
  new_F := y^y_degree;
  new_F +:= &+[coefficients_x[i+1]*a_n^(i-1)*y^(y_degree-i) : i in [1..(y_degree)] ];
  return new_F;
end function;
  
function naive_lift(F)
  R<x,y> := PolynomialRing(RationalField(), 2);
  monomials := Monomials(F); 
  coefficients := Coefficients(F);
  new_F := &+[Integers()!(coefficients[i]) * Evaluate(ChangeRing(monomials[i], Integers()), [x,y]) : i in [1..#monomials]];
  return new_F;
end function;

function lattice_width_transformation(F, v)
  if v cmpeq -1 then
    N := ConvexHullMonomials(F);
    _, u := Width(N);
    v := Representative(u);
  end if;
  x := Parent(F).1;
  y := Parent(F).2;
  phi := ChangeBasis(v);
  monomials := Monomials(F);
  coefficients := Coefficients(F);
  new_monomials := [];
  for monomial in monomials do
    i := Degree(monomial, 1);
    j := Degree(monomial, 2);
    new_degrees := phi([i,j]);
    // print new_degrees;
    Append(~new_monomials, [new_degrees.1, new_degrees.2]);
  end for;
  // print new_monomials;
  min_i := Minimum([new_monomials[i][1] : i in [1..#new_monomials]]);
  min_j := Minimum([new_monomials[i][2] : i in [1..#new_monomials]]);
  // print min_i, min_j;
  new_F := 0;
  for i := 1 to #new_monomials do
    new_monomials[i][1] -:= min_i;
    new_monomials[i][2] -:= min_j;
    new_F +:= coefficients[i] * x^(new_monomials[i][1]) * y^(new_monomials[i][2]);
  end for;
  // print new_monomials;
  return new_F;
end function;


//assume F defined over F_p[x,y]
function lift_curve(F, p)
  t := Cputime();
  Q := change_poly_for_finite_field_function_field(F);
  // print "Q is", Q;
  L := FunctionField(Q);
  genus := Genus(L);
  // print genus;
  N := ConvexHullMonomials(F);
  if NumberOfInteriorPoints(N) eq genus then
    vprint Kyng, 2: "Baker's bound met, naively lifting";
    //naive lift works
    new_F := naive_lift(F);
    new_F := birational_transform(new_F);
    new_F := change_poly_for_rational_function_field(new_F);
    t_1 := Cputime(t);
    return new_F, t_1;
  end if;
  if genus le 5 then
    vprint Kyng, 2: "Genus doesn't exceed 5, using CV18";
    A<x,y> := AffineSpace(GF(p),2);
    C := Curve(A,F);
    try
      new_F := GonalityPreservingLift(C);
      t_1 := Cputime(t);
      return new_F, t_1;
    catch e 
      print "Lift failed, trying next";
      vprint Kyng, 2: "Gonality Preserving Lift failed";
    end try;
  end if;
  lattice_width, u := Width(N);
  u := SetToIndexedSet(u);
  // vprint Kyng, 2: "Lattice width is", lattice_width;
  if lattice_width le 4 then
    vprint Kyng, 2: "Lattice width doesn't exceed 4, using CV20";
    if Degree(Q) ne lattice_width then
      new_F := lattice_width_transformation(F, u[1]);
      new_F := change_poly_for_finite_field_function_field(new_F);
    else 
      new_F := Q;
    end if;
    //add code to check if curve is simply branched. amounts to computing R = Res_y(F, F_y) (where F = new_F)
    //and finding ramification points on the smooth curve over \bar{k} (i.e. just do over a large enough extension, where residual degree must be 1). 
    //(e.g. over extentsion of degree deg(R)*deg_y(F))
    if lattice_width eq 3 then 
      try
        new_F := lift_gonality_3(new_F);
        t_1 := Cputime(t);
        return new_F, t_1;
      catch e
        vprint Kyng, 2: "Low-gonal 3-lifting failed";
        print "Lift failed, trying next";
      end try;
    end if;
    if lattice_width eq 4 then
      try
        new_F := lift_gonality_4(new_F);
        t_1 := Cputime(t);
        return new_F, t_1;
      catch e
        vprint Kyng, 2: "Low-gonal 4-lifting failed";
        print "Lift failed, trying next";
      end try;
    end if;
  end if;
  if lattice_width eq 5 then
    for i := 1 to #u do
      new_F := lattice_width_transformation(F, u[i]);
      new_F := change_poly_for_finite_field_function_field(new_F);
      try
        new_F := lift_gonality_5(new_F);
        t_1 := Cputime(t);
        return new_F, t_1;
      catch e
        vprint Kyng, 2: "Low-gonal 5-lifting failed";
        print "Lift failed, trying next";
      end try;
    end for;
  end if;
  g, orbs := make_monic_and_find_node_orbits(F);
  P<x,y,z> := ProjectiveSpace(GF(p), 2);
  G := make_homogeneous(g);
  bool := IsNodalCurve(Curve(P, G));
  if bool then
    _,_,_,new_F:= lift_curve_and_nodes(g, orbs, p);
    if new_F cmpeq -1 then
      print "Couldn't lift";
    else 
      new_F := change_poly_for_rational_function_field(new_F);
      t_1 := Cputime(t);
      return new_F, t_1;
    end if;
  end if;
  return 0, 0;
end function;






