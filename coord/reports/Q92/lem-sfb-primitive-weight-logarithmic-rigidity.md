## Worker report

Item: lem-sfb-primitive-weight-logarithmic-rigidity. The node statement, dependencies,
proof, status, source and other metadata are unchanged; only `lean` is supplied.
The module is `Sheaf.AlgebraicGeometry.PrimitiveWeightLogarithmicRigidity`.
Its main theorem is
`AlgebraicGeometry.PrimitiveWeightRigidity.eq_of_rightLogarithmicDerivative_eq`.
It has the required `sorry` proof. The five supporting definitions contain explicit
constructions and no postponed proofs or choices. No new nodes or dependency modules
are needed: they are the coordinate maps and derivative expressions introduced by
this item's own statement, listed in `lean.declarations` under its blueprint tag.

Clause-by-clause statement reading:

- A nonzero commutative ring is `{A : Type u} [CommRing A] [Nontrivial A]`.
  No field, characteristic, reducedness, Noetherian or torsion hypothesis appears.
- A finite-rank free abelian group is `{M : Type u} [AddCommGroup M]`
  with `[Module.Free ℤ M] [Module.Finite ℤ M]`, using its canonical integer module.
- The torus is precisely the dependency's `ringDiagonalizableGroup A M`.
  The same universe as A is its recorded interface. Every finite-rank lattice and
  finite index set can be represented in this common universe; no cardinality of
  rank or of the finite index set is bounded.
- Rational independence of `r s : M` is rendered by `h_independent`:
  every integer relation `a • r + b • s = 0` has `a = 0 ∧ b = 0`.
  This is equivalent to independence in `ℚ ⊗[ℤ] M`: clear rational denominators,
  and use torsion-freeness of the free group for the injectivity of rationalization.
  It asserts independence, not merely distinctness or nonzero weights.
- The finite set J is `[Fintype J]`. The specified enumeration is the explicit
  bijection `e : Fin (Fintype.card J) ≃ J`, not a commutative product or a choice
  hidden in an existential assumption. Every ordering is permitted.
- Nonnegative integers are `i k : J → ℕ`; gcd one is `h_primitive : ∀ j,
  Nat.Coprime (i j) (k j)`. The weights are literally `i j • r + k j • s`,
  and `h_distinct` is injectivity of that function of j.
- A group scheme is `H : Grp (Over (Spec (.of A)))`. Its group diagrams are part
  of `Grp`; the base morphism is `H.X.hom`. Smoothness is `[Smooth H.X.hom]`,
  and affineness is `[IsAffineHom H.X.hom]` from the recorded Mathlib modules.
- The specified torus action is `a : ModObj (ringDiagonalizableGroup A M).X H.X`.
  This supplies the unit and action-associativity diagrams. `h_aut` requires
  preservation of group multiplication on every algebra-valued point. Each action
  map is already invertible, by the inverse torus point, so it is an automorphism;
  multiplication preservation also forces preservation of identity and inverse.
  There is no embedding T into H and no interpretation as internal conjugation.
- Each `p j` is an A-scheme morphism from `Spec (Polynomial A)` to H.
  `h_closed` uses `IsClosedImmersion (p j).left`. `h_add` says
  `p_j(z+z') = p_j(z) * p_j(z')` for every commutative A-algebra R and all its z,z'.
  This is precisely being a homomorphism from the additive group scheme: R=A[z,z']
  tests its multiplication diagram; z=z'=0 gives the identity, and z'=-z gives
  inverses. The field-only `StandardGroupSchemes.additive` is deliberately not
  used over arbitrary A. No replacement group structure is supplied or assumed.
- `linePoint` is Spec of `Polynomial.aeval z`, via the existing `algSpec` functor.
  Thus its input z really is the additive-line coordinate, with coefficients fixed.
- `orderedProduct p e` multiplies the morphisms
  `linePoint (MvPolynomial.X (e q)) ≫ p (e q)` using `List.ofFn` and `List.prod`
  in the group of morphisms into H. Its domain is literally `Spec A[z_j : j∈J]`.
  `h_chart : IsIso (orderedProduct p e).left` says this actual multiplication map
  is a scheme isomorphism. There is no arbitrary chart or bijection substituted.
- `characterValue t m` pulls the basis monomial `AddMonoidAlgebra.single m 1`
  through `(Spec.preimage t.left).hom`. It is exactly the monomial character
  associated to m, including for algebras with nilpotents. `h_weight` is the
  specified action equation `t ⋅ p_j(z) = p_j(w_j(t)*z)` for every R, t and z.
- `F₀ F₁` are A-scheme morphisms with domain `Spec (MvPolynomial (Fin 2) A)`.
  `planePoint z` is Spec of `MvPolynomial.aeval z`. Indices 0 and 1 are x and y.
  `h_origin₀`, `h_origin₁` require evaluation at `(0,0)` to be the identity point.
- `h_equiv₀`, `h_equiv₁` assert equivariance for all R, all R-valued t and all
  coordinate pairs z, with the actual characters r and s multiplying z(0), z(1).
  These tests include the universal point over the coordinate algebra of
  T × A², so this is scheme-theoretic equivariance, not only equivariance on
  A-valued or geometric points. All test rings have the ambient universe u,
  which contains the coordinate algebras of the affine schemes in the statement.
- `rightLogarithmicDerivative F d` is the group product
  `F(X+epsilon e_d) * F(X)⁻¹`, in H over `DualNumber (MvPolynomial (Fin 2) A)`.
  The coefficient inclusion is `TrivSqZeroExt.inl`, and epsilon is
  `DualNumber.eps`. This is the right derivative, with the order in the node,
  rather than `F(X)⁻¹ * F(X+epsilon e_d)`. Reduction to B sends it to 1;
  viewing it in the ambient H-point group retains exactly equality in that
  kernel because a kernel subgroup's inclusion is injective. The node's tangent
  operations use coefficient pairs: Mathlib's `DualNumber B` is exactly
  `TrivSqZeroExt B B` with multiplication `(b,c)(d,e)=(bd,be+cd)` and epsilon²=0.
  The assertion uses only equality of tangent points; no additional tangent
  vector-space structure or choice of coordinates on Lie(H) is required.
- `h_dx` and `h_dy` are respectively equality of this derivative at 0 and at 1.
  The conclusion `F₀ = F₁` is equality in the category of A-schemes, equivalently
  equality of their underlying scheme morphisms. It is not equality only on points.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup` and its full source, including
  `ringDiagonalizableGroupMap`. The former is Hopf Spec of `AddMonoidAlgebra A M`;
  its basis is the one used by `characterValue`. No dependency repair is needed.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`,
  already publicly reachable through the diagonalizable-group import.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`, including its full
  signature, coefficient rule and variable rule. These are publicly reachable
  through `Mathlib.Algebra.MvPolynomial.PDeriv`, also imported for the recorded
  partial-derivative dependency `MvPolynomial.pderiv` and its monomial formula.
- Proof-only import `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`. Its full adjunction
  signature and docstring were read; its hom equivalence is the node's proof input.
- Additional existing APIs, read in source: `algSpec` and its map and structure
  map formulas; cartesian `Hom.group`, `Hom.mul_def`, `Hom.inv_def`; `ModObj`,
  its action on hom types, and `DualNumber`, `DualNumber.eps`, `eps_pow_two`.
  The withdrawn CompactObject example and its updated upstream Lean binding were
  both read; this module follows the current module/public-section convention.

Edge cases checked before writing and again against the finished signature:

- Empty J is allowed. `List.ofFn` is empty and its product is the identity map;
  h_chart identifies H with Spec A. There is no nonemptiness binder on J.
- Primitive axial bidegrees (1,0) and (0,1) are allowed. (0,0) is excluded by
  coprimality. If one derivative vanishes automatically, the other kills C_j.
- Positive characteristics 2 and 3 are allowed, including the (2,1) weight in
  characteristic 2. The other partial derivative detects the coefficient.
- Torsion and nilpotents, e.g. A=ℤ/6 and a square-zero coefficient extension,
  do not affect integer Bezout or group-algebra basis comparison.
- Nonprimitive (p,0) over characteristic p would be a counterexample without
  h_primitive, so that hypothesis is present in precisely its necessary form.
- Arbitrary fixed orders and noncommutative H are retained by the list product.
  The derivative uses exact group cancellation, not a commutative approximation.
- Free lattices of rank below two have no independent r,s, as the node requires.
  Zero A is excluded by Nontrivial, as in the node; no further base restriction.

Searches for an existing statement (all negative for this exact assertion):

- msearch.py leanfinder, query: "Equivariant maps into a group scheme with primitive
  torus weights are determined by their logarithmic derivatives over any commutative ring".
  Eight hits: mostly RootPairing weightHom injectivity and affine-space hom_ext.
  None states logarithmic rigidity of group-valued maps.
- msearch.py leansearch, query: "Polynomial maps with vanishing partial derivatives
  and primitive weights are equal". Eight hits: derivation extensionality,
  pderiv_map, weighted homogeneous differentiation, and unrelated primitive
  polynomial results. These are ingredients, not this theorem.
- msearch.py loogle, initial query `MvPolynomial.pderiv, Grp, DualNumber` returned
  zero hits and "unknown identifier Grp". Follow-up query `MvPolynomial.pderiv`
  succeeded with twelve partial derivative declarations and formulas, none exact.
- msearch.py grep, query `logarithmic.*deriv|pderiv.*eq_zero`, returned 25 hits:
  analytic logarithmic derivatives, differential fields, and polynomial pderiv
  formulas. Those analytic/field statements do not cover arbitrary base rings.
- rg in lean/WeilConjectures and lean/Sheaf for logarithmic, primitive-weight,
  ringDiagonalizableGroup, additiveGroupScheme and vectorGroup; and the prescribed
  grep for the item's blueprint id in lean/WeilConjectures. No existing statement.
  The relevant positive discovery is the recorded RingDiagonalizableGroup module.
  StandardGroupSchemes.additive has a Field binder and therefore is not an
  arbitrary-ring additive group. We use literal polynomial spectra and their
  all-algebra additive homomorphism law, without defining another group scheme.
- Read Mathlib group-affine, cartesian Grp/Mon/Mod, MvPolynomial Basic/Eval/PDeriv,
  and dual-number sources. No canonical-map duplication was introduced: the
  helpers apply the existing evaluation and Spec APIs to the maps in this node.
- rg for the final theorem and helper namespace against project/upstream names
  found no conflicting declaration.

Source check: opened Conrad's current online PDF, the coefficient argument on printed
p.146, Proposition 5.1.16 on printed pp.147--148, and Section 6.2 Step 3 on printed p.207.
The docstring explicitly identifies this as the DAG's agent auxiliary lemma, not a
claimed theorem of Conrad. All six recorded proof steps are retained in its docstring.
No source-based correction or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled both the sandbox module and its library module name
cleanly (16.7 s and 8.0 s reported). No error or warning. All delivered Lean compilation
uses that wrapper; no library source, git state, launcher script or artifact was edited.

## Second reading by Q92

The dispatcher explicitly prohibited starting other agents; no independent worker was
started and no independent reading is claimed here. The maintainer supplies the
independent review of this delivery. This section records the worker's separate final
self-audit with the node and finished file open, to make that review concrete.

Checked the signatures again against every clause above. The derivative multiplies the
shifted value on the left of the inverse unshifted value; d=0 and d=1 are both required.
The monomial character is pulled from the recorded torus's actual coordinate ring.
The action is ModObj plus preservation of multiplication, which gives automorphisms,
without an embedding into H. Additivity of p is tested on all algebras; the universal
polynomial pair tests its scheme multiplication law. The product hypothesis is IsIso
of the explicitly ordered map, so its coordinates cannot be an unrelated chart.
The equivariance tests include universal coordinate algebras and do not lose finite
fields, torsion or nilpotents. Coprimality is natural-number gcd one, including axial
weights and excluding (0,0). Integer independence is exactly rational independence
for the stated free lattice. No nonempty J or characteristic-zero binder is present.
All helpers have source/blueprint docstrings and actual data; the only postponed
proof is the main theorem, and the record lists every declaration. No mismatch found.
