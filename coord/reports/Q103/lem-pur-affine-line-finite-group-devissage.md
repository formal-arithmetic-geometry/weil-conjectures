## Worker report

The module `Sheaf.AlgebraicGeometry.AffineLineFiniteGroupDevissage` states
`AlgebraicGeometry.AffineSpace.affineLine_finiteGroup_devissage`. Its entire proof is
`sorry`. There are no additional postponed assertions. The two helper definitions have
real data: they compose the existing constant-sheaf functor, degree-zero single functor,
bounded-below right derived sections, derived adjunction unit and exact-single comparison.
They belong to this node's specified canonical constants map; no independent notion or
new DAG node is introduced. No statement or dependency correction was needed.

Hypotheses and clauses, individually:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Prime invertible in k: `(ell : ℕ) (hell : Nat.Prime ell)` and
  `(hinv : IsUnit (ell : k))`.
- Finite abelian coefficient group: `(B : AddCommGrpCat.{u + 1}) [Finite B]`.
- Killed by a positive power: `(a : ℕ) (ha : 1 ≤ a)` and
  `(hB : ∀ b : B, (ell ^ a) • b = 0)`.
- The geometric affine line C is exactly
  `AffineSpace (ULift.{u} (Fin 1)) (Spec (.of k))`, using the recorded coordinate-type
  convention of def-sbc-affine-space.
- B_C is `(constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B`, the
  recorded abelian sheafification of the constant presheaf on the small etale site.
- Ordinary RΓ of B_C in degree zero is `C.abelianConstantsDerivedSections.obj B`.
  This is explicitly constantSheaf, then `DerivedCategory.Plus.singleFunctor _ 0`,
  then `(Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus`.
  Thus both objects and the comparison live in D^+(Ab), not in compact support cohomology.
- The first conjunct is `IsIso (C.abelianDerivedConstants.app B)`. The helper is the
  unit of `(constantSheafΓAdj ...).derivedPlus`, precomposed with the single functor
  and followed by the existing `mapDerivedCategoryPlusSingleFunctor 0` comparison
  under RΓ. It is the actual constants map, not an arbitrary morphism or an existence
  assertion for an isomorphism. `derivedPlus_unit_app_fac` in the imported adjunction
  module characterizes it by the ordinary constants unit followed by the injective
  resolution augmentation.
- The second conjunct is `IsIso ((constantSheafΓAdj ...).unit.app B)`.
  Its target is Γ(C,B_C), canonically H^0(C,B_C). The recorded cohomology convention
  identifies these using the zeroth right-derived-functor comparison; on the terminal
  etale object, `Sheaf.ΓNatIsoSheafSections` identifies Γ with actual sections.
- Every nonzero integer degree, including negative degrees, is covered by
  `∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.Plus.homologyFunctor ... q).obj
    (C.abelianConstantsDerivedSections.obj B))`. This uses the homology of ordinary
  bounded-below derived sections, so the negative-degree convention is built in.
- Naturality is the fourth conjunct: for every finite B', every positive exponent a'
  killing B', and every group homomorphism `f : B ⟶ B'`, the map `f[0]` followed by
  constants for B' equals constants for B followed by the induced RΓ map. The two
  sides use the same explicitly defined natural transformation and target functor.
  In particular it also induces the degree-zero naturality square. The exponents
  a and a' need not agree and f need not be linear over an arbitrarily selected ring.
- The final conjunct is `∃ b : ℕ, Nat.card B = ell ^ b`, including b = 0.
- No module structure or freeness over Z/ell^a is assumed anywhere.

Statement dependencies, with their actual declarations read in source:

- def-weil-pbc-constant-sheaf: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf` (sheafification of constant presheaves).
- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, on `Scheme.Etale`.
- def-sbc-affine-space is a Mathlib leaf, not a missing Lean record:
  `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace`, with
  coordinate type `ULift.{u} (Fin 1)` exactly as its match specifies.
- def-weil-pbc-sites-and-cohomology: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`. Its record explicitly retains
  existing abelian sheaves and derived cohomology for the remaining components.
  The small etale topology is used directly rather than constructing another site.
- def-weil-pbc-derived-categories:
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`. Its mixed record names
  Mathlib `DerivedCategory`, `DerivedCategory.Plus`, and `DerivedCategory.homologyFunctor`;
  the abelian-group case uses `Sheaf ... AddCommGrpCat.{u + 1}`. We use those categories
  and `DerivedCategory.Plus.homologyFunctor`, with the library's existing instances.

The additional construction APIs are in
`WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections` (additivity),
`Mathlib.CategoryTheory.Sites.GlobalSections` (`Sheaf.Γ`, `constantSheafΓAdj`),
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
(`CategoryTheory.Adjunction.derivedPlus`), and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
(`CategoryTheory.Functor.mapDerivedCategoryPlusSingleFunctor`). These are used directly.
Recorded stated proof dependencies are imported without `public`: primitive roots,
root trivialization, Kummer root-line computation, abstract derived category,
long exact sequence, model-category lifting, homotopy uniqueness/invariance, and exact
sheafification. The theorem docstring carries all seven accepted proof steps.

Edge cases checked before writing: B = 0 has order 1 = ell^0 and zero sections in every
degree; B = Z/ell and Z/ell^2 are allowed; (Z/ell)^2 killed by ell^2 is allowed without
freeness over Z/ell^2; a = 1 is allowed; ell = 2 is allowed when invertible in k.
The prime-characteristic-equals-ell case is precisely excluded by hinv, while characteristic
zero and every other characteristic remain covered. Negative q and arbitrary large
positive q occur in the same integer-degree quantifier. Naturality covers the zero map,
the identity, and maps between groups requiring different exponents. The site has object
universe u+1 and morphism universe u, and coefficients follow the recorded u+1 convention;
no equality of those site universes has been imposed. The affine line over a field is
nonempty; no empty-scheme assumption is introduced.

Searches actually run (msearch.py with group Q103 and this item):

- LeanFinder: `Derived etale global sections of the affine line over an algebraically
  closed field with finite primary constant abelian coefficients equal the coefficients
  in degree zero` returned eight unrelated algebraic-etaleness / affine-coordinate hits,
  including `AlgebraicGeometry.AffineSpace.coord`; no matching theorem.
- Loogle: `"Sheaf", "cohomology"` returned seven generic sheaf cohomology and
  nonabelian H1 declarations, not this statement.
- Mathlib grep: `affine.*line.*cohom|constantSheaf.*line|line.*constantSheaf` returned
  zero hits.
- LeanSearch: `The canonical constants map from a finite primary abelian group to
  derived etale sections of the affine line is an isomorphism` returned eight unrelated
  results about double duality, free abelian groups, sectionwise isomorphisms, condensed
  constants, profinite limits and abelianization; no match.
- The same affine-line grep in `lean/WeilConjectures` and `lean/Sheaf` located
  `AlgebraicGeometry.AffineSpace.subsingleton_sheafH_constantSheaf_line` in
  `WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer`. I read its full signature:
  it supplies positive-degree vanishing for finite groups killed by an invertible integer,
  but not the full specified derived map, naturality and order assertion. It therefore
  does not qualify as an existing declaration for the whole item. Broader derived-constant
  searches located the generic derived adjunction used above, along with ordinary affine
  line invariance and cyclic-to-torsion devissage, neither identical to this item.
- A direct search for this node id in `lean/WeilConjectures` found no attachment.
  Searches for the three proposed names in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json` found no pre-existing declarations.

Source check: read the current `literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-prop-a1-kummer/_section.md` and its full proof, especially
Coefficients, Clause (c), and Degrees 0 and 1. The node's retained seven-step finite-primary
cardinality induction is the refinement being stated. There is no statement dispute.

Validation: scompile.py compiled this module in sandbox and named-library modes with no
errors or warnings (11.9 s and 8.3 s respectively). The initial compiler run caught only
three line-break/projection parsing errors, which were repaired before this clean run.

## Second reading by Q103

This is a second pass by the same dispatcher worker; the brief prohibits starting other
agents, and the maintainer performs the independent review after delivery. I reopened the
node and the final module and matched all clauses above. The first conjunct has the
correct direction B[0] -> RΓ(C,B_C), and its target is the single constant sheaf, not an
arbitrary complex. The comparison is transported by the canonical exact-single isomorphism
with its hom in the forward direction. The ordinary constants unit is used for H^0,
integer q covers the entire nonzero-degree clause, and the naturality square has f[0]
on its left and the induced constant-sheaf RΓ map on its right. The quantified target group
is finite and killed by an independently positive ell-power. Nat.card gives the full order,
including the trivial group. There is no added module-freeness hypothesis or statement
correction. The two helper definitions are real compositions and the only theorem has
exactly `by sorry`. No mathematical mismatch was found in this second pass.
