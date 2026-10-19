## Worker report

The module `Sheaf.Paper.FiniteAffineDirectImageSupportBound` states
`AlgebraicGeometry.Etale.supportCondition_rightDerivedLowerStarPlus_of_isAffine`.
Its sole proof is `sorry`. There are no new definitions, helper theorems, new nodes,
or changes to the mathematical statement. The docstring includes all ten steps of
the node's proof and names the inputs at each step.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`.
- A finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the recorded six-functor module-sheaf universe convention, allowing any
  finite ring by universe lifting; it does not impose nontriviality on Λ.
- Its additive exponent is invertible in k:
  `hΛ : IsUnit (AddMonoid.exponent Λ : k)`. This uses the literal additive group
  exponent, not an extra chosen annihilator or an assumption on an unrelated ring.
- X and Y are k-schemes: `X Y : Scheme.{u}` with `X.Over (Spec (.of k))` and
  `Y.Over (Spec (.of k))`.
- Both structure morphisms are finite type: `LocallyOfFiniteType` and `QuasiCompact`
  on each of `X ↘ Spec (.of k)` and `Y ↘ Spec (.of k))`.
- Both schemes are separated over k: `IsSeparated` on each structure morphism.
- f is a k-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`. The source and the
  stage-1 review explicitly read “between k-schemes” as a k-morphism.
- f is affine and finite type: `[IsAffineHom f] [LocallyOfFiniteType f]
  [QuasiCompact f]`. Quasi compactness is already a consequence of affineness,
  but is spelled out so the finite-type phrase is rendered in full.
- Ordinary module derived categories on the small etale sites, and L bounded below:
  `L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  `L.obj` is its underlying object of the ordinary derived category.
- Every ordinary cohomology sheaf is constructible: `hconstructible` quantifies
  over every `r : ℤ` and applies `Scheme.IsConstructibleEtaleModuleSheaf` to
  `(DerivedCategory.homologyFunctor _ r).obj L.obj`. No boundedness above or finite
  Tor-amplitude is assumed for L.
- The support hypothesis is `DerivedCategory.SupportCondition L.obj`. The
  existing upstream definition quantifies over `i : ℤ`, takes the CLOSED support
  `Etale.sheafSupport` of H^{-i}, and, if nonempty, requires `0 ≤ i` and its
  topological Krull dimension at most `i.toNat`. This is exactly the signed
  dimension inequality with empty support having dimension minus infinity.
- Rf_* is the existing `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f`,
  the right derived module direct image on D^+, evaluated at L.
- The first conjunct is `DerivedCategory.isBoundedConstructible Λ Y` of the
  underlying derived output. Its definition requires every cohomology sheaf to
  be constructible and vanishing outside an integer interval `[a,b]` with `a ≤ b`.
- The second conjunct is `DerivedCategory.SupportCondition` of the SAME output,
  with the identical closed-support and empty-support conventions.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, through
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule Λ X` is definitionally the ordinary derived category
  of `Sheaf X.smallEtaleTopology (ModuleCat Λ)`. Mathlib's
  `DerivedCategory.Plus` is the bounded-below full subcategory.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`,
  requiring affine inverse images of affine opens.
- The convention node `def-weil-pbc-scheme-conventions` introduces no declaration;
  its meanings are the existing `Scheme`, `Over`, `IsOver`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` used explicitly here.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  objectwise sections over the base change. Its actual bounded-below derived
  declaration is in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `Etale.rightDerivedLowerStarPlus`, defined as `lowerStar.rightDerivedFunctorPlus`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` re-exports
  `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and
  `Scheme.IsConstructibleEtaleModuleSheaf` are the recorded finite-value notions.
- `def-weil-derived-cohomology-sheaves` has a current primary binding
  `WeilConjectures.sfModelCohomology` for intrinsic adic Weil categories. I read its
  signature and docstring; it is not the object of this node. The same dependency's
  recorded `mathlib_match` gives `DerivedCategory.homologyFunctor`, which directly
  provides the general ordinary cohomology notion here. Its representative
  comparison is `DerivedCategory.homologyFunctorFactors`; nothing is duplicated.
- `def-per-support-condition` currently binds `WeilConjectures.QbarSupportCondition`
  on an adic category; I read that declaration and its ambient support definitions.
  This item explicitly says to read the support condition at finite coefficients.
  Its existing closed upstream audit records
  `AlgebraicGeometry.Etale.DerivedCategory.SupportCondition` in
  `WeilConjectures.SixFunctors.Etale.Perverse.Basic`. That exact existing
  finite-coefficient predicate, and `Etale.sheafSupport`, are used directly. No
  rational coefficient objects or completion constructions enter the theorem.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.isIso_of_isIso_sheafFiber_map` is imported for the geometric-stalk
  conservativity used by the natural-language proof. Its full signature applies
  to module-valued sheaves as well as abelian-group-valued sheaves.

Proof-only imports retain the available node declarations:
`Scheme.etaleSheafSupport` (EtaleSupport),
`Scheme.affine_direct_image_support_bound` (AffineDirectImageSupportBound),
`Etale.nonempty_higherDirectImage_forget_iso` (HigherDirectImageForgetComparison),
`topologicalKrullDim_closed_irreducible_eq_trdeg` (ClosedIrreducibleDimensionTrdeg),
`Scheme.constructibleEtaleModuleSupport` (ConstructibleEtaleModuleSupport),
`Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`
(FiniteTypeDirectImageConstructibility),
`CategoryTheory.Triangulated.TStructure.isHomological_homology₀` (TStructure.Homology),
and the derived-direct-image shift and triangulated instances in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
The remaining proof leaves have no separate recorded Lean module; their ordinary
standard-t-structure, constructible topology, Noetherian and sobriety APIs are
already available through these imports. No new independent statement was added.

Source and edge-case check:

I read BBD Theorem 4.1.1 and the surrounding 4.0.1' support formulation in the
local PDF (printed page 102), and Stacks `etale-cohomology.tex`,
`lemma-interlude-I` (Tag 0F0X). The latter is the torsion sheaf support estimate,
not a stronger arbitrary-field-coefficient statement. The finite exponent makes
all module sheaves torsion, and the proof retains the module/abelian higher-direct-image
comparison and the constructible-stalk-to-closed-support argument.

L = 0 and empty X or Y are allowed: no Nonempty or positive-dimensional hypothesis
occurs. The zero coefficient ring has additive exponent 1, so it is allowed over
any field, and all its module sheaves vanish. Negative i requires empty support;
i = 0 permits punctual cohomology in degree zero. For q > i the sheaf-level bound
gives empty support, as in the proof. The identity map specializes to a bounded
constructible L because its D^+ and support hypotheses already force boundedness.
A lisse sheaf on a curve must be placed in degree -1 to meet this support condition,
checking the sign H^{-i} and the shift F_i[i]. No field is required separably closed,
no characteristic is excluded except through invertibility of the actual exponent,
and no finite Tor-amplitude or uniform degree bound is added.

Searches for existing statements (all before writing):

- `msearch.py leanfinder`: “Affine finite type morphism preserves perverse support
  condition for bounded below constructible finite coefficient etale complexes”.
  Eight results, all affine scheme geometry or affine limit facts; none is this
  derived support estimate.
- `msearch.py loogle`: `AlgebraicGeometry.IsAffineHom, CategoryTheory.Sheaf`.
  Zero results.
- `msearch.py grep`: `perverse|affine.*support|support.*affine`, scoped to
  Mathlib AlgebraicGeometry. Seven results concerning ideal sheaf support and
  affine-local properties; no match.
- `msearch.py leansearch`: “Artin affine vanishing perverse support condition
  derived direct image”. Eight results on affine limits, Artinian affine schemes,
  ideal support and affine properties; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `SupportCondition`, affine
  support bounds and perverse affine direct images found the exact support
  definition, the sheaf-level affine estimate and the QbarAffineSupportBound
  theorem. None states this finite-coefficient D^+ theorem. The upstream perverse
  Operations file states compact-support perverse bounds, a different functor and
  statement. `grep -rn` of this item's id in `lean/WeilConjectures` found no match.
- Exact-name searches of both source trees and `dag/lean_names_upstream.json`
  found no existing `supportCondition_rightDerivedLowerStarPlus_of_isAffine`.

Validation: `scompile.py NA lem-per-finite-affine-direct-image-support-bound`
compiled the delivered module cleanly against the live server build, including
its canonical module path. After making quasi compactness of f explicit, the
final version also compiled cleanly (3.6 seconds reported per check). No `#check`
commands, local notation, auto-implicit variables or auxiliary proofs remain.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
