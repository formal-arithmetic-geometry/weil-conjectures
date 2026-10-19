## Worker report

The delivery states smooth tensor duality for the entire ordinary unbounded derived
categories of small-etale module sheaves. It supplies the canonical tensor mate as a
real composite, rather than replacing invertibility of that map by existence of an
unspecified isomorphism. The existing upstream SmoothDuality theorem was read in full;
its last clause is only Nonempty of an isomorphism, and its module explicitly documents
that omission, so it is not an exact existing match.

Hypothesis and conclusion correspondence:
- Finite commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
- Positive annihilator N: `(N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)`.
- Noetherian base: `{X S : Scheme.{u}} [IsNoetherian S]`; this Mathlib class means
  locally Noetherian and quasi-compact, equivalently a finite affine Noetherian cover.
- N invertible on S: `hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)`.
- Smooth, separated, compactifiable f with pure relative dimension d ≥ 0:
  `(f : X ⟶ S) [IsSeparated f] [HasCompactification f] (d : ℕ)
  [SmoothOfRelativeDimension d f]`. The relative-dimension class includes smoothness
  (Mathlib's SmoothOfRelativeDimension.smooth); no further smoothness hypothesis is needed.
- All coefficient categories are `DerivedCategoryModule A T`, definitionally
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  There is no boundedness, constructibility, Tor amplitude, field, nonzero ring,
  or pro-etale restriction.
- Inverse image: `(upperStar (ModuleCat A) f).leftDerivedFunctor` is the exact
  termwise inverse image, canonically identified by
  `leftDerivedUpperStarIsoMapDerivedCategory`.
- Exceptional inverse image is the existing `rightDerivedUpperShriek (ModuleCat A) f`,
  the chosen right adjoint of `rightDerivedLowerShriek (ModuleCat A) f`.
  Its adjunction is `rightDerivedUpperShriekAdjunction`.
- Omega is that right adjoint evaluated at `𝟙_ _`, the constant coefficient complex.
- The first existential is a module sheaf L together with an isomorphism from
  omega shifted by `-(2 * (d : ℤ))` to `DerivedCategory.singleFunctor _ 0` of L.
- The jointly surjective etale family is `Scheme.Cover Scheme.etalePrecoverage X`.
  Each localized restriction `L.over (cover.etalePrecoverageToEtale i)` is isomorphic
  to the constant module sheaf with value `ModuleCat.of A A`. This asserts etale local
  free rank one, hence exactly the locally constant condition of the dependency.
  An orientation of L is not selected; all the trivializations occur inside Prop.
- The second conjunct quantifies over EVERY `K : DerivedCategoryModule A S` and says
  `IsIso (smoothTensorDualityMap (ModuleCat A) f
  (isIso_projectionMap_of_finite A f) K)`. The IsIso proof passed to the construction
  is the existing finite-coefficient projection-formula theorem, not an extra hypothesis.
- The helper map first applies compact-support direct image to the canonical Koszul
  swap, then the inverse of `projectionMap`, swaps back, applies tensor with the
  adjunction counit at the coefficient unit, and applies `derivedTensorRightUnitor`.
  Applying the adjunction's homEquiv gives exactly the specified transpose. The two
  swaps solely reconcile upstream's `(omega, K)` factor order with the node's `(K, omega)`.
- `smoothTensorCanonicalDerivedBraiding` directly reuses `DerivedMonoidal.braidedCategory` on Qh and
  quasi-isomorphisms, hence is the canonical descended Koszul symmetry. It contains
  no choice from an unspecified Nonempty isomorphism or braiding.

Dependency declarations used:
- def-asd-compactifiable: Sheaf.AlgebraicGeometry.CompactifiableOverField imports
  WeilConjectures.Compactification.Defs, reusing AlgebraicGeometry.HasCompactification
  and its chosen Compactification; no field-existence theorem is imposed here.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  AlgebraicGeometry.SmoothOfRelativeDimension.
- def-kun-derived-tensor: WeilConjectures.SixFunctors.Etale.Derived.Tensor,
  AlgebraicGeometry.Etale.derivedTensor.
- def-weil-pbc-derived-categories: Sheaf.AlgebraicGeometry.DerivedCategories,
  AlgebraicGeometry.Etale.DerivedCategoryModule.
- def-weil-pbc-inverse-image: WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  AlgebraicGeometry.Etale.upperStar, used through its existing derived interface.
- thm-amb-etale-exceptional-adjoint: Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint,
  AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification.
  The existing UpperShriek module supplies the chosen functor and adjunction.
- def-amb-etale-compact-support: WeilConjectures.SixFunctors.Etale.Derived.LowerShriek,
  AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification and the chosen
  compactification specialization rightDerivedLowerShriek.
- def-constructible-locally-constant: WeilConjectures.ConstructibleSheaf.Defs,
  AlgebraicGeometry.Scheme.Cover.etalePrecoverageToEtale and the localized constant-sheaf
  description in LocallyConstantDatum.
- Added landed prerequisite def-kun-projection-formula-map:
  WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection,
  AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap. It is used by the
  existing compact-support projectionMap through projectionMapOfCompactification.
  Its recorded signature, body and transpose formula were read. The finite-coefficient
  isomorphism theorem is reused to take the inverse of this specified map.

Edge cases checked before stating:
- d = 0: the shift is zero and the same canonical mate is asserted invertible.
- A the zero ring, including N = 1: no Nontrivial instance is assumed; being locally
  isomorphic to A remains the correct rank-one-module formulation.
- X or S empty: the universal stalk-invertibility condition is vacuous where appropriate;
  the Cover formulation allows empty families and introduces no geometric-point existence.
- Arbitrary unbounded K: the quantifier ranges over the whole derived category.
- The site and coefficient universes follow the landed ordinary-etale convention,
  with schemes in Type (u + 1) and coefficient modules in universe u + 1.

Searches:
- msearch.py leanfinder, query "smooth etale exceptional inverse image dualizing
  complex tensor projection formula": eight unrelated etale algebra/differential hits.
- msearch.py loogle, query '"dualizing"': zero hits.
- msearch.py grep, query 'Smooth.*(Dual|Tensor)|smooth.*(dual|tensor)': sixteen
  commutative-algebra/calculus hits; no smooth etale derived duality statement.
- msearch.py leansearch, query "For a smooth morphism the canonical map pullback tensor
  dualizing complex to exceptional inverse image is an isomorphism": service unavailable,
  Internal Server Error; the other searches and direct source reads were used.
- rg over WeilConjectures for the node id and projection/smooth-duality names found the
  weaker SmoothDuality statement and the canonical LowerStarProjection and
  LowerShriekProjection constructions. Both were read in full, along with TensorStructure.
- rg over lean/Sheaf and dag/lean_names_upstream.json for SmoothTensorDuality,
  smoothTensorCanonicalDerivedBraiding and smoothTensorDualityMap: no existing declarations.
- The source blueprint file and all eight original dependency node statements and
  declaration signatures/docstrings were read. The landed projection-map prerequisite
  was also read, and is cited in stmt_deps rather than duplicated.

No statement correction, new node, dependency repair, or statement dispute is required.
The theorem docstring reproduces all seven DAG proof steps for stage 3.

The canonical construction is written for a general coefficient category and then specialized
to ModuleCat A. This avoids the documented expensive concrete tensor-instance comparison in
upstream TensorStructure. The braiding provider is written for a general abelian monoidal category with derived
category; its data is exactly DerivedMonoidal.braidedCategory. The map uses that
specified structure internally as letI instances, without a global instance or a
Nonempty choice. The instance_reducible attribute follows Lean's class-valued-definition
convention and suppresses no warning. This formulation compiles quickly.
All theorem proofs in the delivery are sorry; all helper definitions have real data.

The directly stated proof dependencies are imported, including the local twist line,
compact-support comparisons, and the ringed-topos tensor and exchange comparisons.
The not-yet-recorded proof inputs lem-amb-etale-adjoint-locality,
lem-amb-proper-coproducts-projection and lem-asd-ordinary-finite-p1-adjunction have no
module import yet. The existing upstream finite projection-formula theorem suffices to
construct the canonical map, without waiting for proofs. The Mathlib homology and exact
stalk declarations are already imported through the corresponding derived/stalk modules.

The upstream HasCompactification class allows a non-quasi-compact open immersion in
general. Here S is Noetherian, so the proper compactifying scheme is Noetherian;
every open subscheme is then quasi-compact. Consequently this binder recovers the
finite-type compactifiability meant by def-asd-compactifiable, without an omitted
finite-type case or an additional finiteness assumption. The explicit IsSeparated
binder retains the node's listed separation hypothesis.

Validation: the final full module compiled cleanly through scompile.py in both its
sandbox and library forms (6.8 seconds and 7.1 seconds respectively). There are no
warnings. The sole postponed proof is the named smooth_tensor_duality theorem;
the canonical map and canonical braiding provider contain actual construction data.

## Second reading by NZ

I read the node `thm-asd-smooth-tensor`, its source place
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-asd-smooth-tensor.md`,
and the complete module `Sheaf.AlgebraicGeometry.SmoothTensorDuality`.
The item-by-item correspondence is:

- The finite commutative coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Verdict: exact.
- The positive annihilator is `(N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)`.
  Verdict: exact, including `N = 1` and the zero ring.
- The Noetherian base is `{X S : Scheme.{u}} [IsNoetherian S]`.
  Verdict: exact.
- Invertibility on the base is the stated `hInvertible : ∀ s : S,
  IsUnit (N : S.presheaf.stalk s)`, matching the finite-etale twist-line dependency.
  Verdict: exact local-ring formulation; no stronger global-section assumption is added.
- The morphism hypotheses are `(f : X ⟶ S) [IsSeparated f] [HasCompactification f]` and
  `(d : ℕ) [SmoothOfRelativeDimension d f]`. `HasCompactification` supplies the finite-type
  consequences on a Noetherian base, while the explicit separation binder records the node's
  hypothesis. Verdict: exact, with no field, boundedness, constructibility, or pro-etale premise.
- The coefficient categories are `DerivedCategoryModule A S` and the map uses the existing
  exact `upperStar` left-derived inverse image and unbounded `derivedTensor`; the target is
  `rightDerivedUpperShriek`. Verdict: exact ordinary small-etale derived categories.
- The first conclusion is
  `∃ L, Nonempty (dualizingComplex ... f ⟦-(2 * (d : ℤ))⟧ ≅ singleFunctor ... L)`.
  Verdict: exact rendering of `ω_f[-2d] ≅ L` in degree zero.
- The local rank-one conclusion is the existential etale cover and, for every `i : cover.I₀`,
  `Nonempty (L.over (...) ≅ constantSheaf (...).obj (ModuleCat.of A A))`.
  Verdict: exact local free rank-one trivialization, with no orientation chosen.
- The universal tensor conclusion is `∀ K : DerivedCategoryModule A S, IsIso
  (smoothTensorDualityMap ... K)`. Verdict: exact quantifier over the entire unbounded category.
- The helper `smoothTensorDualityMap` is the actual composite: canonical Koszul swaps,
  inverse specified projection map, swap back, tensor with the exceptional-adjunction counit
  at the unit, and the derived right-unitor, transposed by the existing adjunction. Verdict:
  exact canonical mate required by the node, with no unspecified `Nonempty` isomorphism.

The edge cases checked are `d = 0` (zero shift), the zero coefficient ring and `N = 1`, empty
schemes and vacuous stalk conditions, and arbitrary unbounded `K`. Universes are retained as
`Scheme.{u}` and `ModuleCat.{u + 1} A`; the cover index has the scheme universe and does not
exclude an empty cover.

I repeated the three required searches. `msearch.py` LeanFinder queries for smooth etale
exceptional tensor duality returned only unrelated tensor and smooth-ring declarations;
Loogle's dualizing query returned no match; grep over Mathlib and both project source trees
found no exact smooth tensor-duality map or theorem. The upstream `SmoothDuality` theorem was
read in full and is weaker (it asserts only existence of an isomorphism and omits the specified
canonical map), so it is not an existing match. The landed `def-kun-projection-formula-map`
record and source declaration were also read and added to `stmt_deps`; its canonical projection
map is the exact dependency used by `isIso_projectionMap_of_finite`.

No mismatch was found in the worker's statement or construction. I made no Lean changes. The
module compiles cleanly with `scompile.py` (sandbox and library forms, no warnings); only the
named theorem proof remains `sorry`, as required for stage 2.
