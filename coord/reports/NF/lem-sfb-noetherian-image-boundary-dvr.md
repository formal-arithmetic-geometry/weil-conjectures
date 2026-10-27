## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr` states
`AlgebraicGeometry.exists_dvr_of_mem_closure_range_not_mem_range`, with the whole proof
`sorry`. No definition, helper, dependency repair, or statement correction was necessary.

Hypothesis and conclusion correspondence:

- Schemes U and Y and their morphism g are `{U Y : Scheme.{u}} (g : U ⟶ Y)`.
- Finite type is exactly `[LocallyOfFiniteType g] [QuasiCompact g]`, as prescribed by
  def-weil-finite-type-morphism's recorded conjunction; neither separatedness nor
  quasi-separatedness is assumed.
- Locally Noetherian Y is `[IsLocallyNoetherian Y]`.
- The chosen point is `(y : Y)`. Membership in the Zariski closure of the image is
  `(hy : y ∈ closure (Set.range g))`, using the scheme's native topology.
- Being outside the image is `(hy_not : y ∉ Set.range g)`.
- The existential A, its commutative ring structure, domain structure, and
  `IsDiscreteValuationRing A` give precisely a DVR. The latter class extends
  local principal-ideal-ring structure and requires a nonzero maximal ideal.
- The existential K, `Field K`, `Algebra A K`, and `IsFractionRing A K` give a
  fraction field with its canonical injective ring map `algebraMap A K`.
- The maps called u and v in the node are `(a : Spec (CommRingCat.of K) ⟶ U)`
  and `(v : Spec (CommRingCat.of A) ⟶ Y)`. The name a avoids shadowing universe u.
- The equation `a ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ v`
  is g composed with u equals v composed with j (Lean composition runs left to right).
- `v (IsLocalRing.closedPoint A) = y` is exactly the closed-point requirement.
  Mathlib defines this point as `⟨maximalIdeal A, ...⟩`, not an arbitrary closed point.
- All objects use explicit universe u. A and K can be chosen in the universe of the
  affine chart rings and residue fields of U and Y; no independent smaller test universe
  or extra size restriction is imposed. All variables and universes are explicitly bound.

Dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and its
  morphisms (`Scheme.Hom`).
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; quasi-compactness is
  `AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (all affine rings Noetherian, equivalent to
  the node's affine-cover presentation, as its existing record explains).
- def-sc-discrete-valuation-ring: the node has no lean record; its mathlib_match is
  `IsDiscreteValuationRing` in `Mathlib.RingTheory.DiscreteValuationRing.Basic`, used
  together with `IsDomain` exactly as its signature requires.
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- Standard auxiliary notation is reused directly: `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`, and `IsLocalRing.closedPoint`
  from `Mathlib.RingTheory.Spectrum.Prime.Topology` (exported by Scheme).

The theorem docstring follows all five node proof steps, including the nonfield
argument from the strict prime inclusion. The recorded, stated proof dependencies are
imported with plain imports: the upstream quasi-compact closure-specialization theorem,
localization at a prime, residue fields, Noetherian rings, and the Mathlib residue-field
finite-generation interface (ResidueField.Ideal, EssentialFiniteness,
IntermediateField.Adjoin.Algebra). The proof-only node lem-sfb-local-domain-fg-field-dvr
has neither lean nor mathlib_match in the read snapshot, so has no import to add yet;
it is explicitly cited in the proof docstring. It is not a statement prerequisite.

Edge cases checked: empty U has empty image closure, so the premise is impossible;
empty Y admits no y. A surjective morphism has no point satisfying hy_not. A closed
image likewise gives no boundary point. The zero ring is excluded by IsDomain A,
and a field A is excluded by the nonzero maximal ideal in the DVR class. No assumption
that y is closed in Y is made; only its preimage is the closed point of Spec A.
No generic-component, residue-field equality, characteristic, excellence, or finite-type
hypothesis on A is inserted. The boundary restriction is already in the node and is
retained verbatim; no node fault or disputed statement was found.

Sources inspected: `literature/stacks-project/limits.tex`, the full lemma and proof
at label lemma-reach-point-closure-Noetherian (Tag 0CM2), and the node's five-step
boundary-specific affine expansion. The example CompactObject module is withdrawn
in this checkout; its node points to the upstream WeilConjectures module, whose header
and public declaration conventions were read instead. No repository file was edited.

Searches (2026-10-22):

- msearch.py leanfinder: “A boundary point of the image of a finite type morphism to a
  locally Noetherian scheme is reached by a discrete valuation ring whose generic point
  lifts to the source”; eight results, including ValuativeCriterion.Existence.specializingMap,
  Scheme.range_fromSpecStalk, and valuative square fields. None is the boundary-DVR theorem.
- msearch.py loogle: `"IsLocallyNoetherian", "IsDiscreteValuationRing"`; zero results.
- msearch.py leansearch: “DVR curve selection for boundary points of finite type scheme
  morphism images”; eight DVR class and valuation-ring results, no geometric assertion.
- msearch.py grep: `reach.*[Cc]losure|[Cc]losure.*[Dd]vr|[Dd]vr.*[Cc]losure|IsDiscreteValuationRing`
  in Mathlib/AlgebraicGeometry; seven unrelated DVR hits (elliptic reduction, L-function,
  order of vanishing). Read ValuativeCriterion.Existence: it assumes all valuation-ring
  lifts, rather than constructing this diagram from the given finite-type hypotheses.
- rg over lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `boundary.*[Dd][Vv][Rr]|[Dd][Vv][Rr].*boundary|noetherian_image_boundary|lem-sfb-noetherian-image-boundary-dvr`:
  only downstream properness documentation and unrelated boundary results.
  `grep -rn lem-sfb-noetherian-image-boundary-dvr lean/WeilConjectures` had no hits.
- Broader rg for IsDiscreteValuationRing in both project AlgebraicGeometry trees found
  `WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait`; its full declaration
  `exists_trait_of_strict_specializes` was read. It traces a strict specialization in Y,
  but supplies no fraction-field map to U or commutative square over g, so is not this item.
  GenericDvrPropernessCriterion likewise is a properness criterion, not this assertion.
  The proposed new declaration name has no source or Mathlib collision.

Validation: scompile.py NF lem-sfb-noetherian-image-boundary-dvr compiled this module
both as sandbox Sheaf.Stage2.Sandbox0 and at its library module path, cleanly (1.9 s each).
The only postponed proof is the main theorem, as required for stage 2.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
