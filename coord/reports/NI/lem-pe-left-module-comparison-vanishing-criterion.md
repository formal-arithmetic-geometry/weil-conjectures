## Worker report

The module `Sheaf.AlgebraicGeometry.LeftModuleComparisonVanishingCriterion` states
`AlgebraicGeometry.ProEtale.isZero_rightDerived_comparisonLowerStar_of_evaluation`.
Its sole theorem has proof `sorry`; there are no new definitions, other postponed
lemmas, new nodes, dependency repairs, or changes to the natural-language statement.
Only the item's `lean` field changes.

Sources read: Stacks `proetale.tex`, lemma-relative-comparison (099V), especially
the first paragraph, and `sites-modules.tex`, lemma-abelian (03DA), with the preceding
kernel/cokernel construction; also the current main-20261015 blueprint's
`sec-proetale-coefficients/sk-prop-sf-comparison/sk-prop-sf-comparison.proof.md`.
The theorem docstring carries all four steps of the node's expanded proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme X is `(X : Scheme.{u})`.
- A discrete associative unital coefficient ring, possibly noncommutative, is
  `(Λ : Type (u + 1)) [Ring Λ]`. No topology on Λ, commutativity, or finiteness
  instance is supplied. Here “discrete” means constant scalar coefficients.
- The small sites are `X.Etale`, `X.smallEtaleTopology`, `X.ProEt`, and
  `Scheme.ProEt.topology X`. Their object universe is u+1 and morphism universe u;
  the coefficient and module universe u+1 is the common larger universe in the node.
  This does not identify the site's object and morphism universes.
- Left modules over the associated constant ring sheaf are represented by
  `Sheaf J (ModuleCat.{u + 1} Λ)`. This is the fixed-scalar encoding: restriction of
  a constant-ring action along the sheafification unit gives a Λ-action on each
  section group; conversely locally representing constant-ring sections by scalars
  gives their action, uniquely by the sheaf condition. These constructions retain
  the original sections and morphisms and work for noncommutative rings. This is
  also the encoding already used in the recorded parent
  `lem-pe-comparison-injective-left-modules-acyclic`, which explicitly allows it.
  We introduce no second category, scalar map, or replacement module structure.
- The arbitrary pro-etale module sheaf is the binder
  `M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`.
  It has no injectivity, inverse-image, flatness, torsion, or other hypothesis.
- The comparison direct image is the existing
  `comparisonLowerStar (ModuleCat.{u + 1} Λ) X`. Its definition is exactly
  `(Scheme.toProEt X).sheafPushforwardContinuous ...`, hence restriction on
  objects and arrows with the same left scalar actions. No comparison map is
  supplied as a free parameter.
- The positive integer q is `(q : ℕ) (hq : 0 < q)`; positive integers are precisely
  the positive natural indices of the nonnegative injective resolutions.
- “For every etale W -> X” is `∀ W : X.Etale`, including non-affine and empty W.
  `op ((Scheme.toProEt X).obj W)` is its actual pro-etale-site object.
- Abelian evaluation is `sheafToPresheaf ... ⋙ (evaluation ...).obj ... ⋙
  forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}`. Its object is exactly M(W)
  with scalars forgotten. The `rightDerived q` is applied to this entire composite,
  so it uses module-injective resolutions; it does NOT derive the underlying abelian
  sheaf separately or assume a forgotten injective module is abelian-injective.
- The vanishing assumption is `h : ∀ W, IsZero ((...rightDerived q).obj M)` in
  AddCommGrpCat. The conclusion is `IsZero (((comparisonLowerStar ...).rightDerived
  q).obj M)` in the etale module-sheaf category, not just on stalks or global sections.
  Mathlib's `Functor.rightDerived` and `InjectiveResolution.isoRightDerivedObj`
  implement precisely the injective-resolution convention of the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale` and
  `Scheme.smallEtaleTopology`, the jointly-surjective covering definition.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, weakly etale objects,
  and `Scheme.ProEt.topology` (reexported by the comparison module).
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the recorded
  `Scheme.proEtaleSiteComparison`, its finite-limit theorem, and
  `Scheme.proEtaleSiteComparisonModules`. The latter specializes to finite rings;
  the underlying upstream restriction `ProEtale.comparisonLowerStar` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` is already defined for
  any Grothendieck abelian coefficients, in particular ModuleCat Λ for [Ring Λ].
  Thus no dependency repair or extra finiteness hypothesis is required.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, sheafification
  of the constant presheaf; the module header explains its scalar-action encoding.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the recorded transparent Mathlib `SheafOfModules` specialization; its constant-ring
  interpretation is represented here by the fixed-scalar encoding explained above.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj` (the latter is for the future proof).
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective` and `InjectiveResolution`, read with their fields and docstrings;
  reexported through RightDerived's abelian resolution import.
- Proof dependency `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`:
  `SheafOfModules.isGrothendieckAbelianOfUniverses`, imported privately as planned
  by the DAG; it gives the intrinsic ringed-module Grothendieck statement.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` and
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` supply
  the fixed-scalar sheaf Grothendieck instance and the recorded
  `IsGrothendieckAbelian.enoughInjectives`. These imports must be public because
  the exported theorem's rightDerived terms need their resolution instances.

Edge cases checked mathematically before drafting: Λ = 0 (all unital modules zero),
M = 0, the empty scheme, empty etale W, the first positive degree q = 1, arbitrary
non-affine W, noncommutative matrix rings, infinite rings, and M with no inverse-image
presentation. None is excluded. q = 0 is intentionally outside the node; its positivity
hypothesis was retained. Exactness of evaluation on sheaves is NOT assumed: only
sectionwise kernel formation and sectionwise surjectivity onto the cycle sheaf are
used by the proof. Every derived evaluation uses the same kind of module resolution.

Searches actually run using batch2/msearch.py (2026-10-21):

- leanfinder: “Objectwise vanishing of derived evaluation implies higher direct image
  of a sheaf of left modules vanishes”. Eight hits, including
  `Functor.isZero_rightDerived_obj_injective_succ`, derived-category injective
  vanishing and t-structure vanishing, and `Sheaf.H`. None states this criterion
  for arbitrary M.
- loogle: `CategoryTheory.Functor.rightDerived, CategoryTheory.Limits.IsZero`.
  One hit, `Functor.isZero_rightDerived_obj_injective_succ`, whose injective-input
  hypothesis is absent from this node; not an exact match.
- grep: `rightDerived|evaluation`, Mathlib subdirectory
  `Algebra/Category/ModuleCat/Sheaf`. Six hits about evaluation preserving limits
  and the free/evaluation adjunction; no criterion.
- leansearch: “Vanishing of derived sections at every etale object implies the
  comparison higher direct image of a module sheaf is zero”. Eight hits, including
  injective-input vanishing, module sections, scheme section vanishing, and
  degree-zero comparison; no exact match.
- Local rg of `lean/WeilConjectures` for the node id: no match. Local rg of
  `lean/WeilConjectures/CategoryTheory`, the pro-etale comparison modules, and
  `lean/Sheaf/CategoryTheory` for rightDerived/evaluation/exactness found
  `rightAcyclic_lowerStar_of_isZero_rightDerived`, read in full: it concerns
  a morphism of schemes on pro-etale sites, all positive degrees, and affine
  pro-etale tests, not this comparison morphism in a single degree. Existing
  `rightAcyclic_comparisonUpperStar_obj_of_injective` only concerns an injective
  inverse-image input. RingedComparisonInjectiveAcyclicity assumes CommRing and
  such an injective inverse image. Neither can be recorded as this item.
- Local rg of `lean/Sheaf/AlgebraicGeometry` for comparisonLowerStar/vanishing
  and module comparison interfaces found the modules listed above; none states
  the present arbitrary-M implication. `ConstantRingModuleSheaves` was read to
  check the scalar-action interpretation (its explicit equivalence is specialized
  to commutative rings, so it is not incorrectly applied here).

Validation: prescribed scompile.py passed both sandbox and actual library-module
compilation with no errors or warnings (2.3 s and 2.5 s). Initial compilation
exposed private imports of resolution-providing instances; making those imports
public repaired the interface. Temporary #synth/#check diagnostics were removed.
All variables and the universe are explicitly bound. No STATEMENT-DISPUTED flag
or statement fault was found.

## Second reading by NI

A separate second pass by this worker reopened the node and final Lean file; this
is a self-check, not a claim of an independent second agent. The dispatcher brief
requires the maintainer's independent delivery review and forbids starting agents.

The comparison checked all binders above: Scheme X; arbitrary Ring Λ; unrestricted
pro-etale module M; positive degree; every etale W; the entire abelian-evaluation
composite derived in the module category; and vanishing of the module-valued higher
direct image. The fixed-scalar representation has the same left actions as the
constant-ring representation and matches the parent's already recorded interface.
The potential error of deriving after forgetting at the category level is avoided:
forget₂ occurs inside rightDerived. The potential error of testing only affine W
is avoided by `∀ W : X.Etale`. The public-import correction described above was the
only change after the initial draft. No mismatch in mathematical content was found.
