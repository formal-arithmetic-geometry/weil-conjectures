## Worker report

The module `Sheaf.Paper.CompletionSupportedConstantComparison` states
`AlgebraicGeometry.Etale.isIso_localCompletionSupportedPullback`, with `sorry` as
its entire proof. It constructs the completion spectrum map, the quotient closed
point, the canonical signed coefficient comparison and the canonical supported
cohomological pullback. It does not prove the comparison theorem.

Hypotheses and clauses, matched individually:

- The arbitrary excellent Noetherian henselian local ring is `(A : Type u)`,
  `[CommRing A]`, `[IsNoetherianRing A]`, `[HenselianLocalRing A]`, and
  `(_hA : IsExcellent A)`. The henselian class already supplies `IsLocalRing A`.
- The prime and invertibility assumptions are `(l : ℕ) (hl : l.Prime)` and
  `(hunit : IsUnit (l : A))`. No characteristic or residue-field closure assumption
  is added.
- `(n : ℕ) (_hn : 1 ≤ n)` is the positive coefficient level. Coefficients are
  `ULift.{u + 1} (ZMod (l ^ n))`, the same finite ring transported to the coefficient
  universe required by the small etale site. This transport changes no arithmetic.
- The completion is exactly `AdicCompletion (IsLocalRing.maximalIdeal A) A`;
  `localCompletionSpecMap` is `Spec.map` of its `algebraMap` from A.
- `localClosedPointImmersion` is `Spec.map` of the quotient map
  `A → A ⧸ IsLocalRing.maximalIdeal A`. The target support is
  `pullback.snd (localClosedPointImmersion A) (localCompletionSpecMap A)`.
  This is the scheme-theoretic inverse image closed point. The recorded completion
  theorem identifies its residue field with the original residue field and its
  support with the completion closed point. In particular this is ordinary closed
  support, not support at a geometric point.
- Both integer parameters are retained as `(q m : ℤ)`.
  `Scheme.finiteEtaleTateSheaf ... m` is the recorded signed roots-of-unity twist.
  `completionTwistPullbackFamily` selects the published comparison family whose
  generator, unit, positive tensor and negative evaluation equations fix it;
  `localCompletionTwistIso` specializes it to completion. There is no arbitrary
  isomorphism or root-of-unity choice in the definition.
- `localCompletionSupportedPullback` first applies `affineSupportDerivedMap`
  to the twist in degree zero, then applies the target right-derived support
  functor to the degree-zero inverse-image comparison and the canonical twist
  isomorphism, and finally applies integer-degree homology. Thus the conclusion
  `IsIso (localCompletionSupportedPullback A l hl hunit n q m)` concerns the
  canonical pullback itself, not the existence of some isomorphism of the groups.
- There is no regularity or finite-type-over-a-field binder, and no purity finite
  setting, geometric point, or separably closed residue field is assumed.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` and `IsQuasiExcellent`.
- `WeilConjectures.Mathlib.RingTheory.Henselian` and Mathlib's henselian module:
  `HenselianLocalRing`, extending `IsLocalRing`. Strict henselianity is not used.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `.Algebra`, `.LocalRing`:
  `AdicCompletion`, its algebra map, `AdicCompletion.maximalIdeal_eq_map`,
  and `AdicCompletion.residueField_map_bijective` (the last two are for the proof).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `.Morphisms.ClosedImmersion`: `IsClosedImmersion.spec_of_quotient_mk`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections`
  and `derivedSupportedEtaleSections`, the actual kernel of restriction and its
  bounded-below right-derived functor.
- `Sheaf.Paper.SupportedAffineLineHomotopy`: `Etale.affineSupportKernel`,
  `Etale.affineSupportDerivedMap`, and
  `WeilConjectures.PurityFiniteSetting.affineSupportProjectionComplement`.
  These generic declarations have no finite-setting hypothesis: their kernel is
  the pointwise kernel of exactly the restriction used in `supportedEtaleSections`;
  evaluation of a functor-category kernel gives its canonical identification with
  that functor. Its ordinary map is uniquely fixed by the global-section unit and
  kernel inclusion; the derived map uses right-derived base change. Their owner is
  the new existing-definition node `def-per-canonical-etale-supported-pullback`,
  added to `stmt_deps`. The homotopy theorem is not a statement dependency.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`: `Scheme.finiteEtaleTateSheaf`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `Scheme.etaleFiniteTwistPullback`, including its full generator, unit, tensor,
  evaluation and composition characterization; its node is added to `stmt_deps`.
- Mathlib's `DerivedCategory.Plus.singleFunctor`, `.homologyFunctor`,
  `Functor.mapDerivedCategoryPlusSingleFunctor`, and the upstream right-derived
  base-change API supply the degree-zero coefficient transport and cohomology.

The proof-only imports retain the stated proof DAG: completion Noetherianity,
local-completion facts, affine pullbacks and flatness, geometric regularity,
scheme regularity, supported-kernel adjunction, exact forgetful functors, injective
resolutions, enough injectives, bounded-below derived functors and derived
adjunction. `lem-per-regular-supported-base-change` has no recorded Lean module
on the inspected base, so that proof-only import cannot yet be added; its use is
retained explicitly in the theorem's seven-step proof docstring. It is not needed
to type this stage-2 statement.

Edge cases checked: q is an arbitrary integer, including negative degrees and
zero; m is arbitrary, including zero and negative twists, using the actual sheaf
dual construction. n=1 is included. The ring may be a field (then the closed point
is all of Spec A), may be singular, and may have mixed characteristic. Henselian
local rings are nontrivial, so an empty spectrum is not an accidentally excluded
allowed case. Nothing requires finite dimension, finite type, regularity or
strict henselianity. Invertibility of l^n on both spectra follows by mapping the
unit and its power, with explicit natural-number cast transports.

Searches for existing declarations (the previous attempt's searches were
retained in `searches.jsonl` and repeated against current sources):

- LeanFinder, query `Completion preserves etale cohomology with support at the
  closed point of an excellent henselian local ring`: eight hits, all ring-map
  etaleness, etale loci or localizations, none this cohomology comparison.
- Loogle, query `AdicCompletion, IsLocalRing`: twelve hits, including the local
  completion instance, maximal ideal equality and residue-field bijectivity;
  reused those interfaces, no cohomology comparison found.
- Mathlib grep via msearch, query
  `supported.*[Cc]ohomology|[Cc]ompletion.*[Cc]ohomology`: zero hits.
- LeanSearch, query `Completion preserves etale cohomology with support in the
  closed point`: eight hits about stalks, etale loci and uniform completion;
  no comparison theorem.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf` for completion and
  cohomology, and `grep -rn` for the item identifier upstream: no exact theorem.
  The project hits concern formal functions and a depth-three finite-flat model,
  which have different hypotheses and conclusions.
- Read the existing supported-affine-line and signed finite-twist declarations
  in full and reused their generic canonical maps rather than copying them.
  The new definition cites only the existing support-cohomology and ordinary
  etale supported-sections definitions. These and the signed finite-twist
  pullback dependency do not introduce a path back to this item.

Source checked: the retained extraction of ILO XVII, printed pp. 278--281,
contains the completion reduction in Lemma 3.6.3 at p. 279 and the regular
supported base-change statement of Corollary 4.2.3 at p. 281. The latter applies
to Noetherian schemes and bounded-below complexes, without finite type, exactly
as in the node's proof. The original statement is unchanged; no statement fault
or disputed assertion is reported.

## New nodes

`def-per-canonical-etale-supported-pullback` is an `existing: true` definition
node in the item's chapter and unit. It records the generic canonical supported
pullback already in `Sheaf.Paper.SupportedAffineLineHomotopy`; no module or
declaration is moved, copied or changed. Its seven declarations are:

- `AlgebraicGeometry.Etale.affineSupportKernel`: for arbitrary commutative
  coefficients and closed immersion, the pointwise kernel of restriction from
  the terminal etale object to the open complement. This is exactly the
  module-valued specialization of `Sheaf.supportedSectionsFunctor` from
  `def-pur-support-cohomology`.
- `AlgebraicGeometry.Etale.affineSupportInclusion`: inclusion of that kernel.
  Together these agree canonically with `supportedEtaleSections A X
  i.openComplement` and its inclusion from
  `def-pur-etale-derived-supported-sections`: the latter takes the kernel of
  restriction in the functor category, whose evaluation is the same kernel.
- `AlgebraicGeometry.Etale.affineGlobalSectionMap`: the ordinary section map
  from the inverse-image/direct-image adjunction unit, evaluated at the terminal
  object and transported along its canonical base-change isomorphism.
- `AlgebraicGeometry.Etale.affineSupportUnit_existsUnique`: the unique natural
  transformation of supported-section functors whose composite with the target
  kernel inclusion is ordinary section pullback after source inclusion.
- `AlgebraicGeometry.Etale.affineSupportUnit`: that unique transformation,
  selected by `.choose`; the normalization and uniqueness determine the data.
- `AlgebraicGeometry.Etale.affineSupportDerivedMap`: its bounded-below
  right-derived base-change transformation, with exact etale inverse image.
- `WeilConjectures.PurityFiniteSetting.affineSupportProjectionComplement`:
  the complement equality for the scheme-theoretic inverse-image support.
  Despite its namespace, its signature has only schemes, a closed immersion,
  and a scheme morphism; it takes no purity finite setting.

The new statement includes all seven parts: arbitrary coefficient ring, schemes
and closed immersions, the complement equation, the section-unit normalization
and uniqueness, the derived transformation, and the inverse-image-support
specialization. It explicitly cites `def-pur-support-cohomology` and states
agreement of its kernel with `def-pur-etale-derived-supported-sections`, its only
two statement dependencies. The recorded primary signature is copied verbatim
from `def affineSupportDerivedMap` up to `:=`, including its line breaks.

Searches for this ownership repair are recorded verbatim in the new node:
LeanSearch (`etale supported global sections canonical pullback defined by the
unique map of kernels`), LeanFinder (`etale supported cohomology pullback from
the global sections adjunction unit and the derived kernel of restriction`), and
Mathlib grep (`affineSupportDerivedMap|supportedSectionsFunctor|
supportedEtaleSections`). The semantic results concern general kernels,
structure-sheaf pullback, topological presheaf pullback, or ring etaleness;
Mathlib grep has zero hits. DAG and upstream/project grep find these seven
declarations only as helpers of the homotopy module, with no definition-node
owner. `tools/blueprint_refs.py search 'supported pullback'` has no matches, and
its ancestor command confirms `lem-per-artin-gabber-affine-curve`. The current
module was also read through `scompile.py --source` and agrees with the local
source.

Additional edge cases for this generic definition: empty schemes, empty or full
closed support, the zero coefficient ring, and an arbitrary scheme morphism all
make sense. Empty support gives the zero supported kernel; full support gives
global sections; identity pullback has the ordinary identity normalization.
No regularity, finite-type or torsion hypothesis is introduced. The two existing
helper proof obligations retain their source and proof docstrings in their
published module; this delivery adds no postponed theorem.

## Repair of returned H2

The returned head `6e939c3ba278` used the homotopy theorem node to own generic
definitions, although its theorem was never used. The retained packet's initial
dry run passed as `fd91e383ad` without pushing; independent review still required
the ownership repair above. The packet differs from current main only in the
item's `lean` and allowed additions to `stmt_deps`, plus this new definition
node and report. The new node replaces
`lem-pur-supported-affine-line-homotopy` in the item's statement dependencies.
`lem-asd-etale-finite-twist-pullback` is retained: the actual comparison family
is extracted by `.choose_spec.choose` from `etaleFiniteTwistPullback`, as the
return explicitly accepted. The Lean file, mathematical item statement,
hypotheses, proof plan and proof dependencies are unchanged.

## Second reading by NW

No independent second reading by a worker: this dispatched worker delivers
itself, and the maintainer's independent review reads the delivery. The author
has reread the node against every hypothesis and clause above, including the
intrinsic target twist, ordinary closed support, all integer degrees, and the
absence of regularity or finite-type assumptions.

Repair self-check: reread the seven existing signatures and their docstrings,
the new definition statement, both support-definition nodes and their modules,
and the completion consumer. The new definition's complement hypothesis is
exactly the one passed by `affineSupportProjectionComplement`; its derived
transformation is exactly the one applied in `localCompletionSupportedPullback`.
The kernel agreement is canonical, not a claim of definitional equality between
the pointwise kernel and the functor-category kernel. No use of
`supportedAffineLineHomotopy` remains in the statement dependency graph.

Validation: the prescribed scompile wrapper checked the delivered file both as a
sandbox module (49.1 s) and under its library module name (53.2 s), with no errors
or warnings. All data-bearing definitions have explicit constructions, and the
only postponed theorem is the item itself, with all seven proof steps in its
docstring. Automatic and relaxed implicit binding are both disabled.
