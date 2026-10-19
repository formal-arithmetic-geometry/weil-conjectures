## Worker report

This repair states `moduleObject_ringedSite_derived_comparison` in
`Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison`. All theorem proofs remain
`sorry`; definitions contain actual data. The accepted global Hom/evaluation clause
and `TensorComparison` are retained. The local clause now compares the framework's
native local derived tensor and internal Hom with the ringed K-flat/K-injective
models, rather than defining the local operations by transport of those models.

Hypothesis and clause correspondence:

- `(X : Scheme.{u})` is an arbitrary scheme. Its site is the actual
  `Scheme.ProEt.topology X`, with object universe `u+1` and arrow universe `u`.
  No equality of these universes is imposed. Coefficients/modules and derived Hom
  groups use universe `u+1`.
- `Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}` with
  `[MonObj Λ] [IsCommMonObj Λ]` is an arbitrary commutative condensed ring object.
  `condensedRingObj Λ X` is the existing coefficient ring object `p_X^*Λ`.
- `Internal` is `Mod` over this ring object; `ring` is its `sectionRingSheaf`;
  `Modules` is the existing sectionwise `SheafOfModules` category. `equivalence`
  is the dependency's actual `sectionModuleEquivalence`, leaving sections/maps
  unchanged. `forward` is exactly its `functor.mapDerivedCategory`.
- The global native tensor and Hom are `CondensedRing.derivedTensor` and
  `CondensedRing.derivedHom`. The ringed Hom `hom` is the recorded
  `derivedInternalHomOfUniverses.{u+1,u,u,u+1}` on `ring`.
- Existential `S` and `T` provide closed ringed data and its recorded representative
  model (`CoefficientClosedStructure`, `CoefficientTensorModels`). These are
  outputs, not assumptions. `t : TensorComparison Λ X S T` identifies the actual
  native derived tensor with this ringed tensor. Its K-flat normalization uses
  `localizationIso`, `localizationTensorMap` and `totalComparison`, whose data
  are fixed on every total summand by `ordinaryTensorIso` and thus on pure tensors.
  K-flatness restricts representative tests, not the derived objects K,N.
- `θ` is a natural isomorphism on the product of the opposite and ordinary derived
  categories. This includes contravariant naturality in K and covariant naturality
  in N, for all unbounded objects. Its components are the claimed isomorphisms.
- The first conjunct is the evaluation equation. It applies `forward.map` to
  the native Koszul exchange followed by `derivedTensorHomAdjunction.counit`.
  The other side is `t.iso`, then `S.tensor.map (θ,identity)`, then `S.evaluation`.
  The exchange reconciles the native left tensor adjunction with the ringed
  right tensor evaluation. `internalBraiding` is the localized Koszul braiding,
  transported only along equality of the native and localization monoidal data.
- The second conjunct quantifies over every `U : X.ProEt`. `sliceRingObject` is
  restriction by `J.overPullback`, with the induced multiplication and commutativity;
  `SliceInternal` is the actual `Mod` category on the slice. `sliceSectionRing_eq`
  identifies the reconstructed ring with the literal `(ring Λ X).over U`.
  `sliceEquivalence` retains the actual section-action equivalence across this
  equality. Its additivity gives `sliceDerivedEquivalence` on ordinary unbounded
  derived categories. `sliceInternalRestriction` is the canonical exact
  restriction expressed through these equivalences; its section comparison is
  their counit. This transport concerns restriction, not tensor or internal Hom.
- `sliceNativeTensor` abbreviates the framework's native monoidal tensor on
  `DerivedCategory (SliceInternal Λ X U)`. `sliceNativeHom` is literally the
  uncurrying of `MonoidalClosed.internalHom` on that category. Neither depends on
  the existential `SU`, `TU` or ringed Hom. `sliceNativeEvaluation` is its native
  adjunction counit preceded by the actual localized Koszul exchange.
- The new existential `tU : SliceTensorComparison Λ X U SU TU` identifies that
  independent native local tensor with the ringed tensor. Its `normalization`
  is the local K-flat localization square. `sliceRawComplexTensorComparison`
  fixes every integer summand p+q=n using the dependency's pure-tensor-normalized `sliceOrdinaryTensorIso`.
  `sliceRawComplexTensorIso` selects that uniquely determined map.
  `sliceTotalComparison_existsUnique` transports the entire fixed isomorphism
  to the native endpoints; `sliceTotalComparison` selects only that unique datum.
  HEq bridges the two presentations of the restricted section ring. It does not
  forget the summand maps or permit arbitrary comparison isomorphisms.
- `RingedSliceEvaluationNormalized ... d` retains the existing ringed restriction
  and evaluation normalization. `SliceHomComparison ... SU TU tU d θ` contains
  the local natural isomorphism θ^U on ALL local derived objects, its equation
  identifying native evaluation through tU with ringed evaluation, and r_U from
  restricted global native Hom to native Hom of restricted objects.
  `compatibility` is Step 5's full square. It includes the canonical
  section-restriction counits and their inverse in the contravariant Hom slot.
  r_U is fixed by that square and full faithfulness. θ^U now compares independent
  native and K-injective constructions; it is no longer an equivalence counit.

Dependency declarations used (full signatures/docstrings were read in the retained
packet and reopened where the repair changes the interface):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, `coefficientRing` and their monoid/commutativity instances.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`;
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`:
  `monoidalCategoryCochainComplex`, `derivedMonoidalCategory`, `laxMonoidalQ`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed` and
  `Mathlib.CategoryTheory.Monoidal.Closed.Basic`: native closedness,
  `MonoidalClosed.internalHom`, `internalHomAdjunction₂`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom`, `derivedTensorHomAdjunction` and `derivedTensor`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf`, `sectionModuleEquivalence`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
  `internal_section_tensor_comparison`, `comparison_internalTotalExists`,
  `comparison_additive` and the pure-tensor/total-summand normalizations.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses` with independent site universes.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `CoefficientTensorModels`, `coefficientTotalTensor` and their canonical evaluation.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  literal restriction and `overFunctor`, `overMap`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `ringedSliceDerivedRestriction`.
- `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`:
  `RingedSliceEvaluationComparisons`, `RingedSliceEvaluationNormalized` and
  `RingedSliceFlatRestriction`, reused unchanged through its definition node.
- Proof imports retain `LocalizedModuleExactForSystems`,
  `RhomGlobalSectionsOfUniverses` and `RingedInternalHomSignedCalculus`.

Sources reopened: the item's full statement and five proof steps; Stacks
`sites-cohomology.tex` labels equation-internal-hom, lemma-section-RHom-over-U,
lemma-internal-hom and lemma-restriction-RHom-to-U; the published native framework
and `coord/pefw-upstream-framework.md`; the complete tensor comparison and closed
ringed-model source fetched with `scompile.py --source`.

Edge cases checked: empty scheme/site, zero coefficient ring, zero input objects,
all unbounded complexes and negative degrees, arbitrary p,q,n with p+q=n and the
identity slice. There is no nonzero-ring, nonempty-site, boundedness, perfectness,
constructibility or flatness condition on derived inputs. Restriction and both
comparisons use the same site/coefficient universe levels on the slice.

Searches retained from the original packet:

- LeanFinder: equivalence of internal sheaf modules and sectionwise modules
  identifying derived tensor/Hom and evaluation/slices; eight unrelated Hom hits.
- Loogle: `SheafOfModules, derivedInternalHom`; no exact indexed declaration.
- Mathlib grep: `sectionModuleEquivalence|module.*ringed.*comparison`; no hit.
- LeanSearch: internal module objects equivalence sectionwise sheaf modules
  derived internal Hom; sheaf-Hom/global-sections results, no comparison theorem.
- `rg` in the prescribed upstream/side trees and the DAG: no existing theorem
  for this node, and no pre-existing local normalized module-object comparison.

Additional repair searches (2026-10-18):

- `msearch.py ... leansearch`: native derived tensor/internal Hom of module
  objects over a restricted ring on a slice site; eight presheaf tensor/module
  Hom hits, no derived slice comparison.
- `msearch.py ... loogle`: `MonoidalClosed.internalHom,
  MonoidalClosed.internalHomAdjunction₂`; the service index does not recognize
  the former. The actual Mathlib source supplies both and is used directly.
- `msearch.py ... grep`: `sliceNativeHom|sliceTensorComparison|
  SliceTensorComparison|sliceTotalComparison` in CategoryTheory; zero hits.
- Exact `rg` across the DAG, `lean/Sheaf`, and the upstream source returned no
  competing local comparison. Native generic tensor and closed Hom were found
  in the published framework and reused, not reconstructed.

No change to the item's mathematical statement or proof is needed. The new local
notion's statement is corrected as requested by F1; it was introduced by this
unlanded packet. No `STATEMENT-DISPUTED` issue remains.

## Second reading by Q30

Independent reading on 2026-10-18 by the newly dispatched Q30 repair session,
which did not author the saved Lean packet. I opened all five sandbox node files,
all four delivered modules, the returned slice module, the current shared item
and dependency records, and the native framework and Stacks source. This replaces
the earlier author's self-check; no additional agent was started.

The scheme binder is `X : Scheme.{u}`, its site is `Scheme.ProEt.topology X`,
and coefficients are arbitrary abelian sheaves on coherent Profinite with MonObj
and IsCommMonObj. These express the small-site size convention and arbitrary
commutative condensed ring without a topological presentation or nonzero condition.
`Internal`, `Modules`, `ring`, `equivalence`, `forward` and `complexForward` use
B = condensedRingObj and the recorded section-action equivalence. I read the
published sectionModuleEquivalence source through scompile.py --source: its
forward functor keeps the underlying section groups and maps. `forward` is its
actual mapDerivedCategory, not a different derived equivalence.

For the global conclusion, theta's product/opposite domain gives both required
naturalities. Its source uses CondensedRing.derivedHom and its target the fixed
K-injective derivedInternalHomOfUniverses. The evaluation conjunct sends the
native adjunction counit, preceded by the native Koszul exchange, through forward;
then compares it with t.iso, theta tensor identity and S.evaluation. The exchange
is needed because the native adjunction tensors K on the left, while the ringed
model evaluates Hom tensor K. S and T are existential conclusions, not added
hypotheses. TensorComparison.normalization fixes t on every pair of K-flat
representatives through the actual localization factor and the pure-tensor total
comparison. No boundedness or flatness of arbitrary derived inputs is imposed.

For each U, sliceRingObject is the literal overPullback of B, with the functor's
monoid multiplication. sliceSectionRing_eq compares the two presentations of
the same restricted ring; sliceEquivalence is the exact section-action functor
across that equality. The native monoidal aliases reuse Mod.monoidalCategory,
Mod.monoidalCategoryCochainComplex and Mod.derivedMonoidalCategory verbatim.
sliceDerivedClosed reuses DerivedCategory.monoidalClosed. Thus sliceNativeHom,
sliceNativeTensor and sliceNativeEvaluation are independent of SU, TU and d.
This is the same native closed construction used by CondensedRing.derivedHom,
which I checked in its source. The former transported operations do not occur
in the repaired module or its declaration record.

The new tU is a genuine comparison with these native tensors. I checked the
two fixed localization composites: the left path is tU followed by the tensor
of the section-localization factors; its right path is the image of the native
lax localization map, the localization factor at the total, localization of
sliceTotalComparison, and TU.iso. The flat predicate applies to section images
of representatives. sliceRawComplexTensorComparison states the specialization of the eighth
conjunct of internal_section_tensor_comparison, whose p+q=n equations I checked
against the dependency source; sliceRawComplexTensorIso therefore retains the
ordinary pure-tensor witness and every summand equation. The unique HEq transport
in sliceTotalComparison_existsUnique identifies complete fixed isomorphisms
across equal endpoint presentations and cannot select an arbitrary map.

SliceHomComparison.iso is theta^U on all local derived objects, with native Hom
as its source. Its evaluation field is exactly the local native counit equation
using tU. Its restriction field gives r_U between restricted global native Hom
and native Hom of restricted objects. In the compatibility field, the Hom map
uses the inverse section counit in the contravariant slot and the forward counit
in the covariant slot; the other path is the section counit at global Hom,
restriction of theta, then d.eta. This is the Step-5 square. d has the recorded
RingedSliceEvaluationNormalized representative normalization, so its eta is the
canonical local-family restriction of Stacks 08JB. The remaining counit transport
is only for restriction, as the corrected slice definition explicitly specifies.

I also read each new node against its module. The total node owns the exact
section aliases and summand characterization; the derived tensor node owns
TensorComparison and the generic localization equation; the slice node now
specifies native tensor, Hom and counit plus the normalized tU and restriction
square; the ringed slice node binds the existing normalization definitions
without a copied module. The main node differs from the current shared record
only in lean and its added definition dependencies. Edge cases include the empty
scheme, zero ring and zero objects, identity slice, arbitrary negative degrees
and unbounded complexes. No remaining mathematical mismatch was found. This independent audit replaces the misleading author self-check. F1's saved
mathematical repair is retained. The subsequent compile diagnostics required
performance changes: explicitly typed definitions name the same canonical
functors and factors, and the raw summand witness is stated as a named theorem
with exactly the dependency's equations instead of expanding its existential
projection chain. The evaluation and restriction equations are likewise expressed through the
generic predicates homEvaluationSquare and homRestrictionSquare. Expanding
their specializations gives the audited equations verbatim, including both
section counits and the inverse in the contravariant slot. These changes
preserve the clauses audited above. F3's
explicit totalization instance is retained; all validation keeps the 60-second limit.

Fresh second reading in this repair continuation (2026-10-18): this dispatched
worker did not write the retained four modules. I reopened their complete source,
all five node statements and records, the returned slice source, and the current
shared item and dependency records. I also fetched the current section-equivalence
source with `scompile.py --source` and read the native derived Hom, module-derived
monoidal and derived-closed implementations, the total-summand comparison, the
ringed model and slice-normalization signatures, and Stacks 08J9/08JA/08JB.
The retained packet changes the current shared item only in `lean` and added
statement dependencies. Comparing the returned slice source with this packet
confirms that the transported Hom, tensor, tensor comparison and evaluation were
removed. `sliceNativeHom` has only Λ, X and U as inputs; `SU` and `TU` first enter
at the genuinely constrained `SliceTensorComparison`. The local Hom comparison
quantifies over all local derived objects and its evaluation uses the native
adjunction counit. The normalization has the actual lax localization map, exact
section factor, every-summand total comparison and TU model map on its right path.
The restriction equation has `(c K).inv.op` and `(c N).hom`, matching its two Hom
variances. The new slice node specifies these native operations and both equations.
I found no additional mismatch in the hypotheses, conclusions, four new-node
notions or existing ringed-slice record. No Lean or mathematical node change was
needed in this continuation; the saved F1/F3 repairs are retained. This paragraph
records an actual separate reading of the saved packet, resolving F2 without
starting another agent. The empty scheme, zero ring, zero objects, identity slice
and all unbounded/negative-degree cases remain admitted by the binders.

## New nodes

`def-sfb-internal-section-total-comparison` owns
`Sheaf.Paper.InternalSectionTotalComparison`: the section/module category aliases,
the exact section-action equivalence and its termwise/derived extensions, and
canonical total comparison pinned on pure tensors and every summand. Source:
Step 1; Stacks 03EK and 06YL. Three search kinds find no specialized existing
comparison. The dependency's actual normalized witnesses are reused.
`internalTotalExists` fixes its existing coproduct instance directly, avoiding
the expensive repeated class search noted in F3.

`def-sfb-internal-section-derived-tensor-comparison` owns
`Sheaf.Paper.InternalSectionDerivedTensorComparison`: `TensorComparison`, its
K-flat localization normalization, and the uniquely fixed concrete total
comparison. The global notion and accepted interface are retained. Source:
Step 1; Stacks 06YS and 08J9. Searches in its record find no exact comparison.

`def-sfb-ringed-slice-comparison-model` records the EXISTING canonical restriction,
tensor/Hom comparison and representative normalization definitions in
`Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose`. It uses `existing:true`;
no copy is delivered. Searches distinguish this datum from the theorem using it.
The prior return explicitly accepts this resolution of the ownership fault.

`def-sfb-internal-slice-derived-hom-comparison` owns
`Sheaf.Paper.InternalSliceDerivedHomComparison`. Source: Step 5 and Stacks 03DH,
08J9, 08JB. It records the actual restricted ring/module category, exact section
equivalence and restriction, then the native local tensor/Hom, the unique
pure-tensor/summand comparison, K-flat normalized `SliceTensorComparison`, native
counit normalization and the full Step-5 restriction square. Its statement now
matches these operations instead of prescribing transport. Three search kinds
and exact local searches are listed above and retained in its JSON searches.

## Validation

The prescribed initial dry run was started on the saved packet before editing.
A scratch probe importing an unpublished sibling alone failed because its olean
was absent; sibling files are therefore supplied together to scompile.py, which
compiles them separately in dependency order in one private overlay. This is a
compile-input repair, not a missing dependency or a tool failure.

Every delivered module is compiled individually through scompile.py at the
unchanged 60-second limit. No global build or direct compilation is used.
The local tensor normalization writes both fixed localization composites
directly, with HEq as in the accepted global tensorComparisonNormalized.
The endpoints are the same derived module category and the same representative
objects; heterogeneous equality records the presentations and does not relax
the comparison. Both paths retain the actual local section functors, native
tensor, lax localization map, pure-tensor/summand total comparison and the
ringed K-flat model. The generic tensorLocalizationSquare remains a valid
helper in the derived comparison node, but its local specialization required
expensive type matching and is no longer used for this predicate.
The local total comparison now mirrors the accepted global implementation:
characterize the explicit sum total on all summands, then transport that entire
fixed isomorphism to the native endpoints. This avoids forcing the native tensor
to unfold inside every degree-summand composition. The normalized data are unchanged.

The restricted ring is a named definition, with its canonical functor-induced
monoid structure named as an instance-reducible alias. The native module, cochain and
derived monoidal structures and native derived closed structure are named
instance-reducible aliases of the framework values. They add no alternative
monoidal or Hom data. The local raw total comparison is the named specialization of the eighth
conjunct of `internal_section_tensor_comparison` after its ordinary tensor and
unit witnesses. Its theorem signature explicitly retains the dependency's
exact summand equations with the same pure-tensor-normalized ordinary witness.
This prevents repeated expansion of the entire existential projection chain.
`homEvaluationSquare` and `homRestrictionSquare` state the same two local
equations with generic category endpoints, then specialize to the canonical
functors, native counit, normalized tensor comparison and d.eta. The inverse
section counit remains in the contravariant slot. No condition is omitted.
The profiler located the remaining unfolding cost at the local K-flat
normalization. Its localization factor now has the named sliceComplexForward
in its signature, and the native instance aliases retain standard instance reducibility.
Only their canonical constructor declarations use aggressive unfolding;
normal transparency applies to the normalized predicates. These aliases still have the framework values as bodies.
The theorem docstring explains both specialization and uniqueness on summands.

Only sandbox files are edited; refresh/rebase/delivery bookkeeping is left to
the authorized deliver2.py wrapper. The mandatory initial dry run on the retained packet failed: the total and
derived tensor modules passed in 40.9 and 10.0 seconds, but the slice module
timed out on both compilation routes. This concrete diagnostic triggered the
typed-functor and named-summand-specialization repairs described above.
The independent second reading is recorded above. The repaired four-file
scompile.py run passed cleanly (only expected sorry warnings): total comparison
34.2–38.2 seconds, derived tensor 4.7–5.2 seconds, native local comparison
45.6–59.4 seconds (private overlay 54.6 seconds), main theorem 19.1–19.2
seconds. The first complete repaired dry run compiled every file, then diagnosed a
truncated primary signature record: extraction had stopped at a named-argument
`:=` rather than the theorem body delimiter. The item lean.statement is now
the complete signature through the final conclusion, copied verbatim. The Lean
statement and its mathematical clauses did not change. Final preflight is rerun
after this metadata repair.

Continuation validation (2026-10-18): the mandatory saved-packet dry run
completed successfully: `OK (dry run): commit bc841d0c31 passes the preflight
and compiles; nothing pushed`. All four delivered modules passed both sandbox
and library-path compilation, with the unchanged 60-second limit. The fresh
independent reading above is the only report addition from this continuation;
no Lean source or node signature was changed after that successful check.
