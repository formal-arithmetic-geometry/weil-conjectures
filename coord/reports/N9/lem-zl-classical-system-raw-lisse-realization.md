## Worker report

N9 states `lem-zl-classical-system-raw-lisse-realization`; nothing is proved. The
main theorem has one postponed proof, with all nine DAG proof steps in its docstring.
The original statement is unchanged. Eleven new definition nodes own the concrete
comparison interfaces used to express all clauses without extra hypotheses.

Hypotheses and clauses:

- `D : FiniteFieldDatum.{u}` supplies q, p and the algebraic closure k;
  `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` are exactly the prime hypotheses.
- `PerAdic.Base D.k` is the separated finite-type k-scheme. Its noetherianity,
  finite dimension and invertibility are derived by `realizationBase`,
  `baseInvertible`, and `continuousBase`; none is an extra assumption.
- Coefficients are arbitrary finite `E : Type u` with the field, Padic algebra,
  and finite-dimensional instances. The closure has its independent universe v.
  `Padic.coefficientExtensionIntegers`, its uniformizer, quotient rings and ideals
  supply the actual A and quotient coefficients. `scalarReductionSource` is the
  recorded module category over the completed constant integral ring.
- `Integral` reuses `IsLisseIntegralDiagramOfUniverses`; morphisms are the same
  natural transformations of the actual etale towers. `IsFree` imposes finite
  free stalks at every positive exponent n+1, allowing variable and zero rank.
  `Systems` is its full subcategory. `Rational` uses the existing raw
  `ScalarLocalization`, with Away(uniformizer) identified with E through
  `sfRationalCoefficientEquiv`. It adds no objects or idempotents.
- `IntegralComparison.equivalence` relates all lisse completed lattices and
  exactly these finite-free systems. `reduction`, `quotient`,
  `scalar_compatibility`, `completion`, `limit`, `naturality`,
  `unit_projection`, and `counit_projection` state ordinary quotients,
  transition compatibility, inverse-limit reconstruction and actual maps.
  The existing system predicate includes the tensor/reduction isomorphism via
  its surjective stalk transitions and specified kernels.
- `IntegralRealization.constructible` states membership of L[0] in the actual
  sf predicate, retaining its etale-origin witnesses. `objects` and `maps`
  prescribe degree-zero inverse-limit inclusion. `raw_objects`, `raw_maps`
  prescribe the actual raw rationalization and every fraction map.
- `FiniteComparison.objects`, `map_fraction`, `comparison` identify the sf
  composite with ordinary module localization, acting by a times 1 tensor f.
  `IntegralRealization.fullyFaithful` is full faithfulness of the classical
  realization. `PbcComparison` retains identity-induced integral transport,
  rational object and tensor formulas, the derived single-module comparison,
  and `lift`, which realizes exactly the specified isomorphism.
- `Scalar` supplies free-modelled finite extensions with the ideal-normalized
  positive ramification index, the ramification-ceiling finite quotient tensors,
  raw object and fraction formulas, and the normalized module square.
  `Restriction` supplies levelwise actual etale inverse image and its raw,
  fraction and ordinary-comparison formulas. `Coherence` states identity,
  composition and scalar associator equations; `Mixed` gives their mixed square.
- `CommonSystem`, `CommonRealization` and `Common` use the existing StageSystem.PairCategory (the directed-colimit
  quotient of finite-stage Homs). Its stage morphism fixes each finite functor
  and each scalar comparison. Its functor therefore acts on representatives
  by beta, the finite map, inverse beta; `heart` and `fullyFaithful` give
  exactly the common-stage heart and Hom bijections. `CommonRestriction`
  states descended restriction and its finite representative formula.
- `classicalFibre` is literally inverse limit of the recorded geometric stalks
  followed by ModuleCat.extendScalars along A.subtype. Finite sf and PBC fibre
  comparisons, naturality for integral families and fractions, and common
  fibres after extension to the closure are explicit in `FiniteComparison`,
  `PbcComparison`, `Common.fibre_spec`, `Common.finite`, `Common.classical_fibre`, and its
  `classical_normalization`. The last equation uses the finite natural fibre
  comparison, and `PointComparison.natural` retains every rational arrow.
- `pointReparam` uses the existing `pointSmallEtalePrecomp`, lifted only in
  cardinality. `classicalTransport` is its actual inverse-limit map followed
  by scalar extension. `PointComparison.transport` equates this with ordinary
  restriction followed by inverse-image coprojection. It quantifies every
  automorphism, hence includes every finite power, with the existing normalized
  pullback compositor. `RestrictedFibres` applies completed pullback and the
  given stratum isomorphism to any heart object, with its exact formula.

Dependency declarations read and reused (module names under Sheaf.Paper unless stated):

- FiniteFieldFiber: `WeilConjectures.FiniteFieldDatum`.
- Mathlib algebraic closure and scheme morphism properties: `IsAlgClosure`,
  `IsImmersion`, finite-type, quasi-compactness and separatedness classes.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and its imports:
  `Padic.coefficientExtensionIntegers`, quotient/ideal/uniformizer data.
- CompletedIntegralConstantMapOfUniverses: the normalized completed coefficient
  model used by scalarReductionSource and the actual constant scalar action.
- LisseIntegralSmallCoefficients: `IsLisseIntegralDiagramOfUniverses`,
  `adicIntegralFiberOfUniverses`; LisseAdicSheaves supplies classical operations.
- SfConstructibleHeart: `sfRationalHeart`, `sfCommonStageHeartProperty`.
- LisseRationalRealization: `LisseRealization.Family`, its normalized realization,
  pullback, field-change, point and transport structures.
- RationalCoefficientCategoryComparison: identity-induced sf/PBC comparisons,
  `integralDetailedTransport`, `fdRawTensor`, coefficient equivalences.
- ContinuousRationalDerivedRealization: `ContinuousRational.Family`, Base and At.
- GeneralAlgebraicallyClosedCoefficients: the actual finite coefficient
  `stageSystem`, inclusions and directed-colimit category.
- AdicHeartIntrinsicFibres: `sfAdicRationalFiber`, `SfAdicCommonFiberSpec`,
  `sfAdicCoefficientEmbedding`; PerAdic.Base and fibre from its imported module.
- LisseCompletedSystemData/Comparison: the normalized completed-system interface
  and its existence theorem; the new interface specializes the same notion to
  the small coefficients required by the sf categories.
- WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension:
  `pointSmallEtalePrecomp`, retaining the actual germ map.
- ScalarLocalization and StageSystem from their recorded project modules.

Edge cases checked: positive exponents are indexed by n+1, so n=0 means reduction
modulo the uniformizer. The ramification index is positive and its source index is
ceil((m+1)/e)-1. Every geometric point is universally quantified; no point is chosen
on the empty scheme. Rank is an arbitrary natural number, including zero, varying
locally. No nonempty or connected hypothesis, global basis, derived reduction
concentration, or equality of site/coefficient universes is imposed. The quotient
is a cokernel of ordinary multiplication, and L[0] uses the existing single functor.

Searches: LeanFinder plain-language search returned generic condensed and scheme
results, not this statement. Loogle `LisseIntegralSheaf, sfRationalHeart,
FullyFaithful` and `ClassicalRawLisse, IsFreeSystem, ScalarLocalization` found no
exact declaration. LeanSearch on normalized inverse-limit/raw-heart/coherent
operations returned scalar-restriction and inverse-system utilities only.
Mathlib grep through msearch found no classical realization interface. Upstream
WeilConjectures and project Sheaf rg searches found CompletedLisse and normalized
Weil/cohomology interfaces: these are reused where applicable, but none states
the present finite free-system realization theorem. blueprint_refs search found
no matching definition node. The new node records retain the search outputs.

No statement dispute or source correction is asserted.

## Second reading by N9

Independent reader: `/root/independent_review`, a separate worker, with the return
entry, retained delivered files, node records, final Lean modules and BS pp. 58--62 open. The reader checked
all eleven definition nodes and the main theorem. It identified that a free sf-to-point
bridge would preserve the returned H3 defect, so the bridge is now pinned through
`IntegralCompletedComparison.Comparison.gamma`, its finite projection equations,
identity-on-section coefficient transport, and exact H0 comparison maps. The final
square uses the same `a.point`, `a.along` and `FiniteComparison.fibre` as the theorem.
The reader also checked the PBC identity normalization and the transition/completion
unit equations. A suggested reversal of the exact H0 comparison was withdrawn after
reading its actual upstream signature; the delivered formula uses `.hom`, as required.
The section-map binder was renamed after the compiler identified the reserved word.
Final independent reading covered all twelve modules and all twelve node records.
The reader found no remaining numbered-return defect; every recorded declaration
is in its owning module, all statement dependencies exist, and the requested
ownership corrections are present. Compilation results are recorded below.

## New nodes

`def-zl-classical-raw-lisse-realization-data` owns the finite-stage comparison data
and the small-coefficient finite-free system specialization. Its source is BS
6.8.4, 6.8.11 and 6.8.14. Existing CompletedLisse data use coefficient Type (u+1),
whereas the sf raw heart uses Type u; the underlying existing system predicate,
localization and completed ring are reused. This is data, not an existence axiom.

`def-zl-classical-raw-lisse-operations` owns finite scalar/restriction functors and
their defining level, fraction and realization comparisons. Its source is BS 6.8.4
and 6.8.15, with Weil II (1.1.1)d. It reuses the actual existing tensor and inverse
image functors. Related normalized Weil realization data concern Frobenius and
cohomology, not this interface over arbitrary locally closed restrictions.

`def-zl-classical-raw-lisse-common-fibres` owns the common-stage
realization and its fibre comparisons, using the existing StageSystem quotient and normalized completed
fibres. Its source is Weil II (1.1.1)d and BS 6.8.15. No new substitute pair category or fibre is introduced; point comparisons are
owned by the separate point-fibres node below.

`def-zl-classical-raw-lisse-coherence` owns the separate identity, compositor
and mixed comparison data, to keep each module within the per-file compile limit.
Its source is BS 6.8.4 and 6.8.15, using the same existing normalized sf and ordinary
module comparisons. It asserts no existence and adds no hypotheses to the theorem.

`def-zl-classical-raw-lisse-common-restriction` owns descended restriction and
its exact finite representative comparison. `def-zl-classical-raw-lisse-point-fibres`
owns the completed restricted-fibre formula and actual classical point transport.
These are the two portions of the common/fibre interface described above, split
into separate modules to meet the per-file compile limit. Their sources are BS
6.8.15 and Weil II (1.1.1); the same recorded searches found no existing interface.

`def-zl-classical-raw-lisse-scalar-coherence` owns the scalar unit and associator
equations described above; it is separated from restriction coherence to keep
compilation within the fixed per-file limit. It has the same BS source and searches.

`def-zl-classical-raw-lisse-common-system` owns the classical StageSystem and
its exact scalar transition/compositor equations. It is split from the common
realization for the compile limit; its source and searches are those above.

`def-zl-classical-raw-lisse-common-realization` owns the common stage morphism,
its exact finite comparisons, heart condition and full faithfulness. Its source
is BS 6.8.4(4) and Weil II (1.1.1)d; the searches above apply.

`def-zl-classical-raw-lisse-common-restriction-data` owns the descended
restriction stage morphism, its prescribed finite functors and its Mixed-normalized
beta. The comparison node owns its realization comparison and finite whiskerings;
the restriction node records the equality of those whiskerings. These splits retain
the same BS 6.8.15 source and recorded searches while limiting per-file elaboration.

The final common restriction equation is `CommonRestriction.finite_comparison`: it
compares `restrictionFiniteLeft` (the actual whiskering of the descended
comparison) and `restrictionFiniteRight` (the inclusion of the actual finite
comparison). Naming these concrete maps avoids repeatedly elaborating their
large category expressions; no arbitrary replacement maps are supplied.

`def-zl-classical-raw-lisse-common-restriction-comparison` owns the descended
comparison and the two concrete finite whiskerings, split unchanged from the data
module to stay within the compile limit. Its source is BS 6.8.15 and Weil II
(1.1.1)d. Existing Mathlib, upstream, project and blueprint searches found no
matching interface. The existing logged search records and the fresh grep and
Loogle outputs are retained in its node; it adds no mathematical field.

Validation: all twelve delivered modules compiled cleanly through scompile.py
in the final complete packet; only the main theorem uses the expected `sorry`. Delivery validation is performed by deliver2.py, including
the server preflight and per-file compilation.

## Returned-delivery repair

This packet repairs immutable head f0d3b49a8753 against the current published library.
The original theorem statement and its nine-step proof docstring are retained.

- H3 operations: `Scalar.unit_tensor` is the actual balanced-tensor/sheafification
  unit; `Restriction.unit_pullback` is the actual etale adjunction unit. Their
  `transitions` fields fix every tower arrow. The `integralUnit` maps satisfy
  `completion_projection` for every quotient, so the limit property pins them
  to the canonical completion cone. `ordinary_tensor`, after
  `FiniteComparison.objects`, fixes the localization maps on all tensor-one
  generators and pulled-back sections. The existing module squares then pin
  the raw comparisons; identity, compositor and Mixed equations now refer to
  those specified maps.
- H3 descent: `CommonRestrictionData.mixed` and `scalar_comparison` identify
  every beta with the inverse Mixed comparison for that coefficient inclusion.
  Its normalization fixes beta to the actual mixed tensor/pullback comparison.
- H3 fibres: `PbcComparison.fibre_normalization` fixes the PBC/sf comparison to
  identity on each integral representative. `PointSectionsTransport.section_identity`
  fixes the coefficient transport on sections and `tensor` fixes it on pure
  tensors. `pointSectionsH0` is a full concrete composite of these and the
  exact-functor homology comparisons. `PointComparison.completed_normalization`
  fixes completed to gamma inverse (the gamma package retains all finite Roos
  projections); `intrinsic_normalization` fixes the intrinsic bridge using that
  map and the coefficient-equivalence counit. Finally `normalization` identifies
  finite.fibre followed by comparison with intrinsic followed by the same
  `a.point.comparison`, `a.along.comparison`, and ordinary pullback of the finite
  module comparison. The theorem's `PointNormalized` clause pins this exact
  `a.point.comparison` to the actual sections/localization map. Its existing
  transport clause therefore intertwines the specified sf/PBC point transport.
- H2: added the six requested directly used definition owners to the item;
  replaced theorem-only dependencies of the data definition by the requested
  definition owners and `prop-weil-pbc-rational-transport`; cited
  `lem-weil-scalar-extension-composition` in scalar coherence. New helper uses
  additionally cite the coefficient-presentation, point-sections and integral
  completed-pullback owners. The new definitions cite all their dependency ids
  in their statements. No existing dependency node was overwritten.
- H11: replaced the earlier self-reading with the separate reader described above.

Additional dependency declarations read and used: IntegralPullbackCompletedComparison
(`IntegralCompletedComparison.Comparison`, `Complete`, and its projection-normalized
`gamma`); IntegralCoefficientCompletenessTransport, publicly reexported by the
recorded CompletedCoefficientPresentationTransport (`purCoefficientModel`,
`purOrdinaryCoefficientModel`, and their exactness); PointSectionsScalarExtension
(`pointCompletedSections`, `pointModuleRationalization` and their derived functors).
The existing `mapDerivedCategoryHomologyFunctorIso` has direction H0 followed by
F to derived F followed by H0; all three occurrences in pointSectionsH0 use that
published normalization. No arbitrary additional map replaces a completion cone.

Repair searches: rg in LisseCompletedSystemData found `finiteScalarUnit`,
`EtaleOperation.proEtaleUnit` and `IntegralOperation.reconstruction_normalization`.
The existing unit has coefficient universe u+1, while these systems have u;
`finiteScalarUnit` supplies its literal universe-general construction for u without
changing the mathematical unit. rg in AdicHeartIntrinsicFibres and
AdicHeartPullbackFibres found the actual sf/PBC integral fibres and their unique
rational descents. rg in LissePointNormalization and
ClassicalNormalizedTwoFibreData found the required normalized point-square pattern.
The canonical gamma and exact coefficient transports above supply its concrete
bridge; no new existence theorem or postponed helper proof is introduced.

All variables and universes remain explicit, including small coefficient rings
and the independent closure universe. Zero rank, identity field inclusion,
ramified source level zero, empty schemes and all finite point-automorphism
iterates remain covered. Definitions contain full data; only the main theorem
has `sorry`.

Final independent reading: `/root/independent_review` checked the finite-field,
prime, separated finite-type and finite-dimensional coefficient binders; IsFree
at n+1 including rank zero; quotient/limit units and single0/raw fraction maps;
finite/common full faithfulness and the specified-isomorphism lift; ramified
scalar, pullback and mixed equations; common beta and the finite representative
comparison; sf/PBC/classical fibre identity and point-automorphism transport.
No clause or hypothesis discrepancy remained in the repaired packet. The main
JSON signature and eleven definition signatures match the sources verbatim, every
listed declaration belongs to its recorded module, and every dependency exists.

The exact recorded owner of `integralDetailedTransport`,
`def-sfb-integral-completed-coefficient-transport`, is also cited directly in the
data definition. The retained delivered records were compared with current main:
only the item already exists there, and its changes remain confined to `lean`
and the authorized additional `stmt_deps`; the eleven helper nodes are new.

## Compile-size split

`def-zl-classical-raw-lisse-common-restriction-comparison` owns the unchanged
CommonRestrictionComparison and the two finite whiskering definitions previously
in the data module. Its source is BS 6.8.15 and Weil II (1.1.1)d, and its searches
are the retained normalized-comparison searches plus the repair searches above.
The split removes a local per-file timeout after the Mixed beta equation was
added, without adding or dropping any mathematical field. The new node is cited
by the restriction node and directly by the item. The data module now owns only
CommonRestrictionData, including the new beta normalization.

The independent reader also checked the compilation split and identified two metadata defects: the new comparison node named the old data declaration, and the data node still described the moved comparison and whiskering maps. Both records are corrected; the split contains eleven new definition nodes and twelve Lean modules.

Delivery preflight caught an overlong Coherence signature record that included
the following Mixed declaration. The record now ends at the end of the Coherence
signature; the compiled Lean declarations are unchanged.
