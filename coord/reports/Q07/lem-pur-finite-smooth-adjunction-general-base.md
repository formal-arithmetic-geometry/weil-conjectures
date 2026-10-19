## Worker report

Q07 repairs the duplicate-declaration return on immutable head 7b61d8793947.
The packet now contains five modules: the main statement and four definition modules.
The existing section-deformation and gamma-normalization modules and their node records
are imported unchanged; no replacement dependency module is delivered. The new cone
comparison retains its homogeneous normalization and the earlier clause-by-clause reading.

Hypotheses and clauses, read against the node:

- `ell`, `[Fact ell.Prime]`, `k`, `[Field k]`, and `[Fact (ringChar k ≠ ell)]` give exactly
  the prime and arbitrary ground field with the excluded residue characteristic. No finite
  field, algebraic closure, or perfectness assumption is imposed.
- The `X.Over` and `Y.Over` instances and their separated, locally finite type, quasi-compact
  structure morphisms say separated finite type over k. `f.IsOver` says k-morphism.
  The analogous f properties are consequences of these hypotheses, made explicit for the
  existing compactification API; `SmoothOfRelativeDimension d f`, with d natural, says
  smooth of pure nonnegative relative dimension. Compactification and Noetherian witnesses
  occur as conclusions, not as additional hypotheses.
- `coefficient ell n` abbreviates the published `FiniteReduction.Coeff ell n`, two universe
  lifts of ZMod(ell^n). The existential `level` binder of `FiniteSmoothSystem` requires `1 ≤ n`, and every reduction
  requires positive lower index. There is no level-zero assertion.
- `proCategory A T` is the actual fixed-module small pro-etale derived category. `IsCtf`
  uses `Scheme.IsConstructibleProEtaleFixedModuleSheaf` on every cohomology sheaf, an ordered
  cohomological bound, and the published `ProEtale.DerivedCategory.torAmplitudeIn`, which
  quantifies over every pro-etale module sheaf in degree zero. This is not a finite-perfect
  test substitute for finite Tor amplitude.
- `proCompact` is the published open/proper functor on the selected compactification.
  `intrinsic_compact` identifies its canonical coefficient realization with the recorded
  `Scheme.sfIntrinsicCompactSupport`. Both sides are actual functors; this field does not
  introduce an arbitrary compact-support operation.
- `exceptional` is literally `origin A Y ⋙ rightDerivedUpperShriek … f ⋙ comparison A X`,
  i.e. nu_X^* f_A^times Rnu_Y, rather than a functor field. `origin_ctf` and `origin_counit`
  assert the needed ordinary origin and the actual comparison counit isomorphism on the
  entire intrinsic domain. `any_origin` states the identification for every representative
  and every origin isomorphism, using the actual adjunction unit; it does not fix one lift.
- `line` uses the published `affineLinearBaseCoefficient`: the ordered root line shifted
  by 2 in each of d factors, with the coefficient unit at d=0. Thus it presents
  mu_(ell^n) tensor-power d shifted by 2d. `puritySource` and `proSource` include actual
  derived pullback of K and derived tensor with this line. At K=0 the source is zero.
- `root_transport` supplies `RootSiteTransport` at both X and Y for every positive level.
  It identifies the degree-one comparison root line with the recorded actual pro-etale
  kernel of the power map; its inclusion into units is normalized on every root generator
  over every pro-etale test of an etale object. Thus all tensor powers are the actual
  pro-etale Tate twists, with their canonical scalar action.
- `OrientationNormalized` uses `finiteSmoothDiagonalFactor`, the published Rees family and
  `Normalized` comparison at t=1, its specialization at zero, and the Kummer-normalized
  `FiniteRingSectionDeformation.bundleSectionAdjoint`. `normalSectionMap` is the actual
  exceptional base-change/section mate carrying the cone to the conormal vector-bundle
  presentation. Its bundle identification is over X and carries the zero section to zero.
  The displayed equation says the diagonal-specialization composite is alpha followed by
  this bundle integration adjoint. Since the bundle factor is invertible, alpha is precisely
  the specified composite with its inverse. It cannot be independently rescaled.
- `gamma` is derived tensor of alpha inverse followed by `smoothTensorDualityMap`, with
  its actual projection-formula isomorphism. It is not an arbitrary purity isomorphism.
  `sourceAtOriginIso` uses the canonical published derived strong monoidal comparison and
  the derived pullback square. `proGamma` transports this exact gamma through the inverse
  comparison counit. `ordinary_isIso`, `pro_purity`, `ordinary_natural`, `pro_natural`
  assert invertibility, intrinsic preservation and naturality on the stated domains.
- `trace` and `proTrace` are functorial images of gamma followed by the actual respective
  counits. `proCounit` is formed from the normalized open/proper site comparison and the
  ordinary and comparison counits. `trace_transport` explicitly asserts this equality for
  every etale origin. The orientation equation fixes its Kummer/projective-line trace.
- `dimension_zero` identifies gamma with the actual derived etale adjunction coordinates,
  and trace with the graph-normalized compact-support-to-sum comparison followed by the
  etale-sum/pullback counit. `etale_sum` asserts existence of the normalized comparisons;
  the equations hold for every normalized comparison. Smooth dimension zero is etale.
- `proScalar` is the published left adjoint to actual derived restriction of scalars;
  ordinary extension is the recorded `scalarExtension`. `CoefficientLineComparison`
  fixes the root map by its inclusion into G_m (raising to N/M) and fixes the scalar map
  on every scalar/root generator. Its derived isomorphism equals the canonical scalar
  counit followed by this sheaf isomorphism. `tensorPower` uses the normalized scalar unit,
  tensor and shift comparisons, so `pullbackTwistComparison` is exactly lambda.
- `ExceptionalCoefficients.compactSupportMap` and `.mateMap` are reused unchanged.
  Their pro-etale transports are `proCompactCoefficientMap` and `proCoefficientMap`.
  `ordinary_compact` and `pro_compact` assert IsIso. Both `ordinary_counit` and `pro_counit`
  assert the displayed counit-transpose equation and IsIso(c). `pro_natural` is the
  coefficient comparison's naturality, and `ordinary_purity`/`pro_purity` say exactly
  S(gamma_r) followed by c = lambda followed by gamma_m (with IsIso lambda).
- The five kinds of quotient cocycle are equalities of actual morphisms, with the actual
  scalar associators at both X and Y. `compact_cocycle`, `exceptional_cocycle`,
  `pullback_cocycle`, `twist_cocycle`, `purity_cocycle` cover ordinary presentations;
  `pro_compact_cocycle`, `pro_exceptional_cocycle`, `pro_pullback_cocycle`,
  `pro_twist_cocycle`, `pro_purity_cocycle` explicitly cover
  the intrinsic transported maps. All indices use weak inequalities, including identities.
  The ring-hom equality appears only as the construction of the canonical associator.
  `QuotientCocycle` abbreviates the displayed morphism equation with both associators;
  every argument at every use is the actual scalar, support, exceptional, pullback or
  purity-source functor and its canonical comparison. It adds no arbitrary operation.
- `unit_ctf` asserts intrinsic constructibility/finite Tor bounds for the coefficient unit
  and the source and target at that unit. `unit_degree` asserts IsZero of both cohomology
  objects away from -2d. The universal reduction and cocycle equations therefore apply to
  the coefficient-unit case and its successive reductions as required.

Actual dependency interfaces used:

- `Sheaf.Paper.FiniteReductionConstructibility`: `FiniteReduction.Coeff`, `.quotient`,
  `.realize`, and the ordinary bounded-constructible finite-Tor predicate.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude`:
  `ProEtale.DerivedCategory.torAmplitudeIn`.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`: `rightDerivedUpperShriek`,
  `rightDerivedUpperShriekAdjunction`, `dualizingComplex` (and the compactification API).
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport`;
  the imported published pro-etale compact-support framework supplies
  `ProEtale.rightDerivedLowerShriekOfCompactification`, `compactSupportSiteComparison`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `ordinaryFiniteLine`,
  `Scheme.finiteEtaleTateLine`, `finiteEtaleTateOneGenerator`; the vector integration
  modules supply `affineLinearBaseCoefficient` and `singleFunctorObjUnitIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `Scheme.proEtaleRootsOfUnitySheaf` and `proEtaleRootsOfUnityInclusion`, now used
  directly in the normalized comparison of the actual root sheaf.
- `Sheaf.Paper.FiniteSmoothGammaNormalization`: `finiteSmoothDiagonalFactor`,
  `FiniteSmoothCompactSupportComparisons`, `FiniteSmoothComparisonNormalized`,
  `finiteSmoothSumComparison`, `finiteSmoothAdjointCoordinates`.
- `Sheaf.Paper.NoetherianEtaleSectionSpecialization`: `family`, `Normalized`,
  `specialization`, `sectionMap`.
- `Sheaf.Paper.FiniteRingSectionDeformation`: `Geometry`, `bundleRight`,
  `bundleSectionAdjoint` on the actual conormal degree-one vector bundle.
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`: `smoothTensorDualityMap`,
  `isIso_projectionMap_of_finite`; source/target tensor operations are the published ones.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal`:
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`. The actual comparison
  upper/lower-star and `derivedComparisonAdjunction` are reused.
- `Sheaf.Paper.ExceptionalCoefficientComparison`: `.compactSupportMap`, `.mateMap`,
  `.comparisonInverse`, `.tensorIso`, `.unitIso`, `.quotientAssociator`,
  `.CompactSupportCocycle`. `scalarPullbackIso` is the recorded earlier canonical map.
- `Sheaf.Paper.WitnessCompatibility`: `pbcFixedScalarExtension`,
  `pbcComparisonReduction`, `pbcFixedScalarExtensionComp`; `scalarExtensionRepresentative`
  is the ordinary published derived scalar counit.

Other proof-dependency modules are imported without public for stage 3. Their theorems are
part of the proof plan in the ten-step theorem docstring; they are not claimed to occur in
the current sorry proof. No SGA route is used. Sources are the current main-20261015
`sk-thm-smooth-purity`, `sk-prop-sp-orientation` and `sk-lem-sp-reduction`, especially the
compatibility proof's counit-transpose argument and its tensor/orientation normalization.

Edge cases checked by reading types and formulas: zero K has zero pullback/tensor source;
empty schemes require no point/nonempty assumption; d=0 has a zero-fold coefficient unit
and explicit etale counit equations; positive n excludes Z/(ell^0); characteristic ell is
excluded; equal quotient indices and arbitrary intermediate quotients are included;
nonflat Z/(ell^r)→Z/(ell^m) uses derived rather than ordinary scalar extension; independent
choices of etale origins are covered by `any_origin`/`trace_transport`. Site object/morphism
universes remain u+1/u; coefficient modules and all derived Hom presentations use u+1.

Searches: the saved `searches.jsonl` records LeanFinder, Loogle, LeanSearch and Mathlib grep
queries and results. New-node records retain those outputs. LeanSearch and LeanFinder gave
no matching purity/coefficient comparison; Loogle reported unknown identifiers; Mathlib
grep found none. Direct source/DAG searches found the existing ordinary canonical arrows
and the strong monoidal site comparison, which are reused. `SmoothPurityMap` is specialized
to `PurityFiniteSetting`; it does not state arbitrary-field positive Z/ell^n adjunctions.
`blueprint_refs.py search 'smooth purity'` found the broader chain but no generic source and
coefficient transport interface with these actual counit normalizations. No disputed mathematical
statement remains; the omitted-transport correction is documented below.

## New nodes

`def-pur-finite-smooth-canonical-maps` defines the general finite-ring intrinsic domain,
normalized diagonal orientation predicate, ordinary tensor/counit map, and its canonical
site/source/trace transports. It uses existing categories, roots, tensor maps and Rees
geometry rather than introducing new versions. The missing notion is the assembled map
on the original arbitrary-field pro-etale object with its canonical origin counit. Its
source is the current smooth-purity/orientation construction. The searches above and its
record explain why the specialized finite-field purity node is insufficient.

`def-pur-finite-smooth-coefficient-arrows` defines generator-normalized root reduction and
the actual pro-etale transports of b, c, pullback, twist and lambda. It reuses the previously recorded
ordinary b and c; the new work is their shared site/scalar/origin transport, with no
arbitrary scalar or exceptional operation. Source: current sk-lem-sp-reduction and its
compatibilities. Both definition nodes contain no postponed theorem or sorry data.

`def-pur-finite-smooth-canonical-interfaces` now contains only the missing normalized
extended-Rees/relative-Spec comparison. Its six declarations are coneAlgebraIso,
reesConeChart, ReesConeNormalized, reesConeComparison_existsUnique, reesConeComparison,
and reesConeComparison_spec, all in AlgebraicGeometry.Etale.FiniteSmoothPurity.
The comparison is uniquely characterized on every affine chart by sending degree-one
ideal classes to a/t modulo t. The supporting existence/uniqueness theorem retains its
complete natural-language proof and the node explicitly states its characterization.
The earlier fourteen moved declarations and all aliases of their notions are removed.
The original declarations are used directly from their original owning modules.

`def-pur-finite-smooth-adjunction-data` collects the finite-level orientation, intrinsic
adjunction and two-level reduction properties into fully explicit structures. It makes
no existence assertion: the main theorem supplies the structures. It records the generic finite-level data and their properties as a separate
mathematical notion.
It cites the two canonical-map nodes and the existing dimension-zero gamma-normalization
interface. It introduces no operation besides these properties and the zero-fold unit map.

`def-pur-finite-ring-section-data` has existing:true on the unchanged module
Sheaf.Paper.FiniteRingSectionDeformation. It records Geometry, coneBundleIso,
coneBundleIso_spec, bundleRight, bundleAdjoint and bundleSectionAdjoint under
AlgebraicGeometry.Etale.FiniteRingSectionDeformation. Geometry is a proposition collecting
the actual Rees geometry, rank and regularity requirements, rather than their existence.
The relative-Spec map is the original symmetric-algebra comparison; the two adjuncts are
formed from the original integration and zero-section inverse image. coneBundleIso_spec
is the original supporting specification. The sources are current sk-thm-dnc and the
normal-bundle factor of sk-prop-sp-orientation. Its signature and every field were read
against the original module. Empty schemes, rank zero and the zero coefficient ring
introduce no extra restriction.

`def-pur-finite-smooth-comparison-coordinates` has existing:true on the unchanged module
Sheaf.Paper.FiniteSmoothGammaNormalization. It records finiteSmoothPullbackNoetherian,
FiniteSmoothCompactSupportComparisons, FiniteSmoothComparisonNormalized,
finiteSmoothSumComparison, finiteSmoothAdjointCoordinates, finiteSmoothOmegaCoordinates,
finiteSmoothSectionCoordinates and finiteSmoothDiagonalFactor, all under
AlgebraicGeometry.Etale. The family type and graph/homotopy normalization, the actual
adjoint-uniqueness coordinates and the pulled-back exceptional base-change diagonal map
are recorded as definitions, with exactly their general coefficient rings and scheme
hypotheses. This does not assert the owning gamma-normalization theorem or existence of
a comparison family. Its normalized predicate is weaker data than the existing
EtaleCompactSupportNormalization record because it does not include that record's
refinement and base-change laws. Hence that different record cannot replace this interface.
The source is the current three-factor purity formula and its d=0 sum-counit coordinates.

Fresh LeanSearch and LeanFinder queries for each notion, and the Mathlib exact-name grep,
are stored verbatim from searches.jsonl in both records. Direct source and DAG searches
found these exact declarations in the original modules and their owning theorem nodes,
but no definition-node ownership records. blueprint_refs.py returned zero matches for
both ownership queries and None for this item's blueprint ancestor. The new nodes have
exactly the permitted definition-node fields, no module file, and explicit existing:true.

The citations in all three consumer statements were updated consistently with their
stmt_deps. The previous correction archive remains a verbatim copy of current main's
statement, statement dependencies, proof and proof dependencies. The complete citer audit
is still exactly the same three nodes, all holds:true. The prior theorem signature,
Rees comparison uniqueness, every reduction and cocycle equation, and the d=0 and -2d
clauses are byte-identical. The self-check hashes all five Lean sources against the saved
packet and checks the two new primary signatures verbatim against their unchanged owners.

## Second reading by Q07

Fresh self-check of the node and all five delivered modules, following the dispatcher's
instruction to finish the required self-check without starting another agent. This is not represented
as an independent worker review; the maintainer supplies the independent reading.

The returned H3 fault is removed: gamma has the full Lf^*K tensor root-line source, the
field characteristic condition is present, and n is positive. The H5 operations are actual
comparison, exceptional and derived scalar functors. Counit-transpose, IsIso, gamma
compatibility, and all five quotient cocycles are written as morphism equations. The
orientation is constrained by the diagonal/Rees/Kummer equation; d=0 and degree -2d are
explicit. Pro-etale origin and compact-support transport are displayed, including arbitrary
origins and actual counits. The H8 coefficient/datum declarations now have source/blueprint
docstrings, and the main theorem has a ten-step natural-language proof. The new uniqueness
helper has its source proof in its docstring; coneBundleIso_spec is imported from its
original owner. The report separates
actual definitions used from proof-dependency imports. During this reading the unnecessary
site tensorator datum was removed in favor of the existing canonical tensor comparison,
explicit constructibility at the coefficient unit was added to the vanishing clause, pro-etale pullback and twist cocycles were written out separately, and the normalized
comparison with the actual pro-etale roots-of-unity sheaf was added explicitly.

The existing scalar-extension universe diagnosis fixed the existing essentially-small instance
explicitly as `essentiallySmallSelf.{0, u, u + 1}`. This avoids an unconstrained maximum
universe in class inference; it imposes no equality between site object and morphism
universes and adds no mathematical hypothesis. The added nodes have no dependency path
back to the item.


## Repair of duplicate declaration ownership

The independent return lists six names owned by Sheaf.Paper.FiniteRingSectionDeformation:
Geometry, coneBundleIso, coneBundleIso_spec, bundleRight, bundleAdjoint, and
bundleSectionAdjoint in AlgebraicGeometry.Etale.FiniteRingSectionDeformation.
It also lists eight names owned by Sheaf.Paper.FiniteSmoothGammaNormalization:
finiteSmoothPullbackNoetherian, FiniteSmoothCompactSupportComparisons,
FiniteSmoothComparisonNormalized, finiteSmoothSumComparison,
finiteSmoothAdjointCoordinates, finiteSmoothOmegaCoordinates,
finiteSmoothSectionCoordinates, and finiteSmoothDiagonalFactor in AlgebraicGeometry.Etale.
All fourteen definitions/statements were removed from the new module, without renaming
or replacing them. The new namespace aliases of those notions were removed as well.
FiniteSmoothPurityMaps publicly imports both existing owner modules and calls the
section-deformation constructions by their original qualified names. The existing
Etale comparison names resolve directly from that original namespace.

The two previously delivered replacement modules and their dependency node copies were
removed from the packet. Their signatures were compared with current base sources and
confirmed unchanged apart from the previous ownership move. scompile.py --source confirmed
that the live sources still own the declarations listed in the return. The new cone node
now describes only its new homogeneous comparison and the canonical-maps and datum nodes
cite the definition ownership records for their reused notions. A direct dependency traversal confirmed
neither owner has a path back to this item. The main theorem signature and every geometric,
purity, counit, coefficient, cocycle and degree clause are unchanged by this repair.

## Repair of the returned normalization fault

The saved OrientationNormalized still existentially quantified a bundle isomorphism e.
It now uses the fixed composite reesConeComparison followed by the original
FiniteRingSectionDeformation.coneBundleIso. The only existential bundle-related binder
is a proof of the cartesian square of this specified morphism. normalSectionMap has no
isomorphism parameter: it uses that same composite. Its zero-section compatibility is
computed from reesConeComparison_spec and the original coneBundleIso_spec. Thus neither
an unspecified Rees/graded comparison nor an automorphism preserving only zero and the
projection can change alpha. The homogeneous normalization rules out rescaling.

The comparison's existence/uniqueness proof is postponed as a named theorem supporting
the definition, with its source and a complete proof in the docstring and its precise
characterization in the owning DAG node. Its defining data is selected from a unique
characterization, not a mere existence statement. The imported coneBundleIso_spec retains its original source proof in its owning module. The main purity theorem is still postponed. All other data
are explicit constructions; no axiom or mathematical assumption has been added.

Fresh edge-case reading: the zero ideal and rank zero give the base cone; the unit ideal
and empty centre give the empty cone. On every affine chart the homogeneous formula fixes
constants by the structural map and fixes all ideal generators, so it uniquely determines
all degrees. Localization preserves the formula. The repaired orientation therefore uses
the canonical associated-graded/vector-bundle identification in all these cases. The
previously approved arbitrary-field, positive-level, counit, reduction, cocycle and degree
clauses are unchanged. The omitted transport is corrected as recorded below; no SGA route is used.

Searches repeated for this repair: LeanFinder with the extended-Rees/associated-graded
canonical-comparison query returned eight unrelated Proj chart declarations; Loogle
`Ideal.extendedReesAlgebra, CategoryTheory.Iso` returned an unknown-identifier result;
Mathlib AlgebraicGeometry grep `reesConeComparison|ReesConeNormalized|coneBundleIso`
returned no matches. Direct rg in the named upstream, shared Lean and DAG directories
found no existing normalized comparison. blueprint_refs.py search `Rees cone comparison`
returned zero nodes. The existing purityNormalCone_comparison was read: it asserts only
existence with projection and augmentation compatibility, which does not determine the
comparison. It is not used to choose the new data. Raw service results are retained in
the new node's mathlib_searches.

## Statement corrected

The old orientation composite used the normalized specialization on the actual Rees zero
fibre, but its next factor uses the relative-Spec normal bundle. The intermediate map was
not specified, so the recorded specialization and integration interfaces could not be
composed without supplying a map. An existential bundle identification did not encode
the source's specified relative-Spec comparison. The corrected text now
specifies the homogeneous Rees/associated-graded map (a/t^j maps to the degree-j class of a)
and then relative Spec of the symmetric-algebra comparison. This follows the source's
normal-bundle construction and adds no hypothesis. The previous intended conclusions
and target uses are preserved. The section-deformation geometry and its specification
are included as proof prerequisites, and the existing plain constructions are reused from their original owners. The verbatim
old statement, dependency lists and proof are archived in
`statement_change`.
The complete direct-citer audit found three citers; all still hold:

- `lem-pur-condensed-normalized-witness`: the normalized finite diagonal/DNC maps used in
  its reconstruction are unchanged.
- `lem-pur-condensed-tate-integral-tower`: the finite gamma maps, reductions, quotient
  cocycle and degree at the coefficient unit are unchanged.
- `nt-target-smooth-purity-qbar`: its arbitrary-field finite purity and normalized
  coefficient-compatibility inputs are unchanged.

## Validation

All five delivered modules passed the prescribed scompile.py server compilation on
2026-10-18 without errors or unexpected warnings. The supporting cone comparison compiled
in 4.5 seconds, purity maps in 7.4 seconds, coefficient arrows in 22.5 seconds, adjunction
data in 14.4 seconds, and the main statement in 9.3 seconds. The unchanged original owner
modules compiled as dependencies. The 60-second per-file limit was retained.

The initial saved-packet dry run encountered a missing RationalizationKaroubi object and
then an unchanged-dependency timeout during server confirmation. The repaired packet's
first overlay pass encountered a missing AffineSpaceLinearTraceInvariance object; its
server confirmation compiled all five files successfully. No live source, launcher script,
compiler setting or limit was edited.

The self-check verified all five exact primary signatures, explicit variables/universes,
line lengths, the six-declaration ownership list, removal of all fourteen returned names
and their aliases, unchanged main theorem signature, the canonical orientation equation,
and every coefficient/cocycle/degree clause. The correction's archived old statement,
dependency lists and proof match the current base verbatim, and its three-citer audit is
exhaustive. The two original owner modules and their theorem-node records are not in this packet.


## Repair of H2 on immutable head 68ed1d7d638a

The saved packet was tested first with deliver2.py --no-push: commit 3496ecf7bb passed
compilation and preflight after automatic server confirmation. This does not discharge
the independent reader's H2 finding, which is repaired with definition ownership records
while retaining all five Lean files unchanged.
The two owning theorem nodes stay in the main item's proof_deps. The statement dependencies
of the item, canonical-maps and adjunction-data now cite the following definitions instead.
No existing definition was moved, renamed, copied or restated in Lean.

## Second reading by Q07 — H2 ownership repair

The fresh self-check compared every delivered Lean file's SHA256 against the saved packet:
all five are identical. Both new primary lean.statement strings equal the full original
source signatures up to where or :=. All fourteen reused declaration names remain in their
original two modules. The item, canonical-maps and adjunction-data each cite both new
definition nodes and neither owning theorem as a statement dependency. The main item's
proof_deps retain both original theorems. Every bracketed DAG citation in these three
statements is present in stmt_deps; each new node's cited IDs equal its stmt_deps exactly.
All seven JSON files use indent 1, ensure_ascii false and a final newline. The existing
statement correction's old_statement, old_stmt_deps, old_proof and old_proof_deps still
match current main verbatim. The independent maintainer remains the independent reviewer;
this section records the worker's own second reading, as the dispatcher requires.

## Resumed repair validation — 2026-10-18

The required first dry run compiled all five saved Lean modules and checked all fourteen
existing declarations without errors or unexpected warnings. Preflight rejected only the
report layout: the two existing-definition nodes were described under a second New nodes
heading, while the checker reads the first section. Their descriptions are now consolidated
under one New nodes heading. The self-check also found and replaced one remaining theorem
citation inside a multi-citation bracket in the main statement with
def-pur-finite-ring-section-data. The theorem remains in proof_deps. This is a citation
repair only; the mathematical statement and all five Lean source files are unchanged.

The fresh self-check verified the five saved SHA256 hashes, both original primary
signatures, all three consumers' definition dependencies, the two retained theorem proof
dependencies, the correction archive against current main, all three direct citers,
and the required JSON serialization. Both original owner modules retain their declarations.
