# Target migration, 2026-10-14

The human decided on 2026-10-12 to follow the corrected upstream statements. This sync
adopts `slopmaster2` commit `2104a988ee9fbee4de847237b493e3bd361d4ebb`, including PR 1413
(`46dc75fcf`) and its reviewer fix (`84babb37e`). `isIso_baseChange_of_isProper` is the
bounded-below abelian-sheaf statement with torsion cohomology, Stacks 0DDE;
`isIso_baseChange_of_isProper_of_isAddTorsion_ring` is the torsion-ring form, and
`isIso_baseChange_of_isProper_of_torsionHomology` retains the former module statement.

## Targets selected from the upstream structure

1. `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` — `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`; node `lemma-weil-pbc-p1-exchange-geometric-stalk`.
2. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`; node `prop-weil-pbc-algebraically-closed-extension`.
3. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`; node `lemma-weil-pbc-curve-separably-closed-passage`.

4. `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject` — `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`; node `lem-weil-pbc-cohomology-filtered-colimit`.
5. `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` — `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity`; node `lem-weil-pbc-etale-section-continuity`.
6. `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing` — `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`; node `thm-weil-pbc-henselian-idempotent-lifting`.

These keep the upstream geometric-stalk and field-extension proof boundaries. The reduction
is now proved in `BaseChangeTheorems.Reduction`; injective acyclicity for arbitrary module
coefficients is now deduced from prime quotient coefficients in `BaseChangeTheorems.Coefficients`.
Both former targets leave Challenge. The two duplicated property definitions also leave
Challenge; only upstream defines each notion. All module torsion hypotheses use upstream's
`Scheme.IsTorsionModuleSheaf`, while `Scheme.IsTorsionSheaf` is for abelian sheaves.

## Current compiled closure audit

The user authorized following corrected upstream statements on 2026-10-14, including
substantive changes with adaptations of local users. The six target contracts listed above
are the current upstream boundaries; no local target statement was weakened to obtain a proof.

The completed pure-upstream server build at
`sidebuild-base/2104a988ee9fbee4de847237b493e3bd361d4ebb` reports success for 11,623 jobs.
The exact-tip audit imports that compiled library, with the unchanged shared packages, and
runs within the existing 60-second single-file limit. Both main theorems have precisely
`[propext, sorryAx, Classical.choice, Quot.sound]`. A complete export contains 65,932
project declarations. Traversing project references in declaration types and values reaches
5,699 declarations from the abelian main theorem and 5,594 from its torsion-ring form.
Each closure contains exactly the same six own-sorry owners, namely the six targets listed
above. The full source map and closure traversals are retained in `~/cc1/upsync-audit/`.

Upstream has proved `hasTorsionBaseChange_of_projectiveLine_of_isProper` and
`hasTorsionBaseChange_of_hasInjectiveAcyclicity`, both own-sorry owners in the old main
closure. The modules `BaseChangeTheorems.ProjectiveLine` and
`BaseChangeTheorems.BaseChangeProperty` now have zero own-sorry records. Their proofs
still depend transitively on the six remaining upstream gaps; this audit does not claim
the proper-base-change main theorem is sorry-free.

This source audit uses pure upstream so that a landed local proof resting on unfinished
helpers cannot hide an upstream target. The routine separately requires the combined
side copy's complete default-target build, independent compilation of every local or
retained source file within 60 seconds, name-clash checks, and all current target/definition
hash checks before changing the live base.

## Historical compiled closure audit at ffb7b9060

At 2026-10-13 03:25 +08, the completed pure-upstream server side build
`base-46dc75fcf` was audited again through `sidebuild-base/current`. This supplies exact evidence for the synced
tip: `git diff 46dc75fcf ffb7b9060` changes only `EtaleCohomology/Purity/Smooth/Deformation.lean`,
and that module is absent from the Proper source import closure (1,931 modules).
A single-file `lake env lean` invocation with a 60-second timeout printed both main axioms,
then traversed every declaration referenced by their types or values (opaque values included).
Both main statements have precisely `[propext, sorryAx, Classical.choice, Quot.sound]`.
The abelian statement reaches 88,867 declarations; the torsion-ring form reaches 88,747.
Each closure contains exactly the same six declarations with their own `sorryAx`:

1. `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` — `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`.
2. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`.
3. `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed` — `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`.
4. `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject` — `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`.
5. `AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit` — `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity`.
6. `AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing` — `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale`.

The three additional declarations are exposed by the now-proved reduction and its filtered
colimit/locality ingredients. They are selected as targets alongside the retained three,
using upstream's existing lemma boundaries. `Challenge` contains exactly six named theorem
sorries. The audit was run on pure upstream, because our landed proofs can replace a target
sorry by a proof that still rests on unfinished local helper lemmas.

`shiftedHomFunctor`, `finalObject`, and `unitComparison` must be restated verbatim only in
Challenge: each is defined in a module that also declares one of its targets, so importing
that module there would clash. These are comparator specifications; the compiled library
uses only upstream's definitions. The target checker also compares their types and bodies, ignoring only names of theorem-proof
constants (Lean caches such proof terms under whichever declaration it elaborates first).
A standalone single-file check against the completed upstream build confirmed all six target
type/universe hashes and all three definition type/body hashes agree; both specification
modules compile separately within the 60-second limit.

## Correction, 2026-10-15 (launcher, with the human)

The sync of 2026-10-15 made `TargetsCheck` import the whole module `BaseChangeTheorems.Proper`. That put
the route by which Proper proves the main theorems into the targets' closure, three sorried modules no
target declaration needs (`Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful`,
`...ModN`, and `WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension`). The import of our
`Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange` in Proper was added by that sync; upstream's Proper
uses its own sorry-free `BaseChange.DerivedUnbounded`. The targets did not change: `TargetsCheck` imports
again only the modules of the six target declarations of `Challenge`.


## Upstream 19b471a73, 2026-10-16: batch 3 and over-category migration

The human's standing instruction is to follow upstream target statements. This sync adopts
`19b471a73f2f1ddc4bef81de9bfb45dcd963e5a4` from base
`2104a988ee9fbee4de847237b493e3bd361d4ebb`.

The six batch-1 declarations in `Challenge.lean` have unchanged upstream statement text.
Their comparator remains active in `tools/target_types.sh check`; the batch-1 imports and both
batch-2 target modules remain in `TargetsCheck.lean`.

Both pro-etale Proper batch-2 statements now use `X Y X' Y' : Over (Spec (.of k))`,
structural hypotheses on `X.hom`, and morphisms in that over category. The field `k` is
inferred, the bounded-constructible operations take those bundled morphisms directly, and
properness is `IsProper f.left`. These replace the prior `Scheme` objects with `Scheme.Over`
and `Hom.IsOver` instances and explicit `k` argument. The local pointwise proofs are retained:
canonical `Scheme.Hom.asOver` bundles their morphisms and the cartesian square is transported
through `Over.forget`. This changes the representation of the same schemes, morphisms and
exchange map; no hypothesis or conclusion is weakened. The two natural-transformation
assembly proofs keep upstream's new signatures.

Batch 3 adds `WeilConjectures.SmoothPurity.Defs` to `TargetsCheck.lean` and records it in
`coord/batch3-targets.txt`. Its target is upstream's unchanged sorried `@[no_expose]`
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`, a chosen isomorphism from the
exceptional inverse image of the constant Qbar coefficient object to its shifted Tate twist.

The finite-coefficient module renames are recorded in `coord/upstream-migrations.json`.
Local proofs from changed old paths are moved to the canonical renamed upstream files;
old retained paths forward their imports. The canonical upstream `Mod.freeFunctor` is reused.
The existing local module proofs and their helper statements are preserved during the merge.

The retained all-morphisms amplitude theorem also exports its bound without a quasi-compactness assumption; the new upstream global class alone only requires that field for quasi-compact targets.

The batch-2 smooth-base-change targets also reuse upstream's declarations in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Smooth`. The abelian target now has
upstream's `orderInvertibleOnHomology f K` hypothesis and conclusion for `Etale.baseChange`.
Its previous stalkwise hypothesis is precisely the fields of that predicate; projecting them
and using `baseChange_eq_derivedBaseChangeMapPlus` transfers the existing proof. The ring target
has the same statement, and its existing proof is moved into the canonical declaration.
The two original `Sheaf.Targets` imports forward to the canonical module.

819 local proof modules have exactly the declaration bodies now present upstream (comments,
imports and whitespace excluded in a conservative comparison). Their local paths forward to
upstream, preserving their public imports. The proofs and declarations remain in the library
under the same names; the audit is in `upstream-sync/runs/19b471a73/canonical-proof-preservation.json`.

Further nonidentical copies reuse the canonical upstream declarations: the arbitrary-ring
constant-module equivalence retains our `Ring` generality; the normalization comparison keeps
our closed proof in upstream's formerly sorried declaration; the finite-locally-constant
predicate is shared with the canonical finite-set module. Quasi-coherent extension and
biproduct results use upstream's declarations, with the alternate tilde proof retained.
Torsion filtrations now use upstream's `PNat.DvdOrder`. The locally closed scheme record is
an abbreviation of `Scheme.Stratification`: both already carry the same constructibility
field through `Topology.Stratification`, so removing the repeated witness does not weaken it.
The old acyclic-tensor sheaf predicate is retained verbatim as
`CochainComplex.IsAcyclicTensorKFlat` (and all its clients follow that name); upstream's
`IsKFlat` is the separate generic predicate with additional ambient typeclass requirements.
The stronger sheaf-structure conjunction remains available as
`sheaves_algebraicStructures_objects_with_finiteProducts`.
The exact-postcomposition and derived-mate comparison proofs use the new comparison unit
and upstream's explicit `ViaRightDerived` comparison respectively, with unchanged conclusions.

A source-wide duplicate audit also moved the closed proofs for finite étale descent,
finite hypercover descent and refinements, additive scalar base change, quasi-coherent
annihilators, common covering refinements, split tower envelopes, derived tower limits,
and the Sylow module filtration into their canonical upstream modules. Their statements
are unchanged. Canonical upstream proofs replace the equivalent exported copies for the
other 21 module pairs. The two unique compatibility lemmas (finite-cover constructibility
and zero-dimensional finiteness) are retained alongside those canonical declarations.

## Compiled audit at the exact 19b471a73 tip

The full pure-upstream side build `upsync3-pure` completed successfully (12,550 jobs).
Its retained tree is `upstream-sync/pure-upstream/19b471a73f2f1ddc4bef81de9bfb45dcd963e5a4`;
`compiled-evidence.json` records the forwarding wrapper's result. The complete compiled
source map contains 74,804 declarations and was extracted in 28.3 seconds. Project-reference
closures of the two etale proper-base-change main statements contain 6,002 and 5,903
project declarations, respectively. Both now reach exactly three own-sorry owners:
`exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`,
`IsCurve.bijective_cohomologyMap_of_isAlgClosed`, and
`Scheme.bijective_appTop_idempotent_of_henselianRing` (with their full namespaces as above).
The other three batch-1 contracts have upstream proofs; all six contracts remain checked.

The new `CondensedRing.smoothPurityIso` declaration is present as upstream's sorried data
and its project-reference closure contains 4,691 declarations and 17 own-sorry owners.
The two etale main statements and this data declaration each report precisely
`[propext, sorryAx, Classical.choice, Quot.sound]`. Complete maps, closure owner lists,
and the standalone axiom output are retained in
`upstream-sync/runs/19b471a73/audit/`. This supersedes the older-tip closure counts above.

Module-cohomology callers use `(X := ...)` for the canonical enough-injectives instance's
implicit scheme parameter. These are proof-body argument adaptations with unchanged statements.

The proved coefficient-dependent triangulated-closure instance is retained unchanged as
`isTriangulated_boundedConstructible_of_serre`, with its node and clients redirected.
Upstream's distinct, sorried noetherian-only `isTriangulated_boundedConstructible` instance
is retained under its canonical name for new upstream rationalization statements. Its
pre-existing upstream proof obligation is not treated as a newly proved local result.
The proved Serre instance has higher priority when its hypotheses are available.
Generic K-flat composition declarations now reuse their canonical upstream module.

The exact-postcomposition comparison is now upstream's direct comparison. The
retained comparison through the intermediate right-derived functor is proved
equal to it; the affine unit and open-square mate proofs use this equality or
the new direct unit, with their original conclusions. Bundling a scheme over the
base also carries its local finite type, quasi-compactness and separatedness
instances through `OverSquare`. The lattice proof's private pullback system and
its closed helper lemmas are retained in `ContinuousLissePullbackSystem`, so the
system and the stratified-lattice argument can each pass the independent
60-second check.

The shared closed-fiber nonemptiness lemma keeps its original name and proof in
`WeilConjectures.AlgebraicGeometry.HenselianClosedFiberNonempty`, imported by
both henselian modules. This avoids a cycle through `HenselianClopenRestriction`.
The lattice calculation on one stratum is retained in a generic private helper,
`ContinuousLisseStratumDescent`; the public lattice theorem applies the same
finite étale descent theorem and keeps its original conclusion.

The retained continuous-lisse lattice proof is factored through private generic pullback and stratum-descent helpers. Coefficient specialization passes the integral/rational coefficient objects explicitly, avoiding deep kernel normalization of inferred expressions; the public statement and proof calculations are preserved. The integral residue-exchange proof uses a local 400k elaboration budget (14.1 seconds standalone).

The lattice proof also uses the canonical pullback objects directly in place of an unnecessary existential repackaging. Together with explicit coefficient specialization, the complete unchanged public theorem checks in 2.7 seconds under the normal budget; the private generic calculations remain checked separately.

Further retained clients follow the pair-shaped constructibility witness (Gabber, 32.8 seconds). The integral exchange counit is retyped with the unbundled underlying morphism before identity simplification and uses explicit coefficient arguments (26.4 seconds). The integral-stratum proof retains its coefficient transport calculations in a generic private helper (5.5 seconds) and explicitly specializes them in the unchanged public theorem (4.0 seconds).

The unchanged continuous-exchange integral-model proof also uses a local 400k elaboration budget to check the two bundled coefficient arrows; standalone 10.2 seconds.

The finite discrete exchange comparison retains its complete statement and bounded-devissage proof. The constant-module equivalence now explicitly supplies the required size-shrunk module limits; explicit bundled schemes and morphisms prevent elaboration of the new Over-category exchange from unfolding the coefficient category. Its single-file check takes 5.1 seconds at the normal heartbeat budget. ContinuousExchangeIntegralModel keeps its original proof with a local 400,000-heartbeat elaboration budget (10.2 seconds).

The retained free-sheaf cohomology and shifted-Hom proofs are split into canonical helper modules FreeSheafCohomology and FreeSheafShiftedHom to satisfy the unchanged 60-second independent-file gate. The shifted-Hom calculation is proved generically for an abelian category, then specialized, with its original calculation and naturality proof retained. The public batch-1 target and the comparator definitions keep their exact types and bodies. The curve and free-sheaf filtered-colimit clients reuse the canonical H_map_isColimit_of_isFiltered_of_large theorem, preserving the required index universes.

The retained geometric regular-coefficient proof now shares
`condensedFieldCoefficientRingObj E`, an abbreviation for the same continuous
condensed coefficient object with its normed-field instances fixed once. This
avoids expensive kernel conversion between independently abstracted instance
proofs in the pullback realization and its conjugation calculation. All objects,
morphisms, statements and proof calculations are definitionally unchanged; the
complete proof checks in 6.6 seconds at the ordinary heartbeat budget. Two further
clients publicly import the canonical derived LowerShriek / Coefficients modules
to retain access to cohomology and DerivedCategoryModule after the import refactor.

Fresh worker landings are preserved during the preparation refresh. Their new
bounded-below scalar-basis theorem for coefficient pushforward is retained under
its distinct name with the complete proof and helper modules. The upstream
ambient unbounded instance keeps its upstream statement and existing sorry;
the bounded theorem does not replace or weaken it. Legacy finite-coefficient
reexports and compatibility names reuse the canonical declarations. The WeilSheaf
finiteness proof selects the canonical over-category identity instance with the
same local priority already used by the upstream consumers (single check 6.0 s).

The continuous-field presentation helpers also name the unchanged unit-section evaluation as `condensedFieldContinuousCoefficientMap`. The geometric coefficient and regular-module scalar formulas use that definitionally equal expression, keeping their complete conclusions and closed proofs while avoiding repeated expansion of inverse-image coefficient instances in the kernel. Fresh worker uniqueness, factorization, and scalar proofs remain present. Individual checks: presentation matrix 2.0 s, geometric coefficient 7.0 s, regular scalars 2.7 s.
The compatible-evaluation and presentation-corank callers use the same definitionally equal coefficient object and unit-section evaluation. Their original calculations are unchanged; individual checks take 4.4 s and 3.1 s.

Fresh worker proof adaptations: the restricted residue regular coefficient pullback isomorphism is factored through a generic coefficient-ring morphism, preserving its explicit ordinary-unit and derived-single comparison; its public specialization is unchanged (16.4 s). The common finite-discrete encoding explicitly supplies the mixed-size ModuleCat limits instance (3.0 s). Six new bounded-constructible pull/push preservation calls in the mate proof now use the same morphism over Spec k as the surrounding operations (26.2 s).
The finite-coproduct lattice construction retains its explicit biproduct/unit isomorphism as a Nonempty lemma and its complete calculation in a generic coefficient-morphism lemma. The public integral lattice theorem has the unchanged hypotheses and conclusion and specializes that calculation. This avoids kernel conversion timeouts in cached data proofs; the whole file checks in 4.3 s at the normal heartbeat limit.
The mate proof also simplifies the explicit `OverClass.asOver_left` and `asOverHom_left` projections (27.5 s against the current full-build artifacts). The etale-lattice proof separates compactness for an arbitrary neighborhood property from the finite-family coefficient construction. This keeps the exact public statement and all original calculations, while avoiding expansion of the concrete finite subcover inside module categories; the entire file checks in 2.7 s.

The left coefficient-exchange adjunct proof now performs its composition algebra
over abstract functors. The pullback-cube statement uses the definition
`CategoryTheory.coefficientPullbackCube`, which expands to the same equality;
its original unresolved proof remains unresolved. Both adjunct equations are
derived from the existing closed square-exchange formula. This avoids expensive
implicit conversions between composite functor objects after the Over refactor.
The public left-adjunct statement and all closed proofs are retained.

The two Proper proofs explicitly transport finite-type, quasi-compact and
separated hypotheses from the hom of each bundled object to the structure map
of its underlying scheme before reusing the pointwise proofs. Their statements
remain exactly the upstream statements.

## Preserve newer worker proofs during the final refresh

The disposable snapshot at live commit 33c3f9570a8209a5ec9d70582bf85859fd63e972
contains the completed pullback cube proof fa26c5d77a. Its closed helpers and proof
are retained, with explicit Over parameters and the same coefficient cube equality.
The residue tensor presentation now lives in the worker's new presentation module;
the existing regular-module comparison proof is moved there and reused.

Two retained source modules now import the canonical finite-coefficient TorAmplitude
and GlobalSections modules. The field evaluation linearity theorem retains its
original public statement and proof; its scalar-action calculation is factored
through general monoidal-functor lemmas to avoid expensive concrete conversions.
The base-change source image descent proof is split into sheaf coherence, stalk
coherence and the original descent theorem. All arguments are retained; each part
passes its independent 60-second check (28.8, 45.9 and 29.7 seconds respectively).

Independent 60-second checks: retained the Cartesian inverse-comparison and chart-adjunction proofs in separate modules; split affine tensor augmentation, tensor, homology, and coordinate comparisons; split the proved smooth-base-change survival arguments into basic, limit, closed/open and final modules. All mathematical statements and proof arguments are retained. The public survival module forwards to these proof modules.

New worker scalar-fiber evaluation retains its statement and scalar/conjugation proof, with fully specified geometric evaluation functors (12.6 s). The coordinate factorization uses the associativity of its three unchanged isomorphisms explicitly after splitting the coordinate construction (42.6 s).
