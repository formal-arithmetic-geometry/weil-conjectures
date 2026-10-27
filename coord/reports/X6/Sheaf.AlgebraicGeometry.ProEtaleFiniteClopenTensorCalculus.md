## What changed

Prove the finite-clopen tensor and scalar calculus from the existing normalized tensor,
K-flat descent and scalar comparison declarations. Preserve the already proved derived
calculus and its private helper interfaces.

Add a proved normalization extension on the K-flat full subcategory. The given descent
normalizes only flat-term K-flat pairs, while the item quantifies over arbitrary K-flat
pairs. Flat-term K-flat resolutions, the native simultaneous tensor comparison and
naturality transport this square to every K-flat pair.

Add a proved conversion of the scalar representative square from cochain localization
to the homotopy quotient. The proof expands the canonical quotient factors and counits,
uses naturality, and cancels two isomorphisms. The main scalar proof assembles sections,
this representative formula, model properties, unit normalization and compositor coherence.

The module category, coefficient restriction, module restriction and standard derived
restriction use the canonical tensor and monoidal aliases of the same data. Native monoidal and symmetry
structures, pure tensors and inverse tensorators share the existing canonical clopen
interfaces to avoid repeatedly unfolding large but definitionally equal structures. The change record below
records these definition bodies and the instance reducibility annotation. No theorem
signature or target is changed. No adopted source-library file is changed.

Validation: all twenty delivered Lean modules and all required unchanged direct
importers compile. The item and extracted derived calculus pass in 37.5 s and
23.4 s (`23005eaeeff5f1aa1a223013`). The final support and strict-tower facade
pass in 20.5 s and 32.1 s. The decomposition support module uses default
transparency, and its facade passes in 38.7 s (`3941c0bc53df8155cc83d275`).
The complete eleven-importer check passes (`65d75f756021f3d643b01ae1`).
The augmented support/facade and direct importer pass together
(`30f2ba22f254f954f7ce86e1`); the facade takes 13.7 s. All nine
unchanged validation-only copies are removed. No profiler option or temporary
probe is delivered. Original compiler errors requiring each adaptation and the
remaining timing repairs are documented below.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_tensor_calculus`.
- `AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.finite_clopen_scalar_calculus`.

New holes added: none. There are zero `sorry`s in the eleven proof modules and in the
adapted strict-tower, constructibility and completeness consumers.
The additional linting-only adaptation of `Sheaf.Paper.ClopenCompletedOperationTowers`
retains its one original hole unchanged:
`WeilConjectures.ClopenCompletedOperations.clopen_completed_operation_towers`
(node `lem-pur-clopen-completed-operation-towers`). This is not a new hole.
The proof-only adaptation of `Sheaf.Paper.FiniteClopenDerivedDecomposition` retains
its one current original hole unchanged (node
`lem-pur-finite-clopen-derived-decomposition`):
`WeilConjectures.PurityFiniteSetting.finiteClopen_constructible_equivalences`.
The latest shared source proves `finiteClopen_finite_restriction_identification`;
that proof and its support helpers are preserved verbatim in this packet.
The augmented-descent compilation split retains its one original hole unchanged
in `Sheaf.Paper.AugmentedIntegralDescentCore`:
`WeilConjectures.PurityFiniteSetting.augmentedIntegralReductionComparison`
(node `lem-pur-augmented-integral-descent-core`).

The instance-only adaptation of `Sheaf.Paper.ClopenRoosIntegralDescent` retains five
original holes unchanged (node `lem-pur-clopen-roos-integral-descent`):

- `WeilConjectures.PurityFiniteSetting.finiteClopen_strict_tower_equivalence`.
- `WeilConjectures.PurityFiniteSetting.finiteClopen_resolution_reduction`.
- `WeilConjectures.PurityFiniteSetting.finiteClopen_completed_tensor_unit`.
- `WeilConjectures.PurityFiniteSetting.finiteClopen_strict_tensor_reductions`.
- `WeilConjectures.PurityFiniteSetting.finiteClopen_integral_scalar_extension`.

The compact-support adaptation retains its one original hole unchanged:
`WeilConjectures.PurityFiniteSetting.clopenSupport_independent`
(node `lem-pur-clopen-common-compact-support`). None of these nine retained consumer
holes is added by this delivery.

All newly stated auxiliary theorems are proved, including the extracted existing proofs. The existing imported descent declarations remain the intended next proof dependencies; this delivery does not claim to close their holes.

## No longer needed

No existing module or node is withdrawn. Every original proof dependency remains
necessary in the new transitive dependency closure; none is pruned. The existing internal
coordinate and tuple implementation declarations move to the two extracted generic modules; the private wrapper
interfaces used by consumers remain. The original private imports `Mathlib.CategoryTheory.Localization.Pi`,
`Mathlib.CategoryTheory.Localization.Predicate` and
`Mathlib.CategoryTheory.Adjunction.Limits` are removed from the main module. Product
localization is used by the extracted generic proof; the main module uses its result.
The new scalar quotient helper does not need a private import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`; that import was
removed from the helper. The extracted derived-equivalence proof still needs its APIs. The main module also no
longer needs the private imports of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.CategoryTheory.Functor.ReflectsIso.Exact` and `Mathlib.CategoryTheory.PUnit`;
those remain in the extracted derived-calculus module where their proofs are used.
The scalar-data API is a private proof import in the extracted derived module; no public
definition uses it. The monoidal descent and model-normalization extension are now imported through the
normalized tensor-witness module; their mathematics is still needed.
The already proved derived equivalence and its consumers retain all their interfaces.
The resolution theorem is used as a tool in the new normalization proof; the native tensor
comparison and the original normalized monoidal descent remain necessary.

The derived-decomposition facade also removes its redundant private imports after
the support extraction: all its private proof APIs are available through
`import all Sheaf.Paper.FiniteClopenDecompositionCore`. Its original public imports
are retained verbatim. The following modules remain needed in the support module
or its transitive dependencies, so this is no global pruning:

- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`.
- `Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence`.
- `Sheaf.Paper.FiniteClopenConstructibilityBounds`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`.
- `Mathlib.Order.Bounds.Basic`.
- `Sheaf.CategoryTheory.StrictRoosAdditiveComparison`.
- `Sheaf.AlgebraicGeometry.VaryingRingOperations`.
- `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`.
- `Sheaf.Paper.DerivedPullbackTensorIso`.
- `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`.
- `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport`.
- `Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent`.
- `Sheaf.Paper.OpenCompletedRestrictionIdentification`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Mathlib.CategoryTheory.Localization.Prod`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`.
- `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`.
- `Sheaf.Paper.PurityFiniteSetting`.

The augmented-descent facade removes the following private imports after its
support extraction; their APIs remain supplied by the support module and its
transitive proof dependencies. No module or node is globally pruned:

- `Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`.
- `Sheaf.Paper.IntegralClopenRoosCalculus`.
- `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.
- `Sheaf.Paper.SfDerivedCompleteLegacyComparison`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence`.

## Where the brief, the DAG or earlier work was wrong

The stated monoidal descent supplies model normalization only for flat-term K-flat pairs.
It cannot alone discharge the item's square for arbitrary K-flat pairs. The new proved
resolution-and-cancellation lemma fills this missing step without changing either statement.
The scalar dependency and item express their representative squares in different quotient
models. The new proved conversion makes that change of model explicit. Empty components,
the empty partition and zero coefficients require no additional hypotheses in either proof.

## New nodes

`lem-pur-clopen-kflat-model-normalization` in
`Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatModelNormalization` proves that the normalized
tensor square extends from flat-term K-flat models to all K-flat pairs. It contains no holes.

`lem-pur-clopen-scalar-homotopy-representative` in
`Sheaf.AlgebraicGeometry.ProEtaleClopenScalarHomotopyRepresentative` proves the canonical
change from the cochain scalar representative square to the homotopy square. It contains
no holes and does not construct the scalar comparison.

`lem-pur-finite-clopen-normalized-tensor-models` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenNormalizedTensorModels` assembles the normalized
ordinary, total and derived tensor witnesses. It is the witness part of the tensor theorem;
flatness and K-flatness detection are still combined with it in the main module. It is proved
without holes. Splitting this part keeps the large dependent witness construction separate
from the already proved derived-equivalence argument, after profiling and sealing the slow
localization definitions.

`lem-pur-additive-finite-product-coordinate-decomposition` in
`Sheaf.CategoryTheory.AdditiveFiniteProductCoordinates` contains the existing complete
coordinate-insertion and bilimit proof, now independent of the sheaf-specific theorem.
A private wrapper preserves the original helper signature.

`lem-pur-exact-finite-product-derived-equivalence` in
`Sheaf.CategoryTheory.FiniteProductDerivedLocalization` contains the existing complete
complex equivalence and product-localization proof. A private wrapper preserves the
original helper signature used by consumers. Neither extraction adds a proof hole.

`lem-pur-clopen-arbitrary-scalar-normalized-witnesses` in
`Sheaf.AlgebraicGeometry.ProEtaleClopenArbitraryScalarNormalizedWitnesses` assembles the
existing sections, chain, cochain model, unit and coherence results for arbitrary prescribed
presentations. It is proved; the main theorem still converts the representative formula
and extracts the section and composition equations.

`lem-pur-finite-clopen-derived-calculus` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenDerivedCalculus` contains the already proved
derived-calculus section and canonical data. It is publicly imported by the item. The old
public declaration names and theorem signature are preserved, and the item retains private
compatibility wrappers for import-all consumers. This extraction adds no proof hole.

`lem-pur-clopen-strict-tower-roos-core` in
`Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosCore` contains the existing exact restriction,
product, normalized module-gluing and generic signed-comparison support section of the
strict-tower consumer. Its public data and exactness declarations keep their names and
bodies. Private wrappers in the original module preserve its used support interfaces.
The original strict-tower node still records all its unchanged mathematical conclusions.
This compilation split adds no mathematical hypothesis, proof hole or new proof route.

`lem-pur-finite-clopen-decomposition-core` in
`Sheaf.Paper.FiniteClopenDecompositionCore` contains the existing coefficient data,
additive exactness and fully proved generic derived, tensor, Roos and unit support
section. Twenty-four public names and all their data are preserved. This is a
compilation split with no new hole; the original node retains all decomposition
conclusions and the same remaining constructible-equivalences hole.

`lem-pur-integral-clopen-roos-calculus` in
`Sheaf.Paper.IntegralClopenRoosCalculus` contains the existing complete integral
Roos helper: derived tuple equivalence, countable products and canonical product
comparisons, and normalized reflection of limit triangles. The original augmented
descent module retains its private helper signature through a proved wrapper.
No public declaration is moved, and the new module contains no holes.

`lem-pur-augmented-integral-descent-core` in
`Sheaf.Paper.AugmentedIntegralDescentCore` records the existing exact finite
restriction, augmented quotient comparison and normalized Roos descent support.
Eight existing public names, signatures, attributes and data move here unchanged.
The original reduction-comparison hole also keeps its exact qualified name and
statement. This is a compilation relocation, not a new unproved statement or a
proof of that comparison. The original module keeps the complete membership proof.

Change record: `coord/changes/X6-finite-clopen-canonical-aliases.md`.

## Forced adaptations

`Sheaf.Paper.FiniteClopenConstructibilityBounds` (unclaimed) failed against the canonical
public clopen interface at original lines 220, 229, 234 and 391. The first error was
`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u.11` while choosing
`HasDerivedCategory` on `ProEt.clopenTensorModules`; related `Abelian` candidates caused
the later errors. Its existing fixed-coefficient native tensor model must keep the
published fixed coefficient-universe instances. Add only an explanatory comment and an
attribute block excluding the newly visible generic clopen monoidal/localization
candidates and the scalar derived-category instance exposed through `import all`,
immediately before `universe u w`. No existing declaration signature, visibility, proof
body or attribute is changed. The adapted file passes in 57.9 s (result `3e3f3b93ea8e216d28783622`). The unadapted original compiler result is
`cc63bf6ed10ff14be1e1202b`, and the change record contains the error excerpt.

`Sheaf.Paper.SfClopenPreservesCompleteness` (unclaimed) failed against the new public
interface at original lines 73, 93, 163, 167, 430 and 440: the new generic
`ProEt.ClopenLocalization.Modules` abelian instance leaves two universe parameters
unresolved when comparing it to the fixed `SheafOfModules` abelian instance. The first
constraint was `max (t + 2) (u + 1) =?= max (max (max (t + 2) u) (?u.103 + 1)) (?u.104 + 1)`.
Add only `attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian`
after the existing sheafification instance exclusion. Every original declaration,
visibility and signature is retained. After this exclusion, result
`11aa717d84bf4e98378334c4` reaches the final identity calculation but times out finding
`Mono (DerivedCategory.Q.map (𝟙 (Ψ.obj P)))`. Replace the cancellation proof of the local identity `hid` by
`IsIso.inv_eq_of_hom_inv_id`, followed by the composition-identity and functor-identity
equations. This proves the same identity without a `Mono` typeclass search. A first
attempt with `rw` was rejected by its dependent inverse-instance motive
(`24e80353e9bde9a20b8fab62`); the characterization avoids rewriting under `inv`. The first original result is
`3e3f3b93ea8e216d28783622`. Its direct importer
`Sheaf.Paper.SfClopenDerivedCompatibility` is checked against this change.

`Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence` (unclaimed) typechecks but
has unstable timing: its unchanged source passes in 52.3 s in
`23005eaeeff5f1aa1a223013`, and is rejected at 67 s in
`2fb8e3f5de06b021a9f9fc72`. Profiling locates its support calculations and two large
public proof checks. The definition and import improvements above precede the split.
Move the already proved support section and the fifteen public data/exactness declarations
to `Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosCore`. Keep their names, signatures
and definition bodies identical and publicly import them. The original file retains all
six tower/derived declarations and their complete proofs. Eighteen private compatibility
wrappers preserve the helper signatures used by the remaining proof and direct consumers;
three private data wrappers denote precisely the same product/transpose/comparison data.
Private support implementations receive a `Core` suffix. Re-register the existing
restriction and abelian instances locally to preserve their original inference priority.
Every direct importer is compiled against the split. No source-library declaration is
changed and no proof hole is introduced.

The first extracted consumer check (`a9413cede4f151f9e57158ec`) compiles the support
module in 19.9 s, then exposes generic `ClopenLocalization` abelian/derived instances
in the wrapper at lines 170, 796 and 930. Exclude these two generic instances locally;
the original fixed-universe instances and public signatures are retained.

`Sheaf.Paper.ClopenCompletedOperationTowers` (unclaimed) is a direct strict-tower
consumer. Its unchanged source exceeds 60 s at 64 s in `144c389ca7bd9de4f63372af`
and 67 s in `dc65bae996333a9f48d07c65`. Profiling in
`749eee69d1ed245314bc82e8` locates 22.5 s in linting, almost all at its final large
comparison statement. Add an explanatory comment and disable only
`linter.unusedDecidableInType` and `linter.unusedFintypeInType`, the same type-scanning
linters already disabled in the strict-tower module. All declaration signatures,
attributes, bodies and the existing named `sorry` are byte-identical to the source.
The adapted file passes in 48.0 s (`eb635e6c5d33a4fde82989c0`).
There are no current Lean importers of this module. No mathematical instance or
kernel-checking option is changed, and no diagnostic profiling option is delivered.

`Sheaf.Paper.AugmentedIntegralDescent` (unclaimed) fails unchanged against the new
interface in `fcf3072910f8bd9921d87d8c`, at lines 144, 176, 358 and 771. The first
constraint is `u + 1 =?= max (u + 1) ?u.23`, comparing its fixed
`Abelian (scalarReductionSource l E Y)` with the newly visible generic
`Abelian (ProEt.clopenTensorModules ...)` candidate. Add only a comment and
`attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian`
before the existing options. All original declaration signatures, bodies and attributes
are unchanged. Its one direct importer is `Sheaf.Paper.ClopenRoosIntegralDescent`,
which is included in the remaining checks. The original result also verifies
`IntegralReductionFiniteClopenBounds` in 52.5 s and `SfClopenDerivedCompatibility`
in 22.8 s; those validation-only copies are removed before delivery.

The narrowed augmented-descent check (`faca1dcf6509bcd53439f2f3`) then exposes the
same unresolved fixed-universe choice from `ClopenLocalization.modulesAbelian`.
Exclude that generic abelian candidate as well; no other declaration changes.
The final support module passes with default transparency in 20.5 s
(`de46ca818ec60a03366c1e1f`); its `PUnit` and `DerivedLimit` imports are private
because they are used only by support proofs. The original facade retains its
published imports.


`Sheaf.Paper.ClopenRoosIntegralDescent` (unclaimed) fails unchanged in
`b7065e002b4fa5ea92653bcb` at original lines 235, 246, 430 and 432. Generic
`ClopenMonoidalDescent.modulesAbelian` makes the fixed completed-coefficient
abelian structure leave `u + 1 =?= max (u + 1) ?u` unresolved. Exclude that generic
candidate and `ClopenLocalization.modulesAbelian`, exactly as in augmented descent.
No declaration signature, body or original attribute changes. The adapted file
passes in 35.0 s (`45e48afdf83a65c72ada5587`). It has no current Lean importers.


`Sheaf.Paper.ClopenCommonCompactSupport` (unclaimed) fails unchanged in
`c35afa55dbef73e0125abd77`. Original lines 129--135 and 190--205 leave fixed
`Abelian`/`HasDerivedCategory` universes unresolved via `ClopenScalar.derived`
and `ClopenMonoidalDescent.modulesAbelian`; lines 309--327, 409, 790--793,
852--853 and 973--974 show related fixed-coefficient ambiguities. Add only the
same explicit fixed-universe instance selection block used in constructibility
bounds. Every original declaration signature, proof body and attribute stays
identical. The adapted file passes in 52.5 s (`a08ec9ae9d4256036843ff53`), including
the two original iso-cancellation proofs, which need no changes after instance
selection. Its direct importers `ProperFiniteNormalization` and
`ClopenCounitAdjointComparison` are checked against this adaptation.

Both unchanged compact-support importers pass (`8d68d0e0ffcac10c3fe6b750`);
their validation-only source copies are removed. All validation-only source copies
are removed from the packet. The final strict-tower facade passes in 32.1 s
(`9bcb3dbd2c547a72b953fe11`), augmented descent in 47.1 s
(`c97b73702dc1c244ec3d7f25`), completeness in 56.7 s and constructibility bounds
in 30.1 s (`749eee69d1ed245314bc82e8`).


`Sheaf.Paper.FiniteClopenDerivedDecomposition` (unclaimed) exceeds the limit with
its unchanged source. The detailed unit-helper trace
(`be0caf4e00e45517807bf105`) identifies repeated elaboration of the object formula
of the chosen common-stage pullback. Add the fully proved private lemma
`commonStagePullback_obj` and scope a local irreducibility setting to
`commonUnitCheck`. The latest shared source's finite restriction identification
proof and its support helpers are preserved verbatim. Although this passes once
in 58.9 s, the second delivery compile reaches 74 s. Explicitly simplifying the
named pullback definition still reaches 73 s in `702cdfa64b45ce8a9a4af5be`;
profiling shows proof elaboration dominates and linting is only 3.7 s.

After these definition improvements, extract the existing coefficient data and
complete support section into `Sheaf.Paper.FiniteClopenDecompositionCore`.
Twenty-four public declarations keep their exact names, signatures, attributes
and data. The original module keeps all decomposition conclusions and current
proofs, publicly imports the support module, and privately imports its complete
helpers. Reapply the original local instance selections and irreducibility
settings in the original module. The new support module uses default transparency.
No mathematical route, hypothesis, target, public data or current proof is
removed; the one original constructible-equivalences hole is untouched.
Update only the existing node's proof, dependencies, proof origin and Lean
attachment to record the compilation split. All eleven ordinary direct importers
are checked; none uses `import all` of the original module.

The first delivery attempt stops without pushing because augmented descent takes
70 s in the full compilation. Its profile (`c97cd3eb11983b2e5ad76022`) identifies
11.3 s linting the large final statement (13 s linting in all). As in the completed
operation-towers consumer, disable only `linter.unusedDecidableInType` and
`linter.unusedFintypeInType`, with an explanatory comment. Existing declaration
bodies, signatures, attributes, data, mathematical instances and kernel checking
remain unchanged. No profiler option is delivered.

The clean augmented-descent timing repair passes in 59.8 s
(`b1eb0cc483f4daaf1b7aa807`), with no warnings. Its declaration bodies and one
original hole remain unchanged.

The first decomposition-split check (`c65a06494b635fa4e5daa527`) compiles the
support module, then exposes `ClopenScalar.derived` in fixed-coefficient functor
types of the facade, leaving `u + 1 =?= max (u + 1) ?u` unresolved at lines
299--363 and 881--964, with related sheaf and product-category universe errors.
Exclude the generic scalar derived/sheafification and localization sheafification
candidates, as in the earlier fixed-coefficient adaptations. No declaration
signature or mathematical data is changed.

The split decomposition facade compiles in 38.7 s
(`3941c0bc53df8155cc83d275`). Its proof-only imports are supplied by the extracted
support API. The support module passed with default transparency in
`c65a06494b635fa4e5daa527`. All eleven direct importer checks pass (`65d75f756021f3d643b01ae1`); the nine
unchanged validation-only source copies are removed.

The final decomposition support/facade pair and all eleven direct importers pass
in `65d75f756021f3d643b01ae1`, without additional source adaptations. The nine
validation-only copies are verified against their initial hashes and removed;
no quarantined source, archive or DAG attachment is removed or restored by this
cleanup. The packet retains twenty Lean files and fifteen DAG records: ten new proved
support records, one support record relocating the existing augmented-comparison
hole, and four existing records updated only in the permitted fields.

The full delivery batch rejects augmented descent again at 68 s
(`l2568baf910b7a5416d667417`), despite the earlier isolated pass. The follow-up
profile (`fcad47c80b1c1b9bcd347660`) has 12.1 s in tactics, 6.71 s in type
checking, 7.69 s in instance inference and 8.34 s in linting. After the preceding
canonical-definition improvements and narrow linter repair, extract the already
proved private `integralRoosCalculus` calculation into the new proved module
`IntegralClopenRoosCalculus`. Its default transparency settings are retained.
The original private header and public declarations stay identical; only the
private proof body becomes an application of the extracted theorem, with one
new private import. The support theorem preserves the original proof. Update
only the parent node's proof, dependencies and proof origin. The direct importer
`ClopenRoosIntegralDescent` is included in the new compile check. No hole is moved,
added or removed by this timing extraction.

The private Roos helper extraction compiles but augmented descent still takes
63 s in `ae5b618148363288788dba5b`. Therefore split the remaining support prefix
into `AugmentedIntegralDescentCore`, after the preceding definition and linting
improvements. Its new module uses default transparency. Eight original public
declarations retain their exact names, statements, attributes and data; the
original augmented-comparison hole is the same declaration. The facade retains
every original public import and publicly re-exports the support module. Its
membership theorem and proof are byte-identical. Its old proof-only imports
are supplied by `import all` of the support module, except the finite-bound
and finite-extrema imports still used directly. The parent node retains the
membership attachment and adds the support dependency; the new support node
records the relocated declarations. No target, mathematical statement or
proof hole changes. The sole ordinary direct importer remains
`ClopenRoosIntegralDescent` and is compiled with this split.

The final augmented support module, unchanged membership facade and direct
Roos-integral consumer all compile without warnings in
`30f2ba22f254f954f7ce86e1`. The facade takes 13.7 s and the direct consumer
46.4 s. Default transparency is retained in both new integral support modules.
All twenty packet files have successful compile checks; the existing moved
comparison is the same original hole. Temporary timing sources and profiler
options are removed.

The next full delivery rejects `ClopenCompletedOperationTowers` at 65 s.
The focused profile (`feb807a6a344685964792f1f`) locates 27.7 s in linting
the final statement. That statement already locally marks `TensorComparison`,
`ScalarComparison` and the operation model definitions irreducible, while the
original file globally ignores that transparency setting during backward
elaboration. Scope `backward.isDefEq.respectTransparency true` to the final
theorem. Every declaration signature, body, attribute and the existing hole
remain byte-identical; no definition or import is changed. The clean file
passes without warnings in 47.8 s (`bdd9f4a924e45ccddcb2367e`). This does not
require another support split, and no diagnostic option is delivered.

The final twenty-file batch passes in `l9e1ad6699c0835c7a28e240d`.
The server preflight then identifies two metadata discrepancies: the augmented
support node listed its already proved private legacy-completeness helper as a
dependency without a proof-step use, and the generic derived-equivalence node
included section context in `lean.statement`. Record that existing helper step
and store exactly the declaration header. These corrections change no Lean
source, statement, proof, data or hole count.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
