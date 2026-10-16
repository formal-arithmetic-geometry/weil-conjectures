## What changed

The current independent second reading replaces the hand-written evaluation ring
homomorphism by an abbreviation of Mathlib's `ContinuousMap.evalAlgHom ℤ E`, records
fresh searches for both open lemmas, and adapts the newly landed
`Sheaf.Paper.IntegralScalarContractive` with one proof-import line so it can still
use the extracted private helpers. No theorem statement or proof changes.

Repair of the landing refusal at head `3f9167606`: removed the duplicate
`AlgebraicGeometry.ProEtale.sumComplEquiv_symm_inl`. The existing coefficient-independent
`PadicAlgCl.sumComplEquiv` and `PadicAlgCl.sumComplEquiv_symm_inl` move unchanged from
`WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix` to the lightweight
`Sheaf.LinearAlgebra.FiniteIndexSplitting` module, which UnitMatrix publicly reexports.
The elimination module publicly imports that API and its `sumComplEquiv` is now a
reducible alias of the existing equivalence. Thus its block calculation uses the
existing simp theorem. Directly importing UnitMatrix is unusable here: combining it
with the continuous realization reports a duplicate pro-étale upper/lower-star parser
constant from the finite-coefficient and general APIs. Extracting just the generic API
avoids that conflict, preserves all UnitMatrix public declaration signatures and moved bodies, and adds
no proof obligation. UnitMatrix is unclaimed in `coord/claims`.


Repair of review H9, point 5: removed the unused public import
`Sheaf.AlgebraicGeometry.LocallyClosedStratification` and proof import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` from the extracted
`CondensedFieldContinuousRealization` module. The original item's public
`LocallyClosedStratification` import is retained. No declaration or proof changed.

Closed the sole original hole in
`AlgebraicGeometry.ProEtale.exists_finiteFree_cover_of_condensedField_lfp` by a complete
Lean reduction. From the chosen local presentations, the proof constructs continuous
matrices and their coranks, descends corank through the flat cover, proves local
constancy using noetherianity and generic points, recovers matrix rank, applies the
local cokernel criterion, and composes the covers using the monoidal pullback comparison.
The existing stratum theorem and both original public signatures are preserved.

The coefficient realization and its private helpers move to a publicly reexported
module to avoid an import cycle. The canonical realization is generalized to arbitrary
totally disconnected normed fields. Its chosen isomorphism is determined uniquely by
its test equations, and the uniqueness theorem is proved. Presentation matrices and
pulled-back realizations are explicit definitions with no holes.

The generic flat rank-descent lemma, the Gaussian elimination theorem for continuous
functions (including locally constant rank), the open-cover construction for normal
forms, and the passage from block normal form to finite-free cokernel are all proved.
This follows the source library's existing Schur-complement calculation, generalized
from locally finite p-adic functions to arbitrary normed-field continuous functions.

## Proved and sorry left

This repair adds no holes. The extracted `PadicAlgCl.sumComplEquiv_symm_inl` retains
its existing complete proof. The duplicate theorem is removed, not renamed.

Original hole closed: `AlgebraicGeometry.ProEtale.exists_finiteFree_cover_of_condensedField_lfp`
(1 of 1). This is a decomposition, not an end-to-end axiom-free proof of local triviality:
two new holes remain, each strictly a part of the original argument.

- `AlgebraicGeometry.ProEtale.condensedField_presentation_corank_eq`
  (`lem-weil-pbc-condensed-field-presentation-corank`): still needs the geometric-point
  comparison of the two module presentations, compatibility of the canonical realization
  with evaluation, and rank-nullity. The existing geometric-field evaluation theorem
  supplies exactness; the internal-module and coefficient comparison glue remains.
- `AlgebraicGeometry.ProEtale.continuousField_matrix_sheaf_normalForm`
  (`lem-weil-pbc-continuous-field-matrix-sheaf-normal-form`): still needs the regular-module
  endomorphism/function correspondence, its finite-matrix version and its compatibility
  with the monoidal inverse-image/restriction comparison along an open immersion.
  The matrix factorization, its invertibility, neighbourhoods and open cover are already
  proved separately; this statement takes the explicit factorization as input and
  has neither a locally constant-rank nor a covering hypothesis.

No hole remains in the item module. Neither definitions nor private declarations contain
holes. The delivery closes one original hole and adds two, a net increase of one before
any pruning; it is reported as a decomposition. The previously proved coefficient and
stratum clauses remain proved. Empty schemes, empty cover members, rank zero and
zero rows/columns are allowed in every intermediate statement.

## No longer needed

This repair reading reuses Mathlib's evaluation API: `continuousFieldEval` is now
an abbreviation of `ContinuousMap.evalAlgHom ℤ E`, forgetting its algebra structure.
The `Mathlib.Data.Fintype.Basic` import in the shared finite-index module is needed:
removing it fails to synthesize decidable membership in the finite range. It is retained.
The moved equivalence, inverse equation and simp attribute remain unchanged.

The duplicate `AlgebraicGeometry.ProEtale.sumComplEquiv_symm_inl` is removed entirely,
including its elimination-node declaration attachment. The local duplicate equivalence
construction is replaced by an abbreviation of the existing `PadicAlgCl` construction.
The existing UnitMatrix module stays in the library and publicly reexports the extracted
API; no downstream adaptation is required. No additional module is globally pruned.


In `CondensedFieldContinuousRealization`, the imports
`Sheaf.AlgebraicGeometry.LocallyClosedStratification` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` are unused and removed
as required by H9, point 5. This does not globally prune the stratification module:
the original item still publicly imports it for its stratum statement.

No previously planned module is claimed globally pruned. The explicit separate
`lem-sc-flat-going-down` dependency is replaced in the descent proof by Mathlib's
`Flat.generalizingMap`; finite irreducible components and sobriety are likewise used
directly from Mathlib. Their separate statement modules are not imported by the new
rank-descent lemma. All other old planned dependencies either remain below the
realization/corank lemmas or are statement dependencies of the original item.

The proof imports
`Sheaf.Paper.ProEtalePointComponentsMaps` (including its private API),
`Sheaf.Paper.ProEtaleSheafificationWcontractibleSections`,
`Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`,
`WeilConjectures.CategoryTheory.Sites.MonObj`, and
`Mathlib.Analysis.Normed.Module.FiniteDimension` move with the coefficient realization;
they are not globally pruned. The original proof-only imports
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`, and
`Sheaf.Paper.GeometricFieldProEtaleEvaluation` are removed from the item: the actual
reduction uses the new intermediate declarations instead, while exact inverse image
and geometric evaluation remain in the corank node's unproved plan. The original public
`MorphismDefs` import remains publicly
available through the realization module. The rank-descent module does not import
presentation matrices: it is a generic topology lemma. The unused `Mathlib.Topology.ContinuousMap.Units` import is removed; the normed-field
topology comes directly from `Mathlib.Analysis.Normed.Field.Lemmas`. The source-library
rank and Schur-complement extensions are proof-only imports. Experimental scratch modules are
not delivered. New proof imports are ordinary `import`; statement dependencies are public.

Direct dependency pruning, exhaustively against the original node: the following old
`proof_deps` leave the item node. The realization node now carries
`def-weil-pbc-condensed-e-module-category`,
`lem-weil-pbc-proetale-point-components-maps`,
`lem-weil-pbc-proetale-sheafification-wcontractible-sections`, and
`lem-weil-pbc-proetale-affine-wcontractible-covering-family`. The corank node carries
`lem-weil-pbc-site-pullback-abelian-exact` and
`lem-weil-pbc-geometric-field-proetale-evaluation`. The framework still supplies
`def-weil-proetale-inverse-image`, `def-weil-pbc-proetale-site`, and
`def-weil-flat-morphism`. Mathlib directly replaces `lem-sc-flat-going-down`,
`lem-sc-noetherian-finite-irreducible-components`, and `lem-sc-scheme-sober` in the
proved descent argument. None of these is asserted globally unreachable.

Second reading also changed the matrix-elimination module's
`Mathlib.LinearAlgebra.Matrix.SchurComplement` import from public to proof-only:
its statements use rank, determinants, and block matrices already supplied by the
public matrix-rank import; Schur-complement results occur only in the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery unnecessarily redeclared the existing generic inverse equation.
The landing check correctly rejected that duplicate. This repair shares the original
API instead. The old second-reading section below describes the pre-repair delivery;
the next independent reader must check this extraction and its compilation too.


No mathematical error in the statement or planned route was found. A pro-etale
`Scheme.Cover` does not directly supply all the desired cover-map instances through
`map_prop`/`exists_eq`; the proof extracts weak etaleness and joint surjectivity from
`mem₀` and the precoverage comparison. Flat going-down and noetherian generic-point
arguments are already available in Mathlib.

A packaged ring-object pullback isomorphism caused expensive unfolding when exported.
The explicit realization API instead returns its abelian-sheaf morphism with proved
`IsIso` and `IsMonHom` instances. All final module compilations are below 60 seconds.
The normal-form step was narrowed after proving the actual neighbourhood construction;
it has not been replaced by a restatement of the item theorem.

## New nodes

- `def-weil-pbc-finite-index-splitting`: the already proved generic equivalence and
  inverse equation, extracted unchanged from UnitMatrix; no new hole. Change record:
  `coord/changes/F1-finite-index-splitting-extraction.md`.


- `lem-weil-pbc-condensed-field-continuous-realization`: moved realization proof and
  its proved generalization to totally disconnected normed fields, plus unique canonical API.
- `def-weil-pbc-condensed-field-presentation-matrix`: explicit continuous matrix and
  explicit pulled-back coefficient realization with its instances.
- `lem-weil-pbc-condensed-field-presentation-corank`: the geometric common-fibre step,
  one remaining hole.
- `lem-weil-pbc-condensed-field-rank-descent`: proved generic descent through a flat
  jointly surjective family over a topologically noetherian scheme.
- `lem-weil-pbc-continuous-field-matrix-elimination`: proved continuous Schur-complement
  elimination for constant and locally constant rank, including empty index sets.
- `lem-weil-pbc-continuous-field-matrix-sheaf-normal-form`: lifting a specified factorization
  along one open immersion, the second remaining hole.
- `lem-weil-pbc-continuous-field-presentation-normal-form`: proved neighbourhood and
  open-cover assembly from elimination and the lifting lemma.
- `lem-weil-pbc-continuous-field-cokernel-local-free`: proved categorical cokernel
  calculation from the normal form.

The original node's proof and proof dependencies follow these exact declarations.
Change record: `coord/changes/F1-condensed-field-local-triviality.md`.

## Earlier second reading (a previous round; superseded)

1. **Interfaces — pass.** Compared all nine delivered modules with the repository.
Only the original item already exists there. Its four public signatures are identical:
`profiniteTestProjection`, `existsUnique_condensedFieldContinuousMapIso`,
`exists_finiteFree_cover_of_condensedField_lfp`, and
`exists_finiteFree_cover_on_condensedField_strata`. The first two move through the
public reexport declared in the change record; the projection's body is identical.
No target or existing definition changes value, and no other group's module is edited.

2. **Proof and compilation — pass.** All nine modules compiled through `lcompile.py
--all`, without errors or warnings (longest file 33.3 seconds). A scratch axiom probe
checked all 21 public declarations: only `propext`, `Classical.choice`, `Quot.sound`,
and, precisely for the two open sublemmas and their consequences, `sorryAx` occur.
The realization, its chosen isomorphism, the explicit presentation matrix and pulled-back
realization, generic descent, and both elimination results have no `sorryAx`.
The two reported public theorem bodies are the only `sorry`s. There are no forbidden
axiom/unsafe/opaque/extern/implemented_by declarations, private holes, or hollow definitions.
The chosen coefficient isomorphism comes from a proved unique characterization.

3. **Split statements — pass.** Read both statements, their complete docstring proofs,
and their nodes. Corank comparison concerns two presentations above one base point;
it has no local-freeness conclusion. A common geometric overfield and exact evaluation
identify their cokernels, so rank-nullity proves the stated subtraction equality.
The other hole assumes a specified factorization and only lifts it along one open
immersion; it contains neither local-rank nor covering construction. Multiplication
by global sections, biproduct matrix calculus, and open restriction give its two
basis isomorphisms in the asserted orientation. Both allow zero rows, zero columns,
rank zero, and empty opens; an empty cover member contributes no point to corank
comparison. Repeated LeanFinder searches with different wording and repository searches
found related `SheafOfModules` presentation/Morita APIs, `Scheme.Modules.FreeMatrix`,
and `AdicSheaf.UnitMatrix`. The latter uses locally finite functions into `PadicAlgCl`,
and the former uses structure-sheaf modules; neither directly proves these arbitrary
continuous-field/internal-module statements. Recorded the independent searches in both
new nodes. Neither remaining hole can be closed by a short application of those APIs.

4. **Route and pruning — pass after import repair.** Read the explicit top-down proof:
coranks descend by flat generalization lifting; generic points and finitely many
irreducible components give clopen fibres; the matrix rank bound recovers rank from
corank; continuous elimination supplies neighbourhoods; block cokernel calculus and
pullback composition give the cover. The stratum proof remains unchanged. The proper
base-change unit's `realized` statement and three proof steps are untouched.
Demoted the proof-only public Schur-complement import and expanded `No longer needed`
to list every removed old direct proof dependency, distinguishing moved dependencies
from direct Mathlib replacements. No globally pruned module is claimed.

5. **DAG agreement — pass.** Checked each Lean attachment against its declaration
(the node records normalize whitespace), every proof-dependency set against the union
of its steps, and all new nodes' source, search, creation, blueprint, chapter, unit,
and Lean fields. The original node records the actual reduction; the two open nodes
state strictly intermediate obligations. Existing signatures and the unit record
remain unchanged. Earlier H9 return point 5 is repaired: both unused imports are absent
from the extracted realization while the original stratum import remains public.

Changes in this reading: made the Schur-complement import proof-only, added independent
search evidence to the two open nodes, corrected and expanded the import/dependency-pruning report, and wrote
this review. No theorem statement or mathematical proof changed. One original hole is
closed syntactically and two lower holes are added: this remains a decomposition with
net minus one, not an end-to-end proof of local triviality.

## Second reading by F1

1. **Interfaces — pass.** Diffed the original eleven delivered modules against the read-only
repository, then checked the newly landed IntegralScalarContractive adaptation separately. The original item's four public signatures are byte-for-byte identical,
including those moved into the realization module and publicly reexported. Its projection
body is byte-for-byte identical. All 49 public declaration signatures from UnitMatrix
are preserved; its two extracted declaration bodies are byte-for-byte identical and the
simp attribute is retained. Its only other edit is the public reexport. UnitMatrix is
unclaimed, as the extraction change record says. No target or existing definition is
changed. The only new definition edit in this reading is the definitionally equal
Mathlib evaluation abbreviation.

2. **Proof and compilation — pass.** The first delivery dry run compiled all eleven modules
and ran the declaration axiom probes; its sole preflight refusal was this missing
current second-reading section. The final sequential compile and independent explicit
axiom-probe results are recorded in the verification paragraph below. Source inspection
finds precisely the two reported public theorem holes, no forbidden declarations,
no private holes and no hollow definitions. The chosen continuous realization comes
from a proved unique characterization; presentation matrices and pulled-back
realizations are explicit constructions.

3. **Split statements — pass.** Read both complete docstring proofs and nodes. Common-fibre
corank comparison identifies two finite-dimensional cokernels using a common geometric
overfield, coefficient compatibility, exact pullback/evaluation and rank-nullity; it has
no local-freeness conclusion. The normal-form hole assumes the actual invertible matrix
factorization and lifts it along one open immersion. It neither constructs neighbourhoods
nor assumes/establishes locally constant rank or covers. Thus neither restates the item.
Checked zero rows/columns, rank zero, empty opens and empty schemes; injection hypotheses
bound the chosen rank, and empty cover members contribute no points to corank comparison.
Fresh independent LeanFinder queries found `SheafOfModules.unitHomEquiv` and
`freeHomEquiv`, and ordinary-module stalk-rank lemmas. Read those APIs: they require a
comparison with internal module objects and do not close either hole directly. The
existing Adic UnitMatrix calculus uses locally finite PadicAlgCl-valued functions,
whereas these statements use arbitrary continuous normed-field coefficients. The
shared coefficient-independent equivalence is correctly reused. Neither remaining
hole admits a short direct application of the inspected APIs.

4. **Route and pruning — pass.** The reduction follows specialization-invariant coranks,
flat going-down, noetherian generic points, locally constant ranks, explicit continuous
Schur elimination, block cokernels and composed covers. The unit's `realized` statement
and all three steps are untouched. Checked every one of the twelve original direct
proof dependencies removed from the item against `No longer needed`; each is accounted
for as moved, retained by the framework, or replaced directly by Mathlib. No global
pruning is claimed. New proof-only dependencies are ordinary imports; UnitMatrix
retains its existing public API. Tested removing
`Mathlib.Data.Fintype.Basic` from the extracted module: compilation fails at decidable
finite-range membership, so that import is necessary and retained. Earlier H9 unused
imports remain absent from the realization module.

5. **DAG agreement — pass.** Read the ten node files against their attached Lean
statements and actual proof steps. Every `proof_deps` equals the union of step uses.
The old item changes only `lean`, `proof`, `proof_deps`, and `proof_origin`. The nine new
nodes carry the required source, searches, creation, blueprint, chapter, unit and Lean
fields. The two open nodes describe precisely their remaining obligations, including
the internal-module comparison still required at geometric evaluation. The extracted
finite-index node names the original declarations, not duplicate proofs. Added the
independent search records and the Mathlib evaluation reuse to the appropriate nodes.

Changes in this reading: replaced the hand-written `continuousFieldEval` construction
by an abbreviation of `ContinuousMap.evalAlgHom ℤ E`, added independent search evidence,
checked the extraction and its necessary finite-range import, adapted the newly landed
IntegralScalarContractive proof import, and wrote this current review. No theorem statement or mathematical proof changed. One original hole is closed
by adding two strictly smaller holes: a decomposition with net minus one, not an
end-to-end axiom-free proof of local triviality.

Verification: the final sequential `lcompile.py --all` compiled all eleven delivered
modules without errors or warnings (slowest 32.4 seconds). The independent scratch
`#print axioms` probe checked all 22 public declarations in the extracted/new modules
and the item. Only `propext`, `Classical.choice` and `Quot.sound` occur, with `sorryAx`
precisely in the two open lemmas and their four consequences (the item and stratum
theorems, the cover normal form and the local cokernel criterion). The canonical
realization and its choice, explicit matrices, rank descent, continuous elimination
and shared finite-index equivalence/inverse equation are free of `sorryAx`.
Logs are in `scratch/current-second-reading-compile.log` and
`scratch/current-second-reading-axioms.log`.

## Forced adaptations

`Sheaf.Paper.IntegralScalarContractive` (unclaimed) landed during this reading and was
identified by the next preflight. Its original file compiles against the published
baseline. Against the delivered extraction it fails with:

```text
line 56/99: Unknown identifier `profiniteTestProjection_natural`
line 110: Unknown identifier `pushforwardRingMonObj`
line 170: Unknown identifier `canonicalComponentArrow`
line 281: Unknown identifier `isIso_of_affine_weaklyContractible`
```

These are the private helpers moved out of the original item. The only changed line is
line 11, replacing `import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
with `import all Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`. The adapted
module compiles cleanly against the delivery (11.9 seconds). The unchanged original
against the changed dependencies fails in 13.3 seconds. No declaration, statement,
proof, attribute or visibility changes. The change record's Users section now includes
this importer and the compatibility evidence. Logs are
`scratch/current-importer-baseline-compile.log`, `scratch/current-importer-compile.log`,
and `scratch/current-importer-adapted-compile.log`.
