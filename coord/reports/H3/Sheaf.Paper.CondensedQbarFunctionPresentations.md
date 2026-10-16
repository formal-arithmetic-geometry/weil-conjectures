## What changed

Return repair (2026-10-16): resolved the duplicate-statement refusal by consolidating
coefficient realization in the new lower coefficient module. The unclaimed module
`Sheaf.Paper.CondensedQbarLfpMatrixRefinement` now imports and reuses
`CondensedQbarCoefficientRealization.globalCoefficientIso`; its entire old private
`CoefficientUniverse` section is removed. This removes the three reported duplicate
lemmas, together with the duplicate private constructions supporting them. It avoids
the import cycle that would result from importing matrix refinement into coefficients.
The matrix-refinement public theorem and all public imports are unchanged.
The full overlay checker also matched three private coordinate lemma texts against
`CondensedFieldPresentationCorank`. Those declarations have different universe
contexts: the present file uses `E : Type uE` and `ModuleCat.{u + 1} E`, independently,
whereas the old module uses `E : Type u` and `ModuleCat.{u + 1} E`. All field,
category, functor and coordinate binders are now explicit on
`finiteFreeEvaluationCoords_apply`, `finiteFreeEvaluationCoords_symm_single`, and
`finiteFreeEvaluationCoords_matrix`. This only exposes the already inferred private
signatures; it preserves their proofs and all calls, and records the actual universe
generalization instead of renaming or restating a duplicate. Its DAG
proof route and `coord/changes/condensed-qbar-shared-coefficient-realization.md` record
the consolidation. No coefficient statement, construction or remaining hole changes.
The earlier second-reading section below predates this repair. The current
`Second reading by H3` section checks the adapted matrix-refinement module and
explicit coordinate-lemma binders.

Repair verification: all three delivered modules compile without warnings through
`lcompile.py` (38.6 s, 19.7 s and 8.9 s respectively); the item with explicit binders
also compiles (21.6 s). The unchanged direct consumer of matrix refinement,
`Sheaf.Paper.CondensedQbarLfpLocalTriviality`, compiles against the complete delivery
overlay (2.4 s). The actual `tools/import_prune_check.py` passes for each of the
three delivered modules against the complete overlay, including both sets of
reported statement matches. The required `deliver3.py --no-push` dry run passes
compilation, axiom probing and preflight. No delivery is pushed by this worker.

The assigned theorem `AlgebraicGeometry.ProEtale.exists_condensedQbar_compatible_function_presentations`
is proved, with its original signature and all original public definitions unchanged.
The proof constructs a cover of the required universe by binding the affine open cover
with singleton affine contractible extensions. It reconstructs the pulled-back finite
presentation from regular-module matrix entries, restricts that presentation to every
open, and compares the evaluated quotient vector spaces using finite-colimit-preserving
fiber functors and the dimension formula for a matrix cokernel.

A new coefficient module contains an explicit canonical coefficient-ring realization:
finite-extension continuous realizations are transported through ULift and then through
the filtered colimit of finite coefficient fields. The ring laws, finite-inclusion factorization, and normalization on every bounded
profinite test function are proved. Bounded functions are also proved to descend
through the connected-component quotient with the same finite-extension bound, including
the empty space. Its scalar
action is actual presheaf multiplication, monoidal sheafification and transport through
that constructed realization. No data are chosen from an unproved existence theorem.

The module also constructs geometric fibers by pullback to the algebraic closure of a
residue field and terminal evaluation. It proves that the bounded-presheaf unit at an
algebraically closed field is invertible, constructs the coefficient identification,
converts internal abelian-group modules using their tensor actions, and proves additivity,
finite-colimit preservation, and regular-module coordinates. The tensor-action proof
is adapted from the proved private implementation in `Sheaf.Paper.InternalModuleAbEquivalence`;
that private implementation is not available as a public definition.

Every regular endomorphism of the bounded-function presheaf is also proved to be
multiplication by its bounded image of one at the terminal object.

The remaining coefficient theorem supplies four properties of these constructions:
basis surjectivity of scalars on affines weakly contractible over themselves, restriction compatibility, pointwise scalar evaluation,
and comparison over two points with the same image. The coefficient interface is then
assembled from the proved constructions and those properties. The constructed fiber data
are packaged separately from their properties to prevent kernel unfolding of geometric
functors when checking dependent records and matrix presentations. The original DAG node
and the new coefficient node describe this route. The static check requires a context-change
record for additional universe and private-helper command scopes; see
`coord/changes/condensed-qbar-function-presentation-proof-scopes.md`.

Verification: both delivered modules compile. The unchanged direct consumer
`Sheaf.Paper.CondensedQbarLfpMatrixRefinement` also compiles against their overlay. Explicit `#print axioms` checks for
`globalCoefficientIso`, `presheafScalar_surjective`, `fiber_colimits`, and
`fiberRegularCoordinates` show only `propext`, `Classical.choice`, and `Quot.sound`.
The assembled coefficient theorem additionally shows `sorryAx`, as expected from
the one remaining named compatibility theorem.

## Proved and sorry left

This repair adds zero holes and closes zero additional holes. The adapted matrix
refinement module has zero holes. The retained delivery still closes the assigned
one hole and leaves the same single coefficient-level hole, as listed below.


Original holes closed (1):

- `AlgebraicGeometry.ProEtale.exists_condensedQbar_compatible_function_presentations`.

New holes added / all holes left (1):

- `AlgebraicGeometry.ProEtale.condensedQbar_canonical_coefficient_properties`, in
  `Sheaf.Paper.CondensedQbarFunctionCoefficients`.

This is a decomposition: one original hole closed, one strictly coefficient-level hole
added, net zero holes closed. The remaining theorem has no input module, finite
presentation, chosen cover, matrix, quotient dimension, rank or freeness assertion.
The realization, scalar action, geometric fiber data and their finite-colimit and
regular-coordinate properties are already constructed and proved in this session.
The new hole still needs the canonical realization's compatibility with localization
and geometric evaluation, the point-basis identification giving scalar surjectivity,
and a common algebraically closed overfield comparison for two geometric points.
It is not a completed axiom-free proof of the assigned theorem's import closure.

## No longer needed

Exact import inventory for the item, relative to the repository: these seven plain
imports are removed:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`;
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`;
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`;
- `Sheaf.Paper.CondensedPointBasisEvaluation`;
- `Sheaf.Paper.GeometricFieldProEtaleEvaluation`;
- `Sheaf.Paper.ProfinitePointPullback`.

The new coefficient and affine-contractible-extension imports supply the actual
proof dependencies. The matrix and module-category Mathlib imports support its
local finite-free coordinate and cokernel calculations. The public imports are
unchanged. These are removed direct dependencies, not claims of global pruning.


Return repair: the private coefficient section in
`Sheaf.Paper.CondensedQbarLfpMatrixRefinement` is no longer needed:
`liftNormedField`, `liftNormedAlgebra`, `liftContinuousDown`, `liftContinuousUp`,
`liftCondensedRingIso`, `liftSchemeRingIso`, `finiteFieldComparison`,
`isMonHom_of_colimit`, `fieldDiagramIso`, and `globalCoefficientIso` in namespace
`CondensedQbarMatrixRefinement` are removed. Their sole consumer now reuses the
canonical construction in `CondensedQbarCoefficientRealization`. This removes
265 lines of duplicate private implementation. No DAG node or whole module is
withdrawn. The following proof-only imports are removed from matrix refinement:
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`,
`Mathlib.CategoryTheory.Monoidal.Limits.Colimits`, and `Mathlib.Algebra.Field.ULift`.
Their modules remain reachable elsewhere; globally pruned modules remain none.


No original public imports were removed. No existing module is withdrawn.

The assigned proof no longer directly imports the planned generic affine weakly
contractible covering-family module: singleton affine contractible extensions of the
affine open cover give the required small universe directly. It needs no separate
finite-compositum lemma for all matrix entries, because each entry is retained in the
bounded-function ring and their common-stage descent belongs to the parent theorem.
It imports no generic continuous-field presentation or corank theorem; the required
finite-free evaluation and matrix-cokernel dimension argument are proved locally with
the coefficient field in its original small universe.

The original node's direct proof edges to
`lem-weil-pbc-proetale-affine-wcontractible-covering-family`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`def-weil-weakly-etale-morphism`, `def-weil-finite-subextension-directed-set`,
`def-weil-proetale-inverse-image`, `lem-weil-pbc-profinite-point-pullback`,
`lem-weil-pbc-condensed-point-basis-evaluation`, and
`lem-weil-pbc-geometric-field-proetale-evaluation` are replaced by the affine contractible
extension theorem and the new coefficient theorem. Some of the old nodes remain
transitive dependencies of the coefficient constructions; this is not a claim that
those modules have been removed from the targets' import closure. Globally pruned
modules: none.

The second reading removed eleven redundant imports from the new coefficient module:
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`,
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
`Mathlib.Algebra.Category.ModuleCat.Basic`,
`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`,
`Mathlib.CategoryTheory.Monoidal.Limits.Colimits`,
`Mathlib.Analysis.Normed.Module.FiniteDimension`,
`WeilConjectures.CategoryTheory.ModuleObjects.MapMod`,
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, and
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
Their required declarations remain available through the retained public dependencies.
`Sheaf.Paper.GeometricFieldProEtaleEvaluation` is now a plain import: only proofs
of cover splitting and colimit preservation use it. The totally disconnected-space
instance import remains public because the exposed coefficient constructions need it.
These are import-list cleanups, not additional modules pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The retained delivery copied private coefficient helpers already present in the
matrix-refinement consumer. The first dry run did not detect their duplicate
statements; the landing checker did. The full repaired overlay further exposed three
coordinate-lemma textual matches whose different universe binders were implicit;
the repair now writes those binders explicitly. Consolidating the whole shared construction
in the lower coefficient module fixes the actual duplication, preserving the
canonical normalized realization and the existing unit route.


The scalar interface needs weak contractibility only over the affine cover scheme itself.
The contractible extension theorem supplies this directly, so no passage from weak
contractibility relative to X to weak contractibility in the localized site is needed.

The planned generic affine weakly contractible cover has a larger index universe than
the cover demanded by the assigned statement. The direct affine contractible extension
construction resolves this without changing the statement.

The previous continuous-field matrix/corank argument cannot be imported here: its
coefficient universe is tied to the scheme universe, whereas the algebraic closure of
the l-adic field in this statement is small. The local finite-free evaluation proof
separates these universes and includes empty matrices and zero dimensions.

The old inverse-image node's current Lean attachment concerns a different finite
coefficient transport interface; the proof uses the existing normalized condensed
coefficient inverse-image API directly.

The cited `literature/upstream-master-20261014/WeilConjectures/RefactorInstruction.tex`
was unavailable locally, and the checked upstream raw URL returned 404. The source
attributions and natural-language steps are retained from the assigned node and the
existing declarations; this report does not claim a fresh reading of the missing file.

## New nodes

- `lem-weil-pbc-condensed-qbar-function-coefficients`, module
  `Sheaf.Paper.CondensedQbarFunctionCoefficients`: explicit canonical coefficient,
  scalar and geometric-fiber constructions, followed by the remaining four coefficient
  naturality/basis properties. Its source, full proof in words, searches, blueprint
  ancestry and Lean attachment are recorded in the node and the theorem docstring.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: pass.** I compared the delivered item with the repository
   using a full diff and the delivery declaration parser. The statements, visibility,
   bodies and docstrings of `condensedQbarFunctionEval` and `condensedQbarFunctionComp`
   are identical. For `exists_condensedQbar_compatible_function_presentations` only
   the proof body changes; its prime, scheme universe, noetherianity, weak etaleness,
   coefficient comparison, module and finite-presentation hypotheses, cover universe,
   fixed matrix dimensions, fiber equivalence and every-open presentation conclusion
   are unchanged. All added helpers in this existing module are private. The scope
   change record explains the additional universes and closed helper sections.

2. **Proof and data: pass, with the declared remaining hole.** Both delivered modules
   compile through lcompile.py after the import cleanup. The only remaining admitted
   proof is the entire named public theorem
   `condensedQbar_canonical_coefficient_properties`; no definition contains an
   admission and there are no forbidden declarations. I read the coefficient
   constructions, including the ULift transport, sifted-colimit multiplicativity,
   bounded multiplication, tensor-action ordinary-module conversion, algebraic-closure
   pullback and regular coordinates. `condensedFieldContinuousMapIso` upstream is
   selected by an explicitly unique normalized comparison, not arbitrary existence.
   The fiber-data record is constructed before the admitted property proof; the
   latter supplies proofs only and cannot choose its scalar or fiber data.

3. **Remaining statement and searches: pass.** Its four fields assert scalar
   surjectivity on the affine weakly contractible basis, restriction conjugacy,
   point evaluation of scalars, and natural comparison above the same base point.
   These are genuine coefficient obligations: there is no input P, finite
   presentation, cover, matrix, rank or freeness conclusion. I checked the statement
   against the expanded property record, its complete proof docstring, and its new
   DAG node. I reread the uniquely normalized comparison in
   `CondensedFieldContinuousRealization`, the terminal splitting/finite-colimit
   theorem and arbitrary algebraically closed extension comparison in
   `GeometricFieldProEtaleEvaluation`, and the actual component quotient and two
   naturalities in `CondensedPointBasisEvaluation`. They supply the stated arguments;
   the explicit scalar action must still be identified with those comparisons.
   The missing RefactorInstruction source remains an explicitly reported limitation,
   not a claim to have reread it. Independent LeanFinder, Loogle and grep searches
   used regular-module endomorphisms/sections and geometric-point scalar pullback,
   rather than the first worker's queries. LeanFinder found
   `SheafOfModules.unitHomEquiv` and free-module Hom equivalences for ordinary
   module sheaves; these do not identify the specified internal coefficient action
   or its pullback. Loogle found the generic regular object only. Project/upstream
   grep found the bounded coefficient definitions and the private tensor-action
   implementation, but no replacement for the four-field statement. The existing
   `Mod.regular_hom_ext` supplies generic uniqueness, not coefficient-section
   realization or geometric compatibility. No duplicate new node is needed.
   I checked empty spaces (both bounded functions and regular endomorphisms form
   the zero ring, and there are no point clauses), singleton field spectra
   (bounded evaluation is bijective since each scalar is algebraic), identity
   restrictions/comparisons, and rank-zero/empty matrix cases. The remaining
   four-field theorem is substantial and cannot be closed by a short application
   of the searched declarations. The one-for-one decomposition is reported honestly.

4. **Route and pruning: pass after import cleanup.** The main proof actually builds
   the small cover by binding singleton affine contractible extensions to the affine
   open cover; it obtains weak contractibility over each member itself by the identity
   specialization of the extension theorem. The finite-free pullback isomorphisms
   conjugate the map in the correct direction, its components reconstruct the matrix,
   and scalar restriction gives every open's presentation. The additive fiber functor
   preserves the cokernel; the coordinate identity uses the (row k, column j) entry,
   and rank-nullity computes n minus rank. Same-base-point fiber comparison then
   gives equal finite quotient dimensions and a linear equivalence. The finite index
   arguments admit zero dimensions. All nine removed old proof edges are listed in
   No longer needed, including those retained transitively. No original public import
   is removed, no whole module is claimed pruned, and the realized statement/steps in
   `dag/units/sk-thm-properbasechange.json` remain untouched. These changes are below
   the unit level and preserve coefficient realization before rank descent and minors.

5. **DAG agreement: pass.** The existing node changes only `proof`, `proof_deps` and
   `proof_origin`; its statement, statement dependencies, source, Lean signature and
   review fields are unchanged. Its two direct dependencies are exactly the affine
   extension and new coefficient interface used by the proof. The new coefficient
   node expands the same four properties of the concrete constructions, supplies the
   source, full argument, searches, parent blueprint place, creation data, chapter,
   unit and verbatim Lean attachment. Its proof dependencies cite the coefficient
   realization, point pullback, basis evaluation and geometric-field comparison
   statements read above. No unit realization is removed or bypassed.

Changes made by this reading: removed eleven redundant coefficient imports, made
geometric-field evaluation a proof-only import, and removed an unused local copy
of the finite-field normalization theorem from the coefficient-isomorphism construction.
No statement, definition data, remaining theorem, or hole count was changed.

Independent verification completed: the scratch axiom/edge-case file compiles in
2.9 seconds and the unchanged direct consumer compiles against this delivery overlay
in 10.6 seconds. Explicit axiom prints for the global coefficient isomorphism and its
test normalization, transported scalar action, component quotient equivalence,
presheaf scalar surjectivity, constructed fiber, its colimit preservation and regular
coordinates show only `propext`, `Classical.choice`, and `Quot.sound`. The remaining
coefficient theorem and main theorem additionally show the expected `sorryAx`.
The scratch checks certify the empty-space bounded-function case, bijectivity of
component descent, and zero-dimensional matrix quotients; no scratch file is delivered.


## Second reading by H3

1. **Existing interfaces: pass.** I read all three delivered modules and compared
   both existing modules with their repository versions using full diffs and
   `stage3_delivery.decl_table`. Every retained existing declaration has identical
   statement text, visibility and docstring; the item's two public function
   definitions have identical bodies. In matrix refinement, the only retained proof
   change supplies `globalCoefficientIso` from the lower module. Its deleted ten
   declarations are all private and have no external users. The two change records
   declare the helper scopes and this consolidation. The explicit coordinate binders
   really generalize the independent coefficient universe: the old corank module
   fixes `E : Type u`, whereas these helpers permit `E : Type uE` independently of
   `ModuleCat.{u + 1}`. No target, public definition, or existing theorem changes.

2. **Proof and constructed data: pass with the listed admission.** Fresh compilation
   through `lcompile.py --all` succeeds without warnings: coefficient construction
   41.8 s, function presentations 22.2 s, matrix refinement 9.2 s. The sole textual
   admission is the entire named public theorem
   `condensedQbar_canonical_coefficient_properties`; no definition is admitted and
   no forbidden declaration or option occurs. I checked the finite-field transport,
   diagram naturality, multiplicative colimit comparison, presheaf multiplication,
   sheafification, ordinary tensor-action module construction, and geometric fibers.
   The upstream continuous-field isomorphism is characterized uniquely by its test
   equations. The admitted theorem supplies only properties of already fixed data.
   Fresh axiom prints for the global realization and normalization, transported
   scalar, component equivalence, presheaf scalar surjectivity, field coefficient
   identification, fiber, its finite-colimit preservation, and regular coordinates
   show only `propext`, `Classical.choice`, and `Quot.sound`. The admitted properties,
   item theorem, and matrix-refinement theorem additionally show the expected
   `sorryAx`. This remains a decomposition, with one old hole closed, one new hole
   added, and net zero holes closed.

3. **Split statement, small cases and search: pass.** I expanded the four property
   fields and compared them with the node and full proof docstring. Scalar
   surjectivity, restriction conjugacy, scalar point evaluation and comparison over
   a common base point are true coefficient obligations; they do not repeat a
   finite-presentation, cover, matrix, rank, or freeness conclusion. Algebraic
   closures over the same base residue field admit a common algebraically closed
   overfield, and the published geometric-field comparison applies naturally to all
   sheaves. Its compatibility with the fixed coefficient normalization remains part
   of the declared obligation. I reread `CondensedFieldContinuousRealization`,
   `CondensedPointBasisEvaluation`, `GeometricFieldProEtaleEvaluation`, and the
   generic regular-module API. Independent LeanFinder, Loogle and grep searches for
   endomorphisms of regular module sheaves, terminal sections and inverse-image
   compatibility found `SheafOfModules.unitHomEquiv` and related naturalities, but
   not the bounded internal-module coefficient properties. Project grep found
   `Mod.regular_hom_ext` and the regular scalar-extension comparison, which give
   generic uniqueness rather than the missing coefficient identifications. No
   split-off theorem can be closed by a short use of these results. A fresh scratch
   file compiles checks for empty bounded-function rings, bijective component
   descent, singleton field-spectrum evaluation, identity precomposition, and
   zero-row matrix quotients. Identity restrictions and same-point comparisons
   also satisfy the stated properties. The missing RefactorInstruction source is
   still the explicit source-access limitation already reported above.

4. **Reduction, route and pruning: pass.** The proof uses a small cover obtained
   from the affine open cover and singleton affine contractible extensions. Applying
   the extension property to the identity gives the exact local weak-contractibility
   predicate needed. The finite-free pullback comparisons reconstruct each matrix
   and its open restrictions; additive finite-colimit-preserving evaluation and
   regular coordinates identify its ordinary value matrix. Rank-nullity and finite
   dimensionality yield the required linear equivalence, including zero sizes. All
   original unused direct proof edges are listed above, and the complete removed
   import inventory is now explicit. The new module's public imports support its
   exposed definitions or property signatures; geometric-field evaluation is a
   proof-only import. The matrix-refinement consumer reuses the shared construction
   without an import cycle. The unit's `realized` statement and all three step sets
   in `sk-thm-properbasechange.json` are unchanged; no unit step is bypassed. No
   whole module is claimed pruned.

5. **DAG and downstream agreement: pass.** Both existing node files change only
   `proof`, `proof_deps`, and `proof_origin`. Their statements and Lean attachments
   are unchanged. In all three nodes the union of step uses equals `proof_deps`.
   The item's two dependencies are the actual affine-extension and coefficient
   interfaces used. Matrix refinement adds the shared coefficient dependency and
   describes reuse of its explicit realization. The new coefficient node supplies
   its source, complete argument, three kinds of search (and LeanSearch), creation
   and blueprint ancestry, chapter, unit, and verbatim remaining theorem signature.
   Its four properties agree clause by clause with the Lean record. The unchanged
   direct consumer `CondensedQbarLfpLocalTriviality` compiles against the fresh full
   overlay in 2.7 s; the axiom and edge-case scratch file compiles in 2.7 s.

Changes made by this reading: completed the exact removed-import inventory in this
report and replaced the stale instruction about the prior reading with a pointer to
this current review. No Lean proof, signature, construction, node, or hole count
needed further repair. Scratch checks are not delivered.
