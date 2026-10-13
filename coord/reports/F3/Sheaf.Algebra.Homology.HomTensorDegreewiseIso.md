## What changed

Proved the unchanged `CategoryTheory.homTensorDegreewise_inverse` from a new,
strictly smaller reverse-construction obligation. The reverse construction gives
only a morphism and its localized evaluation equation; it asserts neither inverse
identity and assumes no forward morphism. The item proves both identities for
every forward morphism satisfying the original equation, by actual product,
localized-Hom, tensor and sheafification extensionality calculations.

Added the proof-only imports `Sheaf.Algebra.Homology.HomTensorReverseConstruction`,
`Sheaf.Algebra.Homology.HomComplexProjections`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`. Public imports, existing
signatures and existing docstrings stay unchanged. No existing definition or
statement is changed and no downstream module is adapted. The static checker
classifies the private helper namespace and scoped commands as an interface
change; its conservative classification is documented in
`coord/changes/hom-tensor-degreewise-inverse-private-proof.md`.

Private helpers prove product-section and morphism extensionality, evaluation
under restriction, and localized tensor extensionality. The latter follows the
proved `HomTensorLocalizedExt` argument, with a more general private presheaf tensor-Hom API: the ambient
universe `w` is an extra parameter, and both coefficients and modules
live in `max u v w`. It cannot be imported: `import_direction.py` reports
that it already reaches this item through `HomTensorDegreewise`, so the import
would close a cycle. All private helpers are proved, with no new private holes.

The Mathlib searches found generic closed-category and external cochain APIs,
not this sheaf-valued degreewise inverse. LeanSearch was unavailable (HTTP 500),
recorded as unavailable. The site source was read at Stacks Tag 0A90 and its
explicit algebraic model Tag 0A5Y. The unit's route is preserved.

## Proved and sorry left

Closed the original hole in `CategoryTheory.homTensorDegreewise_inverse`
(node `lem-sc-hom-tensor-degreewise-iso`). No sorry remains in the item's module.

Added one hole: `CategoryTheory.homTensorDegreewise_reverse_construct`, in
`Sheaf.Algebra.Homology.HomTensorReverseConstruction`
(node `lem-sc-hom-tensor-reverse-construction`). Its proof is exactly `by sorry`.
Its full localized evaluation equation, source and construction proof are in
its docstring and matching node. It is only the construction step of the original
argument, not the original conclusion under another name.

This delivery is a decomposition: one hole closed, one hole added, net zero.
The inverse calculations and all extensionality/restriction glue are proved.
The proposed new statement was checked mathematically for zero complexes,
the zero coefficient ring, an empty site, arbitrary integer degree and independent
site universes. It has no boundedness or finite-support hypothesis and never
asserts global pure-tensor generation of sheaf tensor sections.

## No longer needed

No original import is removed. The old direct proof dependency
`lem-pc-sheaf-modules-tensor-closed` is no longer used by the inverse
calculations and is removed from the parent node's `proof_deps`; it remains
a dependency of the new reverse-construction node. No module is claimed pruned from the targets'
closure. The abstract tensor-closed theorem is not invoked by the item's inverse
calculations: their concrete presheaf tensor-Hom and sheafification argument is
proved locally. Its node remains a planned dependency of the reverse construction,
so it is not globally pruned. Four unused convenience
application lemmas from the copied private tensor-Hom API were omitted. The Hom product, total tensor, tensor comparison and
sheafification dependencies likewise remain needed.

## Where the brief, the DAG or earlier work was wrong

The previous missing shared artifact is now present. The earlier sandbox also
contained stale compiled copies of `HomTensorDegreewiseEquation` and an obsolete
reverse-construction module; those shadowed the shared library. These artifacts
were removed. Verification uses the published shared equation interface and only
the new module compiled from this delivery in the sandbox overlay.

The large chosen Hom-complex existence type needs the already-landed
`homComplex_projections_exists` interface for efficient elaboration. No interface
change was needed. The source tensor-Hom equivalence binds the site object,
site morphism and coefficient universes all to one universe; the item binds them
independently. The repaired private API now also permits a larger ambient coefficient/module universe.
The four reported lemmas (`IsoTensorHom.tensorHomCurryApp_app_apply`,
`IsoTensorHom.tensorHomCurryApp_add`, `IsoTensorHom.tensorHomCurryApp_smul`,
and `IsoTensorHom.tensorHomCurryApp_map`) explicitly bind
`R : Cᵒᵖ ⥤ CommRingCat.{max u v w}` and presheaves in `max u v w`.
The localized APIs fix `R` to `CommRingCat.{max u v}`. Thus these are genuine
universe generalizations, not renamed copies of identical statements.
Both existing localized APIs are private and their modules import this item
through `HomTensorDegreewise`, so importing them would create a cycle.
The source public API fixes every universe to one `u` and cannot serve the
independent site universes. The explicit binders make this distinction visible
to the duplicate-statement checker. All four generalized proofs remain complete.
No other module is adapted.

## New nodes

`lem-sc-hom-tensor-reverse-construction`, at
`dag/nodes/sec-picard-framework/lem-sc-hom-tensor-reverse-construction.json`,
states the reverse map and its evaluation equation, without any inverse identity.
Its module is `lean/Sheaf/Algebra/Homology/HomTensorReverseConstruction.lean`.
The construction curries each total-tensor summand and assembles the two Hom
products, then checks its equation by projection and evaluation. It supplies
precisely the construction part left unfinished; the parent node records the
complete inverse calculations using it. The change record is
`coord/changes/hom-tensor-degreewise-inverse-private-proof.md`; it explains the
checker's conservative classification of the private proof commands.

## Second reading by F3

1. Compared the complete existing module with the repository by diff and compared
   the `homTensorDegreewise_inverse` signature byte for byte: identical. Its
   docstring and public import are unchanged. Only private helpers, proof-only
   imports and its proof are added. The sole existing node changes only `proof`,
   `proof_deps` and `proof_origin`. No definition or target statement changes.
   Verdict: pass.
2. Compiled both delivered modules locally through `lcompile.py --all`, with no
   errors or warnings. Inspected every private construction and the two inverse
   calculations: all are complete proofs. The only delivered `sorry` is the
   named public reverse-construction theorem. No forbidden declaration or hollow
   definition is added. A scratch copy checks axioms of the inverse, reverse
   construction and the main private helpers. The inverse and reverse construction
   use only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the
   product, restriction, morphism-extensionality, tensor-extensionality and
   concrete tensor-Hom equivalence helpers use only the three allowed axioms.
   The delivery axiom probe and preflight also pass. Verdict: pass.
3. Read the reverse-construction statement, its complete construction docstring
   and its node against Stacks Tags 0A90 and 0A5Y. It asserts only construction
   and evaluation, neither composite identity; the delivered upper proof supplies
   both identities by substantial independent calculations. It is a genuine
   construction subproblem, not a renamed inverse theorem. Zero inputs, the zero
   ring and the empty site reduce to zero/unique maps. For a one-object site and
   single-degree complexes, it is ordinary bilinear currying. Arbitrary degrees
   use products, so no finite-support condition is missing. Further localized
   restriction is explicitly included. Additional LeanFinder search for bilinear
   sheaf currying/product assembly, Loogle search for MonoidalClosed.curry and
   local searches for curry/uncurry and reverse constructions found no exact
   existing declaration. Generic closed APIs do not identify this chosen
   product/localized evaluation interface. The source concrete API binds all
   universes to one; the already-proved localized private APIs cannot be imported
   here and have smaller universe signatures. The remaining construction would
   require assembling both product cones and their restriction equations; it is
   not a hole that can responsibly be closed in a few minutes. Verdict: pass as
   a decomposition, one hole closed and one added, net zero.
4. Checked from the inverse identities downward. The private product helper uses
   the proved projection specification; the second identity transposes to move
   the tensor out of the internal Hom, then uses coproduct extensionality,
   sheafification and presheaf tensor extensionality. No global generation of
   sheaf tensor sections is assumed. All four added imports serve these proofs;
   only the original equation import is public. Compared old and new dependency
   lists and checked the unit record: no realized unit step is bypassed or
   changed. No module is pruned. Verdict: pass; clarified the omitted old direct
   tensor-closed dependency in `## No longer needed`.
5. Read both node files against the Lean statements and proof. Each `proof_deps`
   equals the union of its proof steps' `uses`. The new node includes its source,
   full Lean signature, construction proof, searches, origin, creation record,
   blueprint ancestry, chapter and unit. The parent describes the actual
   restriction and tensor-extensionality calculations. Verdict: pass.

Changed only the report: explicitly named
`lem-pc-sheaf-modules-tensor-closed` as no longer a direct parent dependency
(it remains needed by the reverse construction), and added this second reading.
No Lean proof repair was needed.

Delivery dry run printed OK (commit `952fc39902`), review class CODEX,
including the repaired duplicate-statement return.
