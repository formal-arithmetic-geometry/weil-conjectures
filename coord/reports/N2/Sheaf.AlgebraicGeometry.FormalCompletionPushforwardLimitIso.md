## What changed

Added `FormalCompletionPushforwardLimitAppBijective.lean`, isolating the affine-section step, and used `Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen` to prove the original limit-sheaf isomorphism theorem.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.formalCompletion_pushforward_limit_isIso`.
Hole added: `AlgebraicGeometry.formalCompletion_pushforward_limit_app_bijective`,
node `lem-weil-pbc-formal-completion-pushforward-limit-app-bijective`.
This is a decomposition: one upper hole closed and one lower affine-calculation hole
added, net zero holes. The parent proves the passage from affine sections to a sheaf
isomorphism using the existing upstream affine-basis criterion. It is not an axiom-free
proof of the original assertion: its axiom list still contains `sorryAx`.

## No longer needed

Removed the parent's direct proof imports `Sheaf.AlgebraicGeometry.TheoremFormalFunctions`
and `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`: they are
needed only by the new affine-calculation module, which imports them privately.
The corresponding old proof dependencies `lem-weil-pbc-theorem-formal-functions` and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` move to that new node; they
remain transitively needed, so no module is pruned from the target closure.
The manual sheaf-gluing step is discharged by the upstream library criterion
`Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen` (not a Mathlib declaration).

## Where the brief, the DAG or earlier work was wrong

The original DAG proof omitted the existing affine-basis isomorphism criterion and left its affine comparison as an implicit long argument. No statement was changed.

## New nodes

`lem-weil-pbc-formal-completion-pushforward-limit-app-bijective` records the strictly simpler affine-section substatement left for parallel proof.

## Earlier second reading (a previous round; superseded)

Pending independent second reading.

## Second reading by N2

1. Compared the entire original module with the repository version by `diff` and
checked the existing theorem signature byte for byte. It is unchanged; no definition,
public import, visibility, target statement, or declaration signature changes. The only
Lean edits to the existing module are private proof imports and its theorem proof.

2. Compiled both modules using `lcompile.py --all`, then compiled scratch copies with
`#print axioms` for both declarations. Both lists contain exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The sole textual sorry is the new
named public theorem; no axiom, unsafe, opaque, extern, implemented_by, or data
construction is introduced. The parent applies the upstream affine-basis criterion
to precisely the map and affine-section hypothesis it requires.

3. Read the new theorem, CoherentFormalModule's explicit cokernel definitions,
`ideal_times_quasiCoherent_affine_sections`, `globalSections_formal_functions`,
and `formalModuleQuotient_affine_projection`. Read Stacks 02OC
(https://stacks.math.columbia.edu/tag/02OC) and the completion identification in 088B
(https://stacks.math.columbia.edu/tag/088B). No extra hypothesis from 088B is needed
for this degree-zero consequence of 02OC. Noetherianity gives Noetherian affine
coordinate rings; properness and coherence persist under restriction; coherence of
H supplies the affine quotient formula. Surjectivity of its quotient projection
makes hκ determine the canonical comparison, rather than an arbitrary isomorphism.
Checked zero ideal (constant systems), unit ideal (zero systems), zero module and
empty open (zero sections). The lemma calculates only the sections on a specified
affine open; the parent's existing criterion supplies the separate sheaf step.
This is a true, needed subargument, not an identical renamed sheaf-isomorphism claim.
Fresh leanfinder, loogle and grep searches are recorded in searches.jsonl; direct rg
of lean/Sheaf and upstream WeilConjectures found the ingredients above but no complete
comparison theorem. The chart and quotient identifications require substantial Lean
work, so this hole could not responsibly be closed in a few minutes.

4. Read the upstream criterion's proof in Modules/LocallyFreeAffine: it uses the affine
basis sheaf criterion and reflection of isomorphisms. This is the short route for the
parent; no manual gluing is needed. Removed the parent's two unused direct imports.
The new module retains the private imports of its planned proof dependencies. Listed
both old proof dependencies above, including their continued transitive use. Read
`dag/units/sk-thm-p1.json` realized: this off-unit local calculation replaces none of
its statement or step nodes, so the unit route is preserved.

5. The first delivery omitted the updated parent node; supplied it with the actual
new affine dependency and upstream criterion step. The new node incorrectly used
the parent assertion as a statement dependency, was not self-contained, lacked
blueprint same_as, and claimed searches not matching the log. Replaced that dependency
with the three defining nodes, wrote all hypotheses in its statement, used the parent's
nearest blueprint ancestor, filled same_as, and recorded the searches actually
run. Its Lean statement is copied verbatim from the declaration. Both nodes now agree
with the Lean and distinguish the local formal-functions calculation from sheaf gluing.

Changes made: expanded the new lemma's short proof docstring into the full restriction,
quotient, canonical-map and limit argument; removed two unused parent imports; repaired
the new node and supplied the parent proof record; corrected the report to count a
one-for-one decomposition and identify the criterion as upstream rather than Mathlib.
No existing statement or definition was changed.

Preflight initially required LeanSearch as a search kind; ran it and recorded its
Internal Server Error as unavailable, not as a negative search result.
