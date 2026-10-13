## What changed

Proved the body of
`AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns_odd`, with its signature and
visibility unchanged, from a new single-open stage presentation. Added proof-only imports
`Mathlib.Algebra.Category.Grp.FilteredColimits` and
`Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation`. All existing public imports stay.

The main module now proves a private generic colimit-recognition lemma. It constructs the
underlying canonical abelian-group colimit cocone, proves it is a set colimit using preservation
of filtered colimits (including the universe shrink), and proves the local-comparison pinning
identity from `colimit.ι_desc`. This construction does not choose data from an existence theorem.
The public proof derives compactness and image containment of the intersection, classifies the
index into 1 or 4, and uses `PerfectHomMVFamily.map_hom₃` to identify the actual row transitions
and cocone legs at shifts -1 and 0. The local-map conclusion follows by the `basic` constructor.

The new module has one theorem, `AlgebraicGeometry.perfect_hom_open_stage_presentation`.
It supplies the stage/apex Hom equivalences and their transport equations for an arbitrary
single compact open and arbitrary integer shift, without any Mayer--Vietoris family, group
colimit, directedness assumption, continuity, bijectivity or local-map conclusion. Its docstring
constructs the local objects by restriction and shifting and describes the remaining geometric
adjunction/restriction argument. This is the geometric part of the original argument, separated
from the colimit argument that is proved here, rather than the original conclusion renamed.

Updated the existing odd-column node's proof, proof dependencies and proof origin, and added
the node for the new theorem. The combined proof-dependency closure through the updated node
is acyclic (841 nodes checked). The unit record has no realized nodes for its statement or steps;
this work does not change the unit or its route.

Both modules compile locally via `lcompile.py`. The final delivery dry run performs the probes
and stage-3 preflight. No target, existing definition, existing signature or other holder's
module is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.perfect_hom_mayerVietoris_geometric_columns_odd`
(node `lem-pc-perfect-hom-mayer-vietoris-geometric-columns-odd`). No sorry remains in the
item module. The private `localComparison_of_stage_presentation` is fully proved.

Added one named whole-proof sorry:
`AlgebraicGeometry.perfect_hom_open_stage_presentation`
(node `lem-pc-perfect-hom-open-stage-presentation`), in its own new module.

Counts: one original hole closed, one lower hole added. This delivery is a decomposition,
not a net reduction of the number of holes and not an axiom-clean final proof. The lower
statement omits all colimit and triangle-row conclusions; the Lean argument from its stage
and apex equations to the two original colimit-map conclusions is complete.

Edge cases checked mathematically: W empty, zero perfect objects, arbitrary positive and
negative shifts, a non-surjective open immersion, and a ring cocone that is not a colimit.
The new theorem requires W contained in the image and no continuity or ring-colimit witness.
Its construction uses Z = (t inverse-image W).toScheme, its canonical inclusion composed
with t, P' = restricted P shifted by -n, and Q' = restricted Q. Empty opens yield zero Hom
groups. It asserts existence only within a theorem; no definition chooses an arbitrary witness.

## No longer needed

Removed no existing import and claimed no globally pruned module.

Removed `lem-pc-perfect-hom-mayer-vietoris-geometric-columns` as a proof dependency of this
odd-column node: the parent theorem is no longer used to prove its own prerequisite. Its
module `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisColumns` remains needed upstream.
The new proof also avoids a separate application of `perfect_hom_stage_colimit`; the actual
underlying group-colimit cocone already supplies the needed set-colimit witness. This does
not claim its module is globally unused, since other modules still depend on it.

Binary-product recognition, the two-open biproduct components, chosen boundary morphisms and
distinguishedness are not used for these odd columns. Their existing modules stay where the
unchanged public statement or the even-column argument requires them.

## Where the brief, the DAG or earlier work was wrong

The odd-column node's only planned proof dependency was its parent
`lem-pc-perfect-hom-mayer-vietoris-geometric-columns`. The parent Lean proof and its DAG
already depend on this odd-column theorem. Applying the planned dependency would therefore
be circular. The replacement dependency is the strictly lower single-open stage presentation.

The source files under `literature/stacks-project/` are absent on this machine. Read the
corresponding online primary sources: Stacks Tags 09RE, 079W, 08FE and 0D5S. Their local
restriction, derived adjunction and pullback-composition arguments justify the remaining
stage/apex presentation; 09RE supplies the open-local Mayer--Vietoris context.

Searches ran through `msearch.py` and repository ripgrep. LeanFinder found underived restriction
functors and comparisons, Loogle found `Scheme.Modules.restrictFunctorIsoPullback` and the
generic colimit-preservation API, and grep found local-comparison definitions and compact-open
intersection lemmas. No existing declaration gave the required pinned derived stage/apex Hom
presentation. LeanSearch returned Internal Server Error and is recorded as unavailable.
Blueprint searches for the single-open presentation and Mayer--Vietoris Hom gave no duplicate.

## New nodes

`lem-pc-perfect-hom-open-stage-presentation`, module
`Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation`, declaration
`AlgebraicGeometry.perfect_hom_open_stage_presentation`. This isolates the geometric single-open
Hom identification and its two naturality equations before passing to colimits. Its proof
constructs the local scheme and perfect pair, uses Yoneda and derived adjunction to identify
the representing system, restricts through the canonical open/direct-image comparison, and
checks the pinned pullback transport. It cites the existing definition, adjunction,
restriction/direct-image and pullback-composition nodes. No change record is needed: no
existing public interface changed.

## Second reading by F3

1. Compared both delivered modules with the repository versions. The existing target
   declaration has the same signature and visibility; the only changes are proof-only
   imports and proof text. The new declaration is recorded by its new node.
   Verdict: unchanged interfaces.
2. Compiled both modules with `lcompile.py --all`; both compile without errors. The
   target module has no `sorry`; the only remaining `sorry` is the named theorem
   `AlgebraicGeometry.perfect_hom_open_stage_presentation`, with its node and proof
   source documented above. No forbidden declarations or hollow definitions occur.
   Verdict: proof checks pass, with the documented split hole.
3. The added theorem is a strict geometric stage/apex presentation: it omits colimits,
   Mayer--Vietoris rows, and local-map conclusions. It is therefore not a restatement
   of the target. Its edge cases include empty opens and arbitrary integer shifts.
   Repository and search checks found no duplicate declaration. Verdict: statement is
   true as sourced and exactly as strong as needed for the reduction.
4. The proof uses the shortest available route for the outer columns: the single-open
   presentation, the canonical underlying filtered group colimit, `colimit.ι_desc`,
   and the basic local-map constructor. The parent geometric-columns theorem is not
   imported as a circular dependency. The old parent dependency was removed from the
   node proof route; no further import can be pruned without changing the statements.
   Verdict: route is pruned and acyclic.
5. The target node proof and proof dependencies match the Lean proof, and the new node
   records the split theorem, source, declaration, and module. The unit route is not
   altered: its `realized` record remains unchanged. Verdict: DAG and unit metadata
   agree.

Changed during second reading: added this review section only; no Lean declarations or
DAG statements were altered.
