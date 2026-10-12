## What changed

Proved `AlgebraicGeometry.Etale.cohomology_continuity_of_isLimit` in
`Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`, with its signature unchanged.
The first conjunct uses the new class-descent theorem. The second conjunct is a
complete Lean argument: undo the composition isomorphism, restrict to `Over j`,
use initiality to retain the limit, apply the existing cofiltered cohomology
cocone, use the filtered-colimit element criterion to obtain a later zero class,
and transport that zero through the stage composition isomorphism.

The proved private helper `finiteStageKilling` implements the filtered-colimit
argument already used in `WeilConjectures.SixFunctors.Etale.Gabber`. Importing
Gabber was checked and would create an import cycle; its existing lower-level
cocone theorem can be imported. No existing declaration or definition changed.
The local transparency settings keep dependent pullback elaboration within the
single-file compilation limit; no heartbeat increase remains.

Added `Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent`, containing only the
strict surjectivity part of the original two-part argument, and its new DAG node.
Its complete proof in words includes the Ext/derived comparison, finite skeleton
and cocycle descent, and the identification of the canonical comparison maps.
Updated the original node's proof, proof_deps and proof_origin to the Lean route.

## Proved and sorry left

Proved in the item: `AlgebraicGeometry.Etale.cohomology_continuity_of_isLimit`.
Its original one sorry is removed. The private helper `finiteStageKilling` is
also fully proved. No sorry remains in the item's module.

One sorry is added, exactly as the whole proof of the public theorem
`AlgebraicGeometry.Etale.exists_cohomology_class_of_isLimit`, in
`Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent`, node
`lem-weil-pbc-etale-cohomology-class-descent`. It proves only descent of arbitrary
limit classes and contains no eventual-vanishing conclusion. The original
injectivity conjunct is proved separately, rather than moved to another sorry.

The proof still depends on the existing sorry-bearing declaration
`AlgebraicGeometry.Etale.exists_cofiltered_etale_cohomology_cocone`
(node `lem-weil-pbc-cofiltered-etale-cohomology-cocone`); that theorem is not
changed or duplicated by this delivery. The target is reduced, not axiom-free.

Edge cases were checked against the statements and argument: all q including 0,
zero sheaves, empty schemes, and a one-object index are retained. `IsCofiltered`
ensures a nonempty index. `Over j` contains the identity stage, and its initial
forgetful functor preserves the limit. The later arrow really has codomain j.
There is no torsion preservation assumption on the stage pullback: the
cofiltered cocone theorem accepts arbitrary abelian sheaves.

Both modules compiled locally in import order without errors or warnings.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.Paper.FiniteHypercoverDescent`
- `Sheaf.Paper.FiniteSplitHypercoverRefinement`
- `Sheaf.Paper.HypercoverCohomology`
- `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity`

The corresponding original proof dependencies
`lemma-weil-pbc-finite-hypercover-descent`, `lem-weil-pbc-hypercover-refinement`,
`thm-weil-pbc-hypercover-cohomology`, and `lem-weil-pbc-etale-section-continuity`
are no longer direct dependencies of the continuity node. They remain in the
proof plan of the new class-descent node, and are not claimed globally pruned.
The injectivity proof no longer needs any hypercover cocycle, refinement,
primitive, or boundary descent argument. No unit statement or unit proof step
is bypassed: `dag/units/sk-prop-h2.json` has no realized node binding for this
continuity lemma, and its Kummer argument is unaffected.

New proof imports in the item are the class-descent module, the existing
cofiltered cocone module, Mathlib's filtered initial-functor and concrete
filtered-colimit APIs, and the existing cohomology isomorphism-injectivity API.
All original public imports are retained. No unused new proof import remains.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original hypercover cohomology theorem is
stated for derived global sections, whereas this item uses `Sheaf.H` (Ext).
The remaining class-descent proof must identify these encodings and their
pullback maps; this bridge is now explicit in its docstring and DAG proof,
using the existing Ext-via-resolution leaf and derived-unit comparison node.
The finite skeleton must also be extended at the descended stage; this is
explicit in the new proof plan.

The existing cofiltered cocone theorem is useful for finite-stage killing but
only specifies its cocone maps on classes restricted from a fixed base. It
does not by itself identify a cocone leg on an arbitrary stage class. Therefore
it cannot be used to claim surjectivity here without additional comparison work.
Gabber cannot be imported into this module because it already reaches this item.

Searches: LeanFinder returned structure-sheaf section continuity and finite-type
morphism descent, not etale cohomology class descent. Loogle's unqualified
`IsColimit` query had no hit; the source API was inspected directly.
LeanSearch for class descent returned Internal Server Error and is recorded as
unavailable, with no inferred absence verdict. Grep of Mathlib's algebraic
geometry and sheaf-cohomology modules found no inverse-limit etale class-descent
theorem; library and blueprint searches found no separate theorem closing it.
Stacks Tags 03Q6 and 09YQ were read online; the imported blueprint node contains
the full finite-hypercover argument, while its referenced literature markdown
is not present in this machine's checkout.

## New nodes

`lem-weil-pbc-etale-cohomology-class-descent` states exactly the surjectivity
conjunct, retaining the original qcqs, affine-transition, limit, torsion and
degree hypotheses. It comes from proof step 1 of
`lemma-weil-pbc-etale-cohomology-continuity`. Its proof plan cites the existing
finite hypercover, section continuity, refinement, Ext resolution and derived
pullback comparison nodes. Three kinds of search are recorded, including the
LeanSearch service failure. It is a strictly smaller task than continuity;
there is no eventual-zero assertion. No change record is needed because no
existing public signature, definition or public import is changed.

## Second reading by K1

1. Interface: PASS. Read the full diff against the repository module. The existing
   theorem signature, from `theorem` to `:=`, is byte-for-byte identical; no existing
   definition or public import changes. The other delivered module is new and has
   exactly the surjectivity conjunct. No statement-change record is required.
2. Proof and axioms: PASS as a partial reduction. Independently compiled both modules
   through lcompile.py in import order (4.8 s and 40.7 s), without errors or warnings.
   Compiled scratch copies with `#print axioms` for finiteStageKilling,
   cohomology_continuity_of_isLimit and exists_cohomology_class_of_isLimit. All three
   report only propext, Classical.choice, Quot.sound and sorryAx. The helper uses the
   existing open cocone theorem; continuity additionally uses the new open descent
   theorem. The only direct sorry delivered is the whole proof of that public named
   descent theorem. No forbidden declaration or hollow definition is introduced.
3. Split statement: PASS. It is a proper part of the original conjunction, retaining
   all its hypotheses and its canonical comparison. Its docstring supplies the
   finite-skeleton and cocycle descent argument, including the Ext/derived comparison
   and pullback compatibility; its node records the corresponding existing nodes.
   The Ext-resolution node is a Mathlib match, not an unstated missing dependency.
   Checked degree zero (section descent and degree-one gluing), zero sheaves, empty
   schemes, and a one-object category. Cofilteredness excludes an empty index, and
   Over i and Over j each have their identity object. Checked Stacks 09YQ and 03Q6:
   09YQ supplies the general directed-system result; 03Q6 is its base-change special
   case. Independent LeanFinder, Loogle and source grep searches found no directly
   applicable class-descent theorem. The cofiltered cocone's restricted comparison
   equations do not justify applying its surjectivity to claim canonical class
   descent. Closing that comparison and the hypercover reduction is not a short
   proof repair, so the split theorem remains open.
4. Route and pruning: PASS. Read the vanishing argument from the original kernel
   equation downward: injectivity of the composition isomorphism, the initial
   restriction to Over j, the existing cocone, and the filtered-colimit equality
   criterion. The resulting object supplies an actual arrow into j. Each new proof
   import supplies a used API; all are plain imports. All four old direct proof
   dependencies are listed under No longer needed, and remain dependencies of the
   split descent node; no globally unreachable module is claimed pruned. Read
   dag/units/sk-prop-h2.json: realized.statement and its sole realized.steps entry
   are empty. This reduction bypasses no bound unit statement or proof step.
5. Node agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Its two proof dependencies are exactly the descent and cofiltered
   cocone nodes used by the Lean proof. The new node has its source, complete proof
   plan, dependency union, search records, creation and blueprint provenance, correct
   chapter/unit and verbatim Lean signature. Existing dependency declarations and
   the Mathlib Ext-resolution match were inspected.

Second reading changed only this report and the new node's search evidence. The
Lean proof and statements needed no repair. Scratch axiom-check copies were removed.
Source checks: https://stacks.math.columbia.edu/tag/09YQ and
https://stacks.math.columbia.edu/tag/03Q6.
