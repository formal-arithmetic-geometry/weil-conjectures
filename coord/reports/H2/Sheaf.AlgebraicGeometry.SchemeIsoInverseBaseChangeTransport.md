## What changed

Proved `AlgebraicGeometry.schemeIso_inverseBaseChange_transport` in
`Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport`, with its signature and
visibility unchanged. Constructed the normalized comparisons `k`, `q`, and `σ` explicitly.
Local proved helpers establish conjugate-counit compatibility, source-coordinate mate
transport, and the pullback-comparison square; their categorical calculations adapt the
already proved helpers in `DerivedBaseChangeSourceIso`. A constructed unit comparison
restricts these maps to the full quasi-coherent subcategories. Pullback composition and
identity comparisons give the equivalence needed to prove `IsIso q`. The ordinary-square
identity is then converted to the inverse-square identity by actual inverse cancellation.

Removed the proof import `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting` and added
`Mathlib.CategoryTheory.Adjunction.FullyFaithful` for invertibility of adjunction units.
Updated the item's DAG proof and proof dependencies to describe this direct route.
The complete module compiled cleanly through `lcompile.py` in 45.2 seconds against the
published build, without warnings. Broader transparency is scoped to the local categorical
helpers and two final proof steps; the existing declaration and file settings are retained.

## Proved and sorry left

Closed: `AlgebraicGeometry.schemeIso_inverseBaseChange_transport`
(node `lem-sc-scheme-iso-inverse-base-change-transport`), the module's sole original hole.
Holes added: none. Sorries left in delivered modules: none. No intermediate statement is
split off. The local helpers and comparison construction are all complete Lean proofs or
explicit data constructions. Existing upstream proof dependencies retain their existing
trust status; this delivery does not claim the entire targets' closure is sorry-free.

## No longer needed

Removed import and proof dependency:
`Sheaf.AlgebraicGeometry.DerivedBaseChangePasting`, node
`lem-pc-derived-base-change-pasting`, declaration
`AlgebraicGeometry.schemeDerivedBaseChange_pasting`.
The proof uses direct source-coordinate mate algebra instead of that pasting theorem.
This removes this item's dependency edge; other users may still need the module.

The theorem `AlgebraicGeometry.dualityEquationBaseChangeMap_eq_inverseSquareMate` is not
applied: `QCohInverseBaseChangeMate` stays publicly imported because its definitions
`qcPullback`, `qcDirectImage`, `qcBaseChange`, and `qcInverseBaseChange` are required by the
unchanged statement and proof. No unit-level statement or step is bypassed: the unit's
`realized` lists do not pin this below-unit argument to a particular auxiliary route.

## Where the brief, the DAG or earlier work was wrong

The original docstring and DAG proposed applying derived base-change pasting. The proved
source-coordinate calculations in `DerivedBaseChangeSourceIso` give a direct route using
only composition coherence and the pinned adjunctions. Its public existential theorem
does not expose the normalization formulas required here, so its proved local categorical
calculations are adapted inside this module rather than its module being imported.
The statement is unchanged; no false statement, interface correction, forced adaptation,
or hollow definition was found or introduced.

Searches run through `msearch.py`: LeanFinder for invertibility of an equivalence
adjunction's unit found the Mathlib fully-faithful adjunction instances; Loogle for
`CategoryTheory.conjugateEquiv` found the conjugation API; reading `Mates.lean` supplied
the conjugate-counit and unit identities. Grep and
repository searches located `DerivedBaseChangeSourceIso` and existing scheme-isomorphism
pullback equivalence constructions. These searches yielded the direct route above.

## Second reading by H2

1. Interface: PASS. Diffed the delivered module against the repository module and
   compared the complete existing theorem signature byte for byte: identical.
   The qcqs scheme assumptions, both qcqs map assumptions, source isomorphism,
   both projection equations, IsIso r, both base-change invertibility hypotheses,
   pinned adjunction/composition choices, inverse-square equation, and all three
   component normalization clauses are retained. The sole public import remains
   QCohInverseBaseChangeMate; the import changes are proof-only. No definition
   used by another module changes and no change record is needed.
2. Proof: inspected all four private categorical lemmas, the explicitly constructed
   qcUnitComparison, and the final theorem proof. There is no sorry, axiom, unsafe,
   opaque, implemented_by, extern, or kernel-check bypass in the delivery. The
   conjugate-counit calculation uses the triangle identity; mate transport uses
   injectivity of the Hom equivalence; the pullback square follows from the three
   associativity identities and equality-transport naturality. The unit comparison
   has explicit components and an explicit naturality proof. The final inverse
   square follows by postcomposition with the upper inverse and cancellation of
   the lower base-change component, with both invertibility hypotheses used.
   No arbitrary witness of a mere unproved existence statement supplies k, q, or
   sigma. The unchanged pinned choices come from the existing derived universal
   property and the adjunction with prescribed counit. The identity comparison
   used locally only establishes full faithfulness and hence the proposition
   IsIso q; it does not select any of the output comparisons.
3. Split-off statements: PASS, none. All private helpers are proved. Checked the
   identity-isomorphism case, zero objects, and empty schemes: the argument uses
   only categorical identities and no nonemptiness or nonzero assumption.
   Independent Loogle search for "CategoryTheory.Adjunction,
   CategoryTheory.conjugateEquiv" confirmed the generic mates API. LeanFinder
   search for "naturality of adjunction mate under composition of pullback
   functors" returned chosen-pullback slice-category results, not the normalized
   derived statement. Repository grep located DerivedBaseChangeSourceIso and
   DerivedBaseChangeCodomainIso; the former's public existential theorem does
   not prescribe the comparisons here, while its reusable calculations are
   private. No shorter applicable public declaration was found.
4. Route and pruning: PASS. QCohInverseBaseChangeMate is required publicly for
   the signature; Adjunction.FullyFaithful is a proof-only import needed for the
   unit-isomorphism instance. DerivedBaseChangePasting is the sole removed old
   proof dependency and is listed above. The retained inverse-square-mate module
   supplies the qc functors and transformations rather than an application of its
   second-mate theorem. Checked dag/units/sk-thm-picard-duality.json: its statement
   and step realized lists are empty, and this below-unit auxiliary calculation
   changes no unit statement, step, or route. The original docstring still mentions
   the old pasting plan; the report and updated node describe the actual direct
   calculation instead.
5. Nodes: PASS. Diffed the existing node: only proof, proof_deps, and proof_origin
   change. The three new proof steps match construction, ordinary transport, and
   inverse cancellation in Lean. Their uses union equals proof_deps, with the
   removed pasting edge absent. No new node or statement correction is present.

Second reading simplified two proof steps to reduce unnecessary elaboration:
the unit-invertibility proof now obtains full faithfulness directly from the two
composition/identity isomorphisms, using Mathlib Functor.Faithful.of_comp_iso and
Functor.Full.of_comp_faithful_iso, instead of constructing Equivalence.mk. The
postcomposition formula for q is now one application of Category.assoc instead
of simplifying the constructed transformation. The sigma calculation still uses
the equality-transport lemmas; reflexivity alone does not establish that formula.
No existing signature, public visibility, comparison data, or proof dependency
changed in this second reading. The DAG's first proof step was adjusted to match
this direct full-faithfulness proof. No mathematical error or new hole was found.

Verification: the revised delivered module compiled without warnings through
lcompile.py in 58.9 seconds. The initial proof also passed the delivery tool's
local compile, axiom probe, and preflight (CODEX: changes a node file); several
other compile attempts reached the unchanged 60-second limit. Final axiom and
delivery verification follows below.

The scratch copy containing #print axioms compiled cleanly in 59.7 seconds.
AlgebraicGeometry.schemeIso_inverseBaseChange_transport reports exactly propext,
Classical.choice, Quot.sound, and sorryAx. The sorryAx is inherited from open
upstream dependencies; the delivered module contains no sorry. This is one
closed local hole and zero added holes, rather than a claim that the entire
import closure is already proved without sorryAx.
