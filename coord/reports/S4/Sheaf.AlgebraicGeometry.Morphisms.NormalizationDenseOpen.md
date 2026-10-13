## What changed

Proved AlgebraicGeometry.Scheme.isIso_fromNormalization_denseOpen with its existing
signature unchanged. The proof checks the section map on affine opens: restriction
is injective because X is reduced and V is dense; integral-section extension gives
surjectivity onto integral closure; Mathlib identifies the normalization section
map with this ring isomorphism and glues the affine isomorphisms.

Added the proved module Sheaf.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection,
with public theorem AlgebraicGeometry.Scheme.exists_integral_section_denseOpen and
three fully proved private helpers. Its proof transfers normality to open connected
components, extends generic germs using normal stalks, and glues the local sections.
The source-library FunctionField and Noetherian modules supply already proved tools.
All extra imports in the original module are proof-only. Updated the original DAG
node to match the implemented route and added the node for the proved extension lemma.

Both modules compile locally in under four seconds without warnings. The axiom check
for isIso_fromNormalization_denseOpen reports only propext, Classical.choice, and
Quot.sound. There is no sorry dependency in its proof. The empty chart, empty scheme,
and disconnected cases are covered by the same indexed-cover argument; no arbitrary
witness of an unproved existence theorem is chosen. No existing interface changed.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.isIso_fromNormalization_denseOpen
(lem-sbc-normalization-dense-open).

Also proved the newly added theorem:
AlgebraicGeometry.Scheme.exists_integral_section_denseOpen
(lem-sbc-normal-dense-open-integral-section), including all its private helpers.

Holes closed: 1. Holes added: 0. Sorries left in this delivery: none.
This is a complete proof, not a decomposition into unproved lemmas.

## No longer needed

No imports of the original module were removed. Its original DAG node had no
proof dependencies, so there are no existing nodes or modules to prune.

The proof uses open connected components and sheaf gluing instead of constructing
a finite product decomposition of every affine normal ring. It needs no separate
normal-ring product decomposition, no new birational-isomorphism theorem, and no
new absolute-normalization comparison module. No such modules were imported.

## Where the brief, the DAG or earlier work was wrong

The original node had one non-elementary proof step with no proof dependencies.
The needed section-extension argument was not available as a stated dependency.
It is now both explicitly stated and fully proved, and the original node records
the actual affine assembly. The original mathematical statement is correct and
was not changed. The unit route remains unchanged.

A combined rewrite initially caused excessive elaboration because the affine
isomorphism criterion has an explicit morphism argument. Applying it explicitly
resolved the issue; the final proof needs no increased heartbeat or time limit.
LeanSearch was unavailable, while LeanFinder, Loogle, source searches and blueprint
searches completed. The local literature checkout lacks the Stacks TeX documents;
the cited Stacks pages were read directly at their official URLs.

## New nodes

lem-sbc-normal-dense-open-integral-section, in
 dag/nodes/sec-smooth-base-change/lem-sbc-normal-dense-open-integral-section.json,
records the proved integral-section extension theorem in
Sheaf.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection. The conclusion
is the surjectivity part of the integral-closure argument, with no normalization
isomorphism in its statement. It is strictly a part of the original argument and
has a complete Lean proof. No change records or forced adaptations are needed.

## Second reading by S4

1. Compared the existing module and node with the repository using diff. The
   existing theorem signature, public imports, namespace, universe and docstring
   are byte for byte unchanged. There are no definition changes, statement
   changes, forced adaptations or change records. The only new public declaration
   is the integral-section extension theorem in its own new module. Verdict: pass.
2. Compiled both modules locally in import order with lcompile.py, without errors
   or warnings. Independently compiled scratch copies with #print axioms for the
   target, the extension theorem and all three private helpers: every declaration
   uses only propext, Classical.choice and Quot.sound. Neither delivered module
   contains sorry, an axiom, unsafe, opaque, implemented_by or extern. Every chosen
   section comes from a fully proved theorem. Verdict: pass.
3. There are no statements split off with sorry. Read the fully proved new theorem
   from generic germs through connected-component restriction and sheaf gluing.
   Density is used for nonemptiness on each component open and for injectivity on
   overlaps; no global nonemptiness or connectedness is assumed. Empty U and empty
   X use the empty indexed cover, and disconnected X uses separate open integral
   components. The affine hypothesis is sufficient (the proof actually works for
   arbitrary U). Independent LeanFinder search for normal-scheme integral functions
   regular on a dense open and Loogle search for IsIntegrallyClosed together with
   Hom.fromNormalization found no direct replacement. Source searches in lean/Sheaf
   and lean/WeilConjectures confirm that the existing generic-germ extension theorem
   is used rather than duplicated. Verdict: pass.
4. The proof first uses Mathlib affine normalization and locality, then the proved
   extension theorem and already proved source-library ingredients. Both added
   imports of the existing module are proof-only; the imports of the new module
   needed only in proofs are also plain imports. A scratch removal test confirms
   the scheme-theoretic-dominance import is required. The original proof_deps was
   empty, so the No longer needed list is complete. Read the unit record
   dag/units/sk-prop-input-spreading.json: its statement, steps and realized record
   are untouched; this componentwise argument is below the unit route. Verdict: pass.
5. Read both delivered nodes and checked their Lean declarations and signatures.
   Their proof steps describe the actual restriction, generic-germ, component and
   gluing arguments. proof_deps are the union of the named node dependencies used
   in the steps: the target uses the extension node, and that node uses
   lem-sc-function-field-sections-glue, whose recorded existing declaration was
   checked against the source. The new node has its source, search records,
   creation provenance, blueprint ancestry, chapter, unit and Lean record.
   Verdict: pass.

Second reading changed only the existing module's unnecessary scoped
backward.isDefEq.respectTransparency option (removed after a successful scratch
compile without it) and its redundant trailing blank line. No proof argument or
signature was changed. All mathematical work of the first reader is retained.
