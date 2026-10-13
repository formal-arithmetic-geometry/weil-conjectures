## What changed

Replaced the proof of AlgebraicGeometry.affineSections_square_mate_path_unit by the
sections pasting calculation from a sheaf-level square mate unit equation. The existing
statement and its docstring are unchanged. Added the proof-only import
Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit. Private proved helpers expand
composite units, move normalized comparisons across units and identify the exact scalar
restriction unit. A private generic sections_unit_pasting lemma keeps those calculations
independent of geometric definitions; the public proof supplies the sheaf mate equation
and proves that the composed underived section comparison equals s. Updated the
existing node to follow this calculation. The public signature was checked byte-for-byte
against the repository original. The fixed nondependent forall binder names are retained;
linting is scoped off for that declaration. Profiling showed substantial linting
cost. The syntax linter flags the named nondependent forall binders, although the proof
introduces and uses the corresponding hypotheses. Kernel checking remains enabled. The localization, composite-unit, exact-derived-comparison and pinned-adjunction
constructions are also kept locally irreducible during specialization, using their
interfaces rather than unfolding their construction proofs. The final normalization
also preserves local functor aliases (zetaDelta := false). The declaration also disables the optional let-to-have cleanup transformation: it
retains the original local let expressions, avoiding repeated expansion of the
localization constructions during cleanup. Full kernel checking stays enabled.
No compiler time limit is changed and no file is split for speed.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.affineSections_square_mate_path_unit
(lem-pc-affine-sections-square-mate-path-unit). Added one hole:
AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit
(lem-pc-derived-pushforward-square-mate-unit), in its own module. This is a decomposition:
one upper hole closed, one strictly smaller sheaf-level hole added, net zero holes.
The remaining theorem contains no affine sections functor and none of the affine
comparison isomorphisms t,b,z,d,v,r,s. The affine sections pasting, exact restriction
calculation and extensionality argument are proved in the assigned module.

## No longer needed

No original imports were removed: the existing public import is needed by the unchanged
statement. The original node's direct proof dependency
lem-pc-ringed-spaces-derived-direct-image-composition and its module
Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition are not needed by the
new calculation. The old direct dependencies lem-pc-ringed-spaces-derived-pullback-composition
(module Sheaf.AlgebraicGeometry.DerivedPullbackComposition) and
def-pc-derived-base-change-map (module
Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap) occur in the new sheaf-level
lemma rather than as separate steps of the affine sections proof. They remain
available through the existing statement import.
No claim is made that these modules leave the whole targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The stated direct-image composition theorem gives a canonical right-derived unit equation,
but it does not identify that comparison with the conjugate of the fixed pullback square.
The missing identification is isolated as the new sheaf-level lemma. The sections part
uses only the three normalization equations supplied as hypotheses, so it does not import
AffineSectionsCompositionComparisons to reconstruct the supplied comparisons.
The local literature sources are absent in this read-only clone; the cited Stacks tags
08HY, 0D5T and 0AA7 were read on the Stacks website.

## New nodes

lem-pc-derived-pushforward-square-mate-unit records the sheaf-level conjugate square
unit equation before affine sections. It supplies an underived square comparison which
is identity on whole-open sections, together with its unit equation for all homotopy
objects. Identity squares give ordinary unit coherence; on zero complexes both sides
vanish. Its proof follows the pinned derived Hom equivalences and the defining
left-derived composition factorization. The new module is
Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit. All existing signatures and visibility are preserved. The local elaboration
settings are documented in
coord/changes/affine-sections-mate-local-transparency.md, as required by the static
checker for added attribute commands.

Validation: standalone lcompile compiled the main module cleanly in 45.2 seconds
with the alias-preserving proof and optional cleanup transformation disabled.
The earlier attempt timed out in deliver3. With this repair, both source compiles
and both axiom probes passed; the final dry run also checks the change record.
No delivery has been pushed.


## Second reading by T2

1. Compared the delivered module with the read-only repository version and
   programmatically compared the complete public theorem signature: byte-for-byte
   identical. Its docstring and visibility also agree. The existing node changes
   only proof, proof_deps and proof_origin. The new module has no existing interface
   to alter. The local elaboration attributes and options are covered by
   coord/changes/affine-sections-mate-local-transparency.md; no definition changes.
2. Compiled both modules through lcompile.py in dependency order and compiled the
   new module separately. No errors or unexpected warnings. The only source sorry
   is the public named exists_derivedPushforwardSquareMateUnit. No forbidden trust
   declarations or hollow definitions occur. The witness e is eliminated within
   a theorem proof, never selected as definition data. The delivery dry run checks
   the axioms of every delivered declaration, including the private helpers.
3. Read the new equation against canonicalPullbackAdjunction,
   exists_schemeDerivedAdjunction and exists_derivedPullbackComposition. The shared
   counits and normalized Hom equations pin the mate, ruling out adjunction twists.
   The equation is true for arbitrary J: derive the unit and counit
   factorization identities from the normalized Hom equation, paste them,
   and use the composition factorization and adjunction triangle identities. Identity
   squares reduce to composite unit coherence; zero complexes and empty schemes
   need no extra condition. This strictly removes the affine sections and all
   seven affine comparisons from the open task; it is a genuine decomposition,
   not a restatement. Independent leanfinder, loogle and grep searches with
   localization/adjunction/unit language found generic derived adjunction laws,
   and local rg found bounded-below PlusAdjunction and exact-left-adjoint
   CompConjugate tools, neither applicable to arbitrary tensor pullback here.
   Checked Stacks Tags 08HY, 0D5T and 079W online: they support the underlying
   adjunction/composition route. The new docstring now spells out these unit/counit factorization
   identities and their pasting instead of leaving the extension step implicit. Closing
   this sheaf-level equation is not a short application of the available lemmas.
4. Read the generic pasting proof from its conclusion backwards: comparison_unit_inv
   supplies the first normalization, hδ supplies the only geometric step,
   comparison_unit_hom and exactCompUnit_fac supply the final normalizations.
   The component extensionality proof really identifies the underived path with s.
   Both imports of the item are needed, and the new module's public import supplies
   canonicalPullbackAdjunction in its signature. No import is proof-only but public.
   Completed the list of old direct dependencies no longer used by this node.
   The unit sk-thm-picard-duality has empty realized statement/step slots in the
   repository; this delivery does not change or bypass any recorded realization.
5. Checked both node statements against Lean, including their verbatim lean.statement
   fields, proof dependency unions, sources, creation fields and blueprint origin.
   The existing node records the implemented affine pasting; the new split node
   records exactly the remaining sheaf equation. Verdict: deliver as one hole
   closed and one strictly smaller hole added, net zero, with no whole-module pruning.

Second reading changed only the new theorem's natural-language proof and the
report's complete pruning/review account. The compiled proof bodies were retained.

Dry-run repair: the new proof docstring initially introduced a line longer than
100 characters. Replaced that text with the explicit factorization argument
above and kept all its lines within the project limit; no Lean proof changed.

Explicit #print axioms probes compiled in a scratch module for both public
declarations. Both report only propext, Classical.choice, Quot.sound and
sorryAx, as expected for the remaining named sheaf-level hole and upstream
open statements. The scratch source was removed from the delivery set.
