## What changed

Proved AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_composition with its
original signature and visibility. Private proved helpers singleComp, sourceComp,
targetComp and rawGeneralComp implement the single-complex, source-factor, target-factor,
and final naturality calculations. The private rawGeneral definition is the actual
five-factor morphism, with no postponed data or proofs. Abstracting the coefficient
category avoids repeatedly unfolding concrete abelian-sheaf instances.

Proof-only imports now use import all Sheaf.AlgebraicGeometry.EtalePullbackSingleComp
and import all Sheaf.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift to reuse
already proved private exact-functor single and shift helpers. Public imports are unchanged.
The node's proof, proof_deps and proof_origin follow this implementation. No existing
statement, definition, or public interface changed.

## Proved and sorry left

Closed 1 original hole: AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_composition
(lem-sbc-abelian-raw-pullback-composition). Added 0 holes; split off 0 statements.
Every new private lemma is completely proved. No sorry remains in the item's module.
The proof uses the existing proved exact-functor helpers, rather than any new or existing
unproved theorem. The delivery axiom probe found no axiom beyond propext, Classical.choice and Quot.sound.
All coefficient binders occur explicitly on private helpers, with no new section context.

## No longer needed

Removed the direct proof import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition and
its planned proof dependency lem-weil-pbc-derived-inverse-image-composition: the actual
composition isomorphism, naturality and its proved shift compatibility suffice.

Removed the direct proof import Sheaf.AlgebraicGeometry.AbelianPullbackSingleComposition
and its planned proof dependency lem-sbc-abelian-pullback-single-composition: singleComp
uses the already proved generic exact-functor helpers in EtalePullbackSingleComp instead.
The latter module stays needed, as does upperStarComp associativity from
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence.

These are dependencies pruned from this proof; other modules may still require them.
The unit sk-lem-failure-field has empty realized statement and step lists, so this
calculation bypasses no realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned proof cited a large packaged derived coherence
theorem where naturality of the concrete composition isomorphism suffices, and an abelian
single-complex specialization where the existing generic exact-functor helpers suffice.
The shift compatibility needed by the plan is already proved in the private helpers of
AbelianDerivedDirectImageTransitionShift. No hypothesis on coefficient-map invertibility,
nonzero coefficients, nonempty schemes, or positive degree is used: zero sheaves, empty
schemes, identity maps and p = 0 all follow from the same categorical identities.

## Second reading by N2

1. Compared the delivered module with the repository version and extracted the existing
   theorem signature through its proof delimiter: byte-identical. Public imports and
   visibility are unchanged. Only private helpers, proof imports, the proof and its
   explanatory docstring changed. No definition or statement used by others changed;
   no change record or forced adaptation is required. Verdict: pass.
2. Compiled the delivered file locally with lcompile.py, without errors or warnings.
   Inspected all four private lemmas and rawGeneral: no sorry, axiom, unsafe, opaque,
   implemented_by or extern, and no unproved witness selection. rawGeneral is exactly
   the actual five-factor construction. Checked #print axioms on the existing theorem
   and all five new private declarations in a scratch copy: only propext,
   Classical.choice and Quot.sound. Verdict: pass.
3. No statements were split off, and no new holes or nodes were added. The private
   lemmas are fully proved categorical calculations. Their binders impose no extra
   conditions on the original theorem. In particular no coefficient map is cancelled:
   only canonical isomorphisms are cancelled. Zero classes/sheaves, identity maps,
   empty schemes and degree zero require no additional assumptions. Verdict: pass.
4. Read the imported generic single-complex and shift proofs, and searched the library
   for alternative raw composition laws and Mathlib for shift/composition identities.
   Mathlib's commShiftIso_comp_hom_app and shift_app_comm are already used directly.
   The other raw composition theorem concerns fixed ModuleCat coefficients in Over W
   and rests on a sorry; it offers no shorter proved route for arbitrary coefficient
   morphisms here. An additional Loogle query returned a query elaboration error,
   providing no evidence either way. Both retained proof imports supply used private
   proved helpers; import all is necessary to access them and remains non-public.
   Both removed imports and both removed old proof_deps are listed under No longer
   needed. The unit's realized statement and step lists are empty, and this structural
   calculation does not replace its geometric route. Verdict: pass.
5. Compared old and new node JSON: only proof, proof_deps and proof_origin differ.
   The proof steps describe sourceComp, targetComp and rawGeneralComp accurately;
   proof_deps is exactly the union of their recorded uses. The two helper-containing
   modules are explicitly identified in the proof text rather than claiming to apply
   their coefficient-specialized public theorems. Statement, lean signature, chapter,
   unit and source remain unchanged. Verdict: pass.

Second reading changed only this report: added the independent checks and verdicts.
No Lean or node repair was needed. Net holes closed in this delivery: one; holes added:
zero. The pruning is of two direct proof dependencies, not a claim that their modules
have become unreachable from every target.
