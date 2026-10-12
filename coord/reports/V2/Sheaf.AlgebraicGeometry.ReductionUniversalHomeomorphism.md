## What changed

Proved the single theorem in Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism,
with its signature unchanged. Added the proof-only import
WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme for its already proved
Scheme.isReduced_nilradical_subscheme instance. Surjectivity follows from the range
of the subscheme inclusion and support_nilradical. In each arbitrary pullback square,
base-change stability gives a surjective closed immersion, hence a homeomorphism.
Updated the existing node's proof and proof_origin to record the actual declarations used.
The three-step argument and its proof_deps remain: the affine reducedness ingredients
are used inside the existing source-library instance. No unit statement or step is bypassed;
the item is not itself in sk-thm-p1.realized.

Searches: LeanFinder through msearch found Mathlib's affine_isReduced_iff and closed
immersion lemmas; Loogle through msearch found nilradical ingredients; rg found the
exact reducedness instance and its proved vanishing-ideal argument in the source library.
Import-direction check permitted the new proof-only import. Local compilation passed.

## Proved and sorry left

Proved AlgebraicGeometry.reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism
(blueprint: lem-weil-pbc-reduction-universal-homeomorphism).
One of one original sorries eliminated. No sorry remains in the item; no new theorem,
sorry, definition, or node was added. The delivery dry run checks axioms and compiles
on the project server as well as locally.

## No longer needed

None. No existing import was removed. All existing DAG proof dependencies remain relevant:
the affine reducedness argument is supplied by an already proved source-library instance,
and the two base-change leaves are used directly through their Mathlib declarations.
No additional Sheaf proof module or universal-homeomorphism bridge is needed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The node's candidates correctly identified the existing
source-library reducedness argument. A still shorter presentation is available through
Scheme.isReduced_nilradical_subscheme in the same source module. The universal assertion
can be proved directly by base-changing closed immersion and surjectivity, without
importing WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.

## Second reading by V2

1. Visible declarations: compared the entire delivered module with the repository
   version using diff. The sole theorem's signature and existing docstring are
   byte-for-byte unchanged; no declaration or definition was added. The only
   differences are the proof body and a plain, proof-only import. X remains an
   arbitrary Scheme.{u}, with no reducedness, affine, finiteness, or nonemptiness
   hypothesis. Read Stacks Morphisms lemma-reduction-universal-homeomorphism
   (054M), and Schemes lemma-reduced-closed-subscheme (01J3) and
   definition-reduced-induced-scheme (01J4), in the local source copies
   /home/ubuntu/c1-stacks-review/morphisms.tex and schemes.tex. All four clauses
   agree: the nilradical subscheme is reduced, its inclusion is a closed immersion
   and surjective, and every base change is a homeomorphism. Verdict: pass.
2. Proof and trust: local lcompile succeeds without warnings on the delivered
   module. A scratch copy with #print axioms for the theorem reports exactly
   propext, Classical.choice, Quot.sound, with no sorryAx. Scanned the delivered
   Lean for sorry, axiom, unsafe, opaque, implemented_by, extern: none. There are
   no hollow definitions. Verdict: pass.
3. Split-off statements: none were added or left open. Independently searched
   Mathlib via msearch grep for surjective closed immersions and nilradical
   subschemes, and searched both Lean roots for the reducedness instance and the
   universal-homeomorphism bridge. Read the source-library
   isReduced_subscheme_vanishingIdeal and isReduced_nilradical_subscheme proofs: the
   first uses radical quotient rings on the subscheme affine cover and
   IsReduced.of_openCover; the second specializes it using vanishingIdeal_top.
   No restatement of the item hides an obligation. Checked the empty scheme and
   Spec of a nonreduced ring (for example k[e]/(e^2)) in the argument: support is
   still the whole space, radical quotients remain reduced, and base change never
   assumes that the base-changed source is reduced. Verdict: pass.
4. Route and pruning: step 1 uses range_subschemeι and support_nilradical to prove
   surjectivity; the subscheme inclusion instance supplies closed immersion.
   Step 2 uses the existing reducedness proof, whose Spec reducedness instance is
   precisely the direction recorded by lem-weil-pbc-affine-scheme-reduced-iff.
   Step 3 applies both recorded base-change instances to h.flip; checked the
   orientation against of_isPullback and universally in Mathlib's Limits module.
   The resulting embedding plus surjectivity proves IsHomeomorph. The upstream
   universal-homeomorphism bridge would introduce an additional module and is
   unnecessary. Every original public import supplies notions appearing in the
   unchanged signature: subscheme, topologically, universally, IsReduced,
   IsClosedImmersion, Surjective. The sole new import is proof-only. All old
   proof_deps remain used directly or inside the reused affine reducedness proof;
   no pruning is missing. Read sk-thm-p1.realized: this item is not a realized
   statement or step, and the delivery keeps the unit's route. Verdict: pass.
5. DAG agreement: compared the complete node against the repository. Only proof
   texts and proof_origin changed, describing the three actual Lean steps;
   proof_deps is unchanged and is exactly the union of their uses. Read the three
   Mathlib leaves and verified their recorded declarations: affine reducedness
   (Properties.lean:114/122), closed-immersion base change
   (ClosedImmersion.lean:382), surjective base change (PullbackCarrier.lean:436).
   There are no new nodes or statement changes requiring change records.
   Verdict: pass.

Changes by the second reader: added this independent review and a search-log
entry. No repair to the Lean proof or DAG was necessary. The axiom-check scratch
copy is outside lean/ and is not delivered.
