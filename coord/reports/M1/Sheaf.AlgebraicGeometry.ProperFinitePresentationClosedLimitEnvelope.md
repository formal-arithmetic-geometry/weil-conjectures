## What changed

Proved AlgebraicGeometry.exists_proper_finitePresentation_closedImmersion_envelope in
Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope without changing its
statement. The proof follows Stacks 09ZR: separated envelope, Chow modification,
finite-subideal closed subscheme system, pullback limit, eventual closed immersion, and
surjective descent of universal closedness. The identification of X with its image is
handled by i.toImage. All cone maps and their compatibility are constructed in Lean.
Added the proof-only import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
for IsClosedImmersion.of_universallyClosed. Updated the node's proof and dependencies.
The source was read at https://stacks.math.columbia.edu/tag/09ZR because the local
literature/stacks-project/limits.tex is absent on this machine.

## Proved and sorry left

Proved AlgebraicGeometry.exists_proper_finitePresentation_closedImmersion_envelope
(node lem-weil-pbc-proper-closed-in-proper-fp-envelope-part): 1 of 1 original sorries removed.
No sorry remains in the delivered module, and no new sorry or node is added.
The proof uses the existing eventually_isClosedImmersion_of_isLimit theorem,
which is still sorry in Sheaf.AlgebraicGeometry.EventuallyClosedImmersion; this is the
existing downstream item, not a new obligation introduced by this delivery.
Compiled cleanly locally after removing unused imports; the required dry run checks the server.

## No longer needed

Removed direct imports:
- Sheaf.AlgebraicGeometry.LimitAffineTransition.
- Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace (its declarations are used, supplied by
  the public imports of ChowFiniteType).

Removed proof dependencies def-nagata-finite-type-closed-in-fp and
lem-weil-pbc-limit-affine-transition. The explicit chosen envelope definition is unnecessary:
the existing 01ZJ existence theorem suffices. The general affine-transition limit theorem
is unnecessary: isLimitFgSubCone already supplies the limit, and the pullback limit is
constructed with isLimitOfIsPullbackOfIsConnected. No other planned mathematical nodes are
pruned. Projective-space definitions and properness remain used. LimitAffineTransition may
still be reached through EventuallyClosedImmersion's public imports and dependencies;
this delivery only removes its direct use from the envelope argument.

## Where the brief, the DAG or earlier work was wrong

No statement error or unit-route departure. The planned generic affine-limit existence
invocation was redundant with the closed-subscheme system's existing limit theorem.
The blueprint unit sk-thm-p1's realized statement and steps are unchanged.

## Second reading by M1

1. Compared the delivered Lean file and node with the repository using diff. The existing
   declaration's signature is byte for byte unchanged; no definition or public import changed.
   The only Lean changes are the proof and proof-only imports. PASS.
2. Compiled the module cleanly using lcompile.py. Scanned for sorry and prohibited declarations:
   none occurs in the delivered module. A scratch copy with #print axioms reports exactly
   propext, Classical.choice, Quot.sound and sorryAx. The last is inherited from existing
   open dependencies, including eventually_isClosedImmersion_of_isLimit; this delivery
   closes the envelope's original hole, not the transitive proof closure. PASS.
3. There are no split-off statements, new declarations, new nodes or new holes to review.
   Checked the existing eventual-closed-immersion theorem's hypotheses against this application:
   the finite-subideal index is nonempty and directed; all pulled-back transitions are closed
   immersions, the stages are qcqs, their maps are locally of finite type, and the limit map
   is closed. Empty schemes and the zero ideal need no additional hypothesis. PASS.
4. Read the proof from the envelope down through Chow, the finite-subideal cone, connected
   pullback limits, eventual closed immersion, and surjective descent. Read Stacks 09ZR at
   https://stacks.math.columbia.edu/tag/09ZR; the route agrees with its proof. Searched lean/
   for alternative proper-envelope declarations and used msearch grep with the different
   query proper.*envelope|exists.*proper.*finitePresentation; no shorter existing envelope
   theorem was found. Removed direct imports and old proof dependencies are fully listed
   above. Tested removal of AffineTransitionLimit: compilation failed because its 01ZJ
   envelope theorem disappeared, so restored this necessary proof-only import. The unit
   sk-thm-p1's realized statement and all four realized steps are unchanged and not bypassed.
   PASS.
5. Compared the node diff with the proof: its changes are restricted to proof, proof_deps,
   and proof_origin. proof_deps is the union of the recorded proof steps' uses. The two
   removed dependencies match the unused chosen envelope definition and generic limit
   existence theorem; the explicit finite-subideal limit and pullback argument replace them.
   No new node fields or change records are needed. PASS.

Second reading changed only this report. The proof and node were correct and were retained.
The existing proof docstring's step 3 still describes the old generic affine-transition
limit route; read that final sentence instead as: "The explicit fgSubCone is limiting by
isLimitFgSubCone." Step 4 is implemented by isLimitOfIsPullbackOfIsConnected rather than
an explicit Yoneda proof. These documentation clarifications do not affect any statement.
