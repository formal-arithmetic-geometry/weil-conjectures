## What changed

Repaired `Sheaf.AlgebraicGeometry.LocalKoszulAugmentedCarrier` after the landing
review rejected duplicate private helper declarations. Removed the duplicate
`finiteFree_flat` and `tensorPullback_additive` declarations and inlined their
arguments, while retaining the existing public theorem signature and imports.
The earlier duplicate `koszul_term_zero` helper remains removed, with its
exterior-power zero calculation inlined at its single use. Relative
to the repository baseline, its single hole is closed by constructing the actual
sheafified Koszul complex and transporting the augmentation, flatness, free bases
and zero differentials through the chart and over-site comparisons. The private
proof imports replace AffineQuotientResolutionSheafification with
AffineKoszulFiniteFreeResolution and add the extension, scalar base change,
tensor pullback, and flat coproduct APIs used by the proof.

## Proved and sorry left

Hole closed (1): `AlgebraicGeometry.exists_local_koszul_augmented_carrier`
(node `new-s1-local-koszul-augmented-carrier`). Holes added (0): none.
No `sorry` remains in the delivered module; no statement was split off.
This closes the existing hole rather than decomposing it into new holes.

## No longer needed

Removed proof import: `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`.
Removed old proof dependency: `lem-sc-affine-quotient-resolution-sheafification`,
replaced by `lem-sc-affine-koszul-finite-free-resolution`, whose augmentation
already has the exact Koszul source required here. The old general affine
quotient resolution is not directly used by this proof. No global module-pruning
claim is made: other targets may still reach that module. All other old
`proof_deps` remain. The duplicate private `koszul_term_zero` declaration
is removed, with its elementary calculation inlined at the only use. The
duplicate private `finiteFree_flat` and `tensorPullback_additive` declarations
are also removed, with their arguments inlined at each use.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private theorem whose statement duplicated a
library theorem indexed from `AffineKoszulGeometricProperties`. The repair keeps
the same mathematical argument while avoiding a second declaration of that
statement. The public target statement and DAG route are unchanged.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

Verified that the repaired module compiles with `lcompile.py`, retains the
original public theorem signature, and has no `sorry`, `axiom`, `unsafe`, or
other forbidden declarations. The exact duplicate private theorem is gone;
the remaining local proof is inside the target proof and introduces no public
statement. The pre-existing local attribute change record
`coord/changes/local-koszul-carrier-local-reducibility.md` remains applicable
and is included in this repair. The DAG node and its proof dependencies are
unchanged because only the implementation of the proof was repaired.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module and node with the repository baseline. The
   existing public theorem signature is byte for byte identical, and all six
   public imports are unchanged. The sole scoped reducibility annotation is
   documented in `coord/changes/local-koszul-carrier-local-reducibility.md`; it
   changes local elaboration only. No existing definition or target is altered.
   Verdict: pass.
2. Compiled the complete module with `lcompile.py` (15.1 seconds, no warnings).
   Checked every private helper and the public theorem with `#print axioms` in
   a scratch copy. All use only propext, Classical.choice and Quot.sound; none
   uses sorryAx. No sorry or forbidden declaration occurs in the delivered
   source. The carrier is explicitly P.obj E; the isomorphisms chosen from
   Nonempty and the adjunction witnesses used by private definitions come from
   proved APIs, not an unproved arbitrary existence theorem. Verdict: pass.
3. No statements with sorry were split off and no new nodes were introduced.
   Reviewed the private glue lemmas: contraction by zero, extension in positive
   degrees, faithful detection of zero differentials, and preservation of free
   terms along the open pullback square. Checked m=0, ranks zero, exterior
   degrees above m, empty opens, and zero rings; none needs nontriviality.
   Independent source searches and msearch grep/loogle searches found the
   existing mapFreeIso and exterior-basis APIs already used, and no shorter
   public carrier construction. Other occurrences of the elementary finite-free
   flatness glue are private, so are not usable imports. Verdict: pass.
4. Read the proof from the carrier construction down through the affine
   augmentation, K-flatness, zero differentials, bounds and free terms. The
   proved finite-free affine augmentation is a more direct route than the old
   general quotient-resolution dependency. Proof-only imports remain plain
   imports, public imports support the unchanged signature, and retained proof
   imports provide the APIs used. Corrected the report's incomplete pruning
   list. The unit sk-thm-picard-duality has empty realized entries, which are
   unchanged; the prescribed local Koszul route remains. Verdict: pass.
5. Compared the node proof steps with the actual construction and checked that
   proof_deps is exactly the union of their uses. The only existing-node changes
   are proof, proof_deps and proof_origin. Each dependency resolves to its
   existing Lean API or Mathlib match. The statement and its recorded Lean
   signature are unchanged. Verdict: pass.

Second reading changed the report to describe the full baseline diff and list
the removed import and old dependency, and corrected the theorem docstring to
name the affine_koszul_finite_free_resolution API actually used. The duplicate
private finiteFree_flat and tensorPullback_additive declarations were removed
and their arguments inlined; the public signature is unchanged.


## Second reading by C1

1. Compared the delivered Lean module and DAG node with the repository versions.
   The existing public theorem signature is byte for byte identical and all
   public imports are unchanged. No existing definition is changed. The local
   irreducibility annotation is scoped to this module and has its change record.
   Verdict: pass.
2. Compiled the delivered module with lcompile.py: success in 21.5 seconds,
   without warnings. Regenerated a scratch copy from the current source and
   checked all nine declarations with #print axioms: each uses only propext,
   Classical.choice and Quot.sound, with no sorryAx (22.8 seconds). No sorry,
   axiom, unsafe, opaque, implemented_by or extern occurs in the source. The
   carrier is explicitly the pushforward of the sheafified Koszul complex;
   chosen adjunctions and comparison isomorphisms come from proved APIs, not
   arbitrary witnesses of unproved existence. Verdict: pass.
3. No statements were split off, no holes were added, and no new nodes exist.
   Read the private differential, scalar-extension, chart and over-site glue.
   Checked m=0, degrees above m, rank zero, empty opens and zero rings: the
   exterior-basis and zero-object arguments require no nontriviality. New
   independent source searches for Koszul zero differentials and finite-free
   flatness, plus msearch loogle for mapFreeIso and leanfinder for scalar
   extension killing generators, found the already-used free-sheaf API and no
   shorter carrier theorem. Existing duplicate flatness/additivity helpers are
   private and the delivery correctly inlines those arguments. Verdict: pass.
4. Read the proof from the explicit carrier and augmentation down through
   K-flatness, zero differentials, support [-m,0] and local free terms. The
   affine_koszul_finite_free_resolution API supplies the exact required source.
   All added proof imports are plain imports and support the displayed proof;
   signature imports remain public. The removed dependency and import are
   completely listed under No longer needed. No global module pruning is
   asserted. The unit sk-thm-picard-duality has unchanged empty realized
   entries and the local Koszul route is retained. Verdict: pass.
5. The node changes only proof, proof_deps and proof_origin. Compared each step
   with the Lean argument, and verified proof_deps equals the union of step
   uses. The recorded Lean statement is unchanged and the named dependencies
   provide the APIs used. There are no new-node metadata requirements to apply.
   Verdict: pass.

Second reading changed only documentation: corrected the local reducibility
change record's stale reference to the removed private finiteFree_flat helper
and open MonoidalCategory command, and appended this independent review.
No Lean proof repair was needed. Holes closed: one, namely
AlgebraicGeometry.exists_local_koszul_augmented_carrier. Holes added: zero.
