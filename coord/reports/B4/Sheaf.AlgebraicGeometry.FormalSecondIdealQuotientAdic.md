## What changed

Restored the complete proof of
`AlgebraicGeometry.formalSecondIdealQuotient_coherent` on the current synced source.
The repair changes the proof-only import from
`import all Sheaf.AlgebraicGeometry.CoherentFormalModule` to
`import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule`.
The former module is now only a public re-export; its private declarations do not
include the ideal-product helpers owned by the latter module. The returned proof
failed with unknown identifiers `idealModuleProduct_quotient_comp_zero_iff` and
`idealModuleProduct_mono`; the corrected import makes that proof compile.

The proof follows all three existing DAG steps: coherence of each quotient from
`formalCompletionSystem_coherent`, descent of I-annihilation through the epimorphic
K-quotient, and the adjacent quotient isomorphism obtained from the canonical
quotient interchange and the K-quotient of M's defining adjacent isomorphism.
Cancellation of the quotient projection proves the required transition equation.
No signature, definition, public import, or DAG route changes.

Validation: the repaired module compiles through `lcompile.py` without errors or
warnings (3.0 seconds). A separate sandbox overlay compiles both the repaired module
and its sole direct consumer,
`Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftData`, unchanged
(3.1 and 3.3 seconds). The import-direction check permits the source-module import.
No consumer adaptation or change record is necessary for a proof-only import repair.

## Proved and sorry left

Closed one existing local hole:
`AlgebraicGeometry.formalSecondIdealQuotient_coherent`, node
`lem-weil-pbc-formal-second-ideal-quotient-adic`.
Zero `sorry`s remain in the item's module. Zero holes or statements were added,
and zero theorems were split off. The private `quotientProjection_map` is proved.

This is a complete proof from the existing stated dependencies. It still uses
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_comparison`, node
`lem-weil-pbc-devissage-second-adic-system-comparison`, whose existing theorem is
currently `sorry` in the synced source. An explicit axiom check on the published
compiled dependencies reports `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx` for the item and comparison theorem. It reports only the three permitted
axioms for `formalCompletionSystem_coherent` and `quotientProjection_map`.
No inherited hole is presented as a fully axiom-closed proof.

## No longer needed

Removed the obsolete proof-only
`import all Sheaf.AlgebraicGeometry.CoherentFormalModule`, replacing it with the
source module that owns the required private lemmas. The public re-export import
stays because it is part of the existing interface. No nodes or modules are pruned:
both existing proof dependencies are used, and Currying supplies the statement's
`flip`. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

Repaired the returned upstream-sync failure concretely, rather than merely rebasing:
the returned head's proof no longer found the two private helpers through the
retired Sheaf wrapper. They now live in
`WeilConjectures.AlgebraicGeometry.CoherentFormalModule` (lines 140 and 195).
The theorem statement and the node's three-step plan remain correct. Read Stacks
Tag 088A, `coherent.tex`, `lemma-existence-tricky`, specifically the construction of
G_e from the termwise quotients. The positive Lean indices e+1 and n+1 agree with
that construction, including e=0 and n=0.

The previous report's claim that the item had no inherited `sorryAx` is no longer
true after the sync; the explicit axiom results above replace that claim. The
comparison module's existing residual theorem, and its pre-existing private holed
`quotientSwapMap` definition, belong to that separate repair item; this delivery
adds neither and does not conceal them.

Fresh searches through `msearch.py` found no shorter ready-made sheaf theorem:
LeanFinder returned module-level adic-completion transition maps, while Loogle
confirmed `CategoryTheory.Limits.cokernel.π_desc`, already used by the projection
helper. Repository searches confirmed the source ownership of the private helpers.
The unchanged node proof, proof dependencies, and origin already match the restored
proof, so no DAG field is modified.

## Second reading by B4

1. **Repository comparison.** I compared the delivered module with the repository
   version. The theorem signature, private helper signature, public imports, and all
   declarations are unchanged; only the proof body and its proof-only source import
   differ. Verdict: pass.
2. **Proof and axioms.** I compiled the module and its scratch copy with explicit
   `#print axioms` checks using `lcompile.py`. Compilation is clean. The item and
   comparison theorem report exactly the three permitted axioms plus inherited
   `sorryAx`; the completion theorem and private projection helper report only the
   three permitted axioms. No local `sorry`, forbidden declaration, or hollow
   definition was introduced. Verdict: pass.
3. **Statements and split-offs.** No statement was added or changed, and no hole was
   split off. The existing theorem is proved with the exact node statement. Searches
   found no duplicate Mathlib or library theorem needed here. Verdict: pass.
4. **Route and pruning.** The proof follows all three planned steps and uses both
   recorded proof dependencies. The only import change restores access to the source
   private helpers; no unused dependency, node, or module was pruned. Verdict: pass.
5. **DAG agreement.** The node's Lean declaration, statement, proof route,
   `proof_deps`, and `proof_origin` agree with the delivered code, and the unit route
   remains intact. Verdict: pass.

I checked the source construction at `lemma-existence-tricky` in `coherent.tex`,
including the first positive indices and the zero or unit ideal cases. I also
compared the node JSON byte for byte with the repository and read the unit's
`realized` field. No route or node edits were needed. The second reading made no
Lean changes: it verified the first worker's proof and import repair and added this
review record.
