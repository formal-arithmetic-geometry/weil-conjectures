## What changed

Proved `horizontal_ordinary_forward_fixed_pasting_core_aux` from the existing rectangle
comparison lifts and ordinary compatibility theorem, plus a new isomorphism-transfer
identification theorem. The proof computes the fixed upper and base comparisons,
applies rectangle pasting, and explicitly cancels the comparison isomorphisms.
Existing signatures, definitions and public imports are unchanged.
Proved private component equations keep the lifted comparison definitions folded. Updated the auxiliary node's
proof route to match Lean.

## Proved and sorry left

Closed `AlgebraicGeometry.horizontal_ordinary_forward_fixed_pasting_core_aux`.
Added one remaining hole:
`AlgebraicGeometry.horizontal_transfer_eq_of_inverse_formula` in
`Sheaf.AlgebraicGeometry.HorizontalTransferInverseFormula`, node
`lem-sc-horizontal-transfer-inverse-formula`.
This is a decomposition (one hole closed, one added, net zero), not a complete
axiom-free proof. The original module has no remaining sorry.

The remaining theorem concerns only an isomorphism over a single base and its
adjunction/composition comparisons. It contains no ordinary base-change map or
iterated pullback calculation. Its supplied inverse formula determines the
comparison uniquely by faithfulness; no arbitrary data are chosen from a sorry.
The supplied transfer is tied to its explicit construction by an equality,
instantiated by rfl in the main proof. This is an isomorphism-transfer
normalization step, not a renamed forward-pasting theorem. Identity arrows, empty
schemes and zero objects need no extra hypotheses.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting`
and `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting`: their calculation is now
used through `RectangleQCohOrdinaryCompatibility`, which still imports them.
Old direct proof dependencies removed from the auxiliary node are
`lem-pc-derived-base-change-horizontal-pasting` and
`lem-pc-derived-base-change-pasting`.
No transitive modules or nodes are claimed pruned. Both original pasting lemmas
remain needed by that existing rectangle proof.

## Where the brief, the DAG or earlier work was wrong

The previous attempt correctly identified transfer normalization as the missing
step, but stopped without combining the existing rectangle result with that step.
This delivery completes the combination. A direct-component definition experiment
was withdrawn; no definition change or downstream adaptation remains. An intermediate faithful-inclusion
restatement was discarded because it was not a strict reduction.

## New nodes

`lem-sc-horizontal-transfer-inverse-formula` isolates transfer normalization over
one base. Its source is Stacks Tags 0D5S, 0D5T and 08HY and its proof uses the
unit compatibility of right-adjoint uniqueness. Searches found the generic
Mathlib unit compatibility lemmas; LeanSearch was unavailable. No definition or
existing interface was changed, and no forced adaptation or change record is needed.

## Second reading by C2

1. PASS. Compared the delivered module with the repository using diff and exact
   text checks. All six existing public declaration signatures and all three
   definition bodies are byte-for-byte unchanged. Public imports are unchanged.
   No change record or forced adaptation is needed.
2. PASS with the reported open lemma. Both delivered modules compiled locally
   through lcompile.py, in import order (15.1 s and 36.2 s). Source inspection
   found exactly the one named theorem sorry reported above, no hollow definition,
   and no axiom, unsafe, opaque, implemented_by or extern. A scratch import probe
   printed axioms for all six existing public declarations and the new theorem:
   only propext, Classical.choice, Quot.sound, and expected sorryAx appeared.
   The transfer itself already depends on upstream open proofs; its constructed
   data and all existing definitions remain unchanged. The rectangle witnesses
   are obtained locally by destructing its proved comparison-lifts theorem;
   the new sorry supplies only a propositional equality, never arbitrary data.
3. PASS. The sole split-off identity is strictly smaller than forward pasting:
   one source isomorphism over one base, with no base-change map, rectangle or
   second base morphism. Checked its inverse direction and factor order against
   the definitions of horizontalMatePushComp, horizontalMateAdjunction and
   horizontalMateEquivalence. Composing j.inv with k gives the identity by
   conjugate cancellation and unit_rightAdjointUniq_hom_app. This argument also
   covers identity arrows, empty schemes and zero objects without exclusions.
   Checked the cited Stacks Tags 0D5S, 0D5T and 08HY. Independent leanfinder,
   loogle and grep searches used conjugate composition and restriction terms;
   their Mathlib hits are generic or underived. Local SchemeIsoRightAdjointNormalized
   concerns a different, further right adjoint and does not prove this identity.
   The lemma has its matching node and complete docstring proof. Formalizing the
   ambient/restricted conjugate identification is substantial, so it remains open.
4. PASS. The proof applies existing rectangle comparison lifts and ordinary
   compatibility, then cancels the fixed comparisons; no shorter exact existing
   declaration was found. Each new plain import is used; the two existing public
   imports supply signature/definition vocabulary. Added explicit old dependency
   node names to No longer needed. Those nodes remain used transitively, so no
   module pruning or positive net-hole progress is claimed. The unit record
   sk-thm-picard-duality has empty realized entries; no realized step is bypassed,
   and this reduction stays below that unit's route.
5. PASS. The auxiliary node proof and proof_deps follow the rectangle lift,
   upper/base comparison computation, transfer identification and cancellation.
   Its only changed fields are proof, proof_deps and proof_origin. The new node
   has source, creation/blueprint records, searches, complete proof steps, their
   dependency union and a Lean signature matching the module verbatim.

Second reading changed one proof-boundary whitespace difference back to the
repository spelling, clarified the new lemma's docstring and node proof with the
explicit j.inv-followed-by-k cancellation, and completed the pruning report.
No mathematical signature, definition, or executable proof was changed.
