## What changed

No Lean signature, proof term, or import needed changing. The only Lean diff is
a comment before the proof explaining the two finite-dimensional comparisons. The dispatched item is a stale repair:
`coord/repairs.txt` still names upstream review #1428, but the checked-out statement
already assumes `(⊤ : IntermediateField k K).FG`, not `Algebra.FiniteType k K`.
The existing complete-intersection proof was retained in the sandbox and
compiled successfully with lcompile.py (2.7 seconds).

The proof enumerates a finite transcendence basis and field-generating set, applies
`FieldTheory.exists_completeIntersection_fractionField_model`, and then applies
`Algebra.exists_fractionField_completeIntersection_cotangent_model`. The domain
instance obtained from the first theorem supplies the second theorem's hypothesis.
The kernel and quotient equivalences give finite dimensionality; rank-nullity and
`c ≤ n`, `n - c = s.card` give the natural-number dimension equality. Casting to
Cardinal gives the untruncated formula. For finite extensions, `trdeg_eq_zero`
gives the final clause. No unit-level route is bypassed.

## Proved and sorry left

Holes closed this session: none (0 of 0). Holes added or split off: none.
`cartier_equality` already has a complete proof; there are no `sorry`s in this
module. This is verification of an already completed listed repair, not new proof
progress. The delivery dry run runs the project's axiom probe as well.

## No longer needed

None. Both Sheaf proof imports are used by the existing proof. No imports,
nodes, or modules are newly pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says the module still contains `sorry`, but it contains none.
The outstanding repair-list entry for upstream #1428 has already been addressed:
the theorem explicitly assumes finite generation as a field extension, and the
proof uses `IntermediateField.fg_top_iff` to obtain essential finite type.
No target or other statement was changed. The module compiles unchanged.

A fresh LeanFinder search for Cartier equality returned smooth-algebra rank
formulas and unrelated cotangent-space results, not a shorter general theorem.
The existing source follows the recorded three-step DAG proof, so no replacement
argument or new node is warranted.

## Second reading by G4

1. **Interface: pass.** Diffed the sole delivered module against
   `lean/Sheaf/Paper/CartierEquality.lean`. The only difference is one proof comment;
   the existing signature is byte for byte identical. In particular, the hypothesis
   remains `(⊤ : IntermediateField k K).FG`, both `Module.Finite` conclusions remain,
   and the untruncated Cardinal equation and finite-extension clause remain. No
   definition, visibility, or target statement changed; no change record is needed.
2. **Proof: pass.** Independently compiled the module with `lcompile.py` (2.6 s,
   no errors or warnings). A scratch copy with `#print axioms cartier_equality`
   compiled and printed exactly `propext`, `Classical.choice`, `Quot.sound`, with
   no `sorryAx`. There is no `sorry`, definition, or forbidden declaration in the
   delivered file. The existential model is eliminated inside a theorem proof;
   no definition chooses arbitrary data from an unproved existence theorem.
3. **Split statements: not applicable, pass.** No new statement, node, or lower
   hole was added, so there is no disguised restatement or new edge case to repair.
   Read the signatures of both model theorems: the first supplies `c ≤ n`,
   `n - c = s.card`, `f.length = c`, the quotient-domain instance, and the fraction
   field equivalence needed by the second. Both linear equivalences in the second
   have the kernel/cokernel orientations used in the proof. The rank-nullity
   cancellation also applies when the basis is empty or a dimension is zero.
4. **Route and pruning: pass.** Read all three steps of
   `lem-weil-pbc-cartier-equality` and the `realized` record of `sk-thm-p1`.
   The proof retains the recorded finite-basis, complete-intersection, cotangent
   comparison, rank-nullity route; no unit step is bypassed. Each proof dependency
   is used, either through its Sheaf theorem or its recorded Mathlib match.
   Both Sheaf imports and the finite-transcendence/rank-nullity proof imports are
   needed and are plain imports; public imports supply signature notions.
   Fresh Loogle search for `Algebra.H1Cotangent` returned presentation equivalences
   and smoothness results, not the general dimension equality. A separate `rg`
   search in the library and pinned Mathlib found no shorter general result.
   `SeparablyGeneratedDifferentialsDimension` requires a separably generated
   extension and does not cover this theorem's general hypothesis. No dependency
   or import was removed, so `## No longer needed` is complete.
5. **DAG: pass.** The node's `lean.statement` matches the unchanged signature.
   Its proof and seven proof dependencies describe exactly the declarations used
   above; `proof_origin` records the same Tag 07E1 complete-intersection argument.
   There are no node edits or new-node fields to review. The already landed
   field-generation correction explains why the queued upstream #1428 repair is
   stale; this verification closes no new hole.

Second reading changed the report to acknowledge the actual one-comment diff and
added this independent review and axiom evidence. No Lean repair was necessary.
