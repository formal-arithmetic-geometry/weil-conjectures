## What changed

Retire the duplicate public theorem
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker (upstream review #1428).
Retain its module as a declaration-free compatibility import, with its six original
public imports. The sole caller, Scheme.Hom.pic_proper_ntorsion, now contains the
complete existing cokernel calculation as its local hc proof. Its signature, visibility,
public imports, torsion proof and divisibility proof stay identical. Update both DAG
proof records and point the cokernel node to the corresponding conjunct of the caller.

Change record: coord/changes/retire-pic-proper-ntorsion-coker-duplicate.md.

## Proved and sorry left

Zero baseline direct sorries, zero holes closed, zero holes added, zero split off.
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker is removed.
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion remains completely proved.
No delivered declaration contains sorry. lcompile.py --all compiled both files
successfully (2.9 seconds for the caller, 1.9 seconds for the compatibility module).
The required deliver3.py --no-push printed OK; nothing was pushed.

## No longer needed

Remove the caller's import of Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker.
This module is no longer reached through that caller and declares no theorem.
Remove its proof imports PicardDecomposition, PicProperNTorsionDiv and TypeTags.Hom.
The caller imports these directly for its local cokernel proof. The compatibility
module preserves the public imports. The node lem-sc-pic-proper-ntorsion-coker remains
as documentation of the conjunction, but is no longer a separate proof dependency of
lem-sc-pic-proper-ntorsion. No decomposition or divisibility argument is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a sorry-bearing module; this checkout already proves the
item, and the specific task is removal of its duplicated public theorem.
The cited Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient and Curve/Jacobian module
are absent from the available sources. The existing cokernel calculation is therefore
retained locally in the already-existing conjunction theorem, rather than introducing
an unavailable upstream import or another public duplicate.

The earlier attempt deleted the entire module, but deliver3.py's counterfactual ignores
deleted.txt and still imports the baseline artifact. Retaining a declaration-free module
provides a compatibility import and lets the ordinary changed-dependency check verify
that the original caller fails. No tool was edited or bypassed.
The earlier searches are retained in searches.jsonl. Edge cases remain valid: n=1
works; n=0 is excluded by the nonzero cast hypothesis. The unit's route is unchanged.

## Forced adaptations

Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion is unclaimed in the checked snapshot.
It is the sole direct importer and declaration user. Its original proof fails against
the repaired module with:

```text
error(lean.unknownIdentifier): Unknown constant
  AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker
```

Replace the removed private import with PicardDecomposition and TypeTags.Hom, and
replace the single theorem call with the original cokernel proof. These are the only
changed Lean lines of the caller. The caller's existing signature and visibility are
identical. The deliver3.py counterfactual validates the original failure and the adapted
compilation; the final dry run passes.


## Second reading by A3

1. **No accidental visible changes.** I compared both delivered Lean modules with the
repository versions. The compatibility module removes only the retired declaration and
keeps all six original public imports. The caller changes only proof-local imports and the
proof of its existing conjunct; its theorem signature and visibility are byte-for-byte
unchanged. Verdict: pass.

2. **Proof and axioms.** Both modules compile with `lcompile.py --all`. The delivered
modules contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
The retired module has no declarations; the caller's local cokernel calculation is fully
proved and uses the existing decomposition and divisibility lemmas. Verdict: pass.

3. **Statements and split nodes.** No new statement is introduced. The existing cokernel
node remains the documented component of `pic_proper_ntorsion`, with its original
statement and source; it is not used as a duplicate theorem. The local proof follows its
two recorded steps and the cited Mathlib first-isomorphism APIs. Verdict: pass.

4. **Pruning and imports.** The caller no longer imports the retired compatibility module,
and instead imports the decomposition and type-tag modules required by its local proof;
the compatibility module intentionally preserves its six public imports for downstream
source compatibility. The reported removed dependency and imports agree with the proof,
and no unit step is bypassed. Verdict: pass.

5. **DAG and unit route.** The `lem-sc-pic-proper-ntorsion` node records the local
`hc` calculation and the three actual proof dependencies. The cokernel node points to the
corresponding conjunction component and remains split/documentary. The unit's realized
route is unchanged. Verdict: pass.

I changed only this report: recorded the second reading and corrected the prior note that
the reading remained outstanding.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-_b1tzkg9/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:70:13: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
/tmp/forced-adaptation-_b1tzkg9/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:68:77: error: unsolved goals
k : Type u
inst✝⁴ : Field k
inst✝³ : IsAlgClosed k
C : Scheme
f : C ⟶ Spec (CommRingCat.of k)
inst✝² : IsConnectedCurve f
inst✝¹ : Smooth f
inst✝ : IsProper f
n : ℕ
_hn : ↑n ≠ 0
ht : Nonempty (↥(powMonoidHom n).ker ≃* Multiplicative (Fin (2 * genus f) → ZMod n))
⊢ Nonempty (↥(powMonoidHom n).ker ≃* Multiplicative (Fin (2 * genus f) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n).range ≃* Multiplicative (ZMod n)) ∧ ∀ L ∈ picZero f, ∃ M ∈ picZero f, M ^ n = L

(with the modules compiled into /tmp/forced-adaptation-_b1tzkg9/.lbuild) [1.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
