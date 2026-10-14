## What changed

Retired the standalone `pic_proper_ntorsion_coker` module body and adapted its caller
`lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean`. The caller now removes the
retired-module import, imports `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` and
`Mathlib.Algebra.Group.TypeTags.Hom`, and inlines the complete cokernel proof as the typed
local `hc`. The parent theorem signature and visibility are unchanged. Change record: `coord/changes/withdraw-retired-pic-proper-ntorsion-coker-module.md`. The cokernel node's
`lean.statement` now records the exact multiline parent theorem signature and retains the
note identifying the cokernel conjunct.

## Proved and sorry left

The parent theorem's local cokernel proof is complete. No declarations with `sorry` remain
in the delivered files; no holes were added or split off.

## No longer needed

The standalone duplicate declaration and its module import are no longer needed. The
cokernel mathematics remains needed as the second conjunct of
`Scheme.Hom.pic_proper_ntorsion`, where it is now proved locally. No DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The returned delivery incorrectly claimed that the baseline caller was already adapted and
had no importer. The baseline `PicProperNTorsion` still imported
`PicProperNTorsionCoker` and called `Scheme.Hom.pic_proper_ntorsion_coker`; removing that
module therefore required the forced caller adaptation below. The node's collapsed
one-line parent signature also did not match the adapted theorem declaration; it is now
recorded verbatim in multiline form.

## New nodes

None.

## Forced adaptations

`lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean` is held by A3. Against the
delivered empty retired module, the baseline compiler error is:

```text
unknown constant 'AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker'
```

Exact necessary changes:

```diff
-import Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker
+import Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
+import Mathlib.Algebra.Group.TypeTags.Hom
...
-  have hc := Scheme.Hom.pic_proper_ntorsion_coker f n _hn
+  have hc : Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
+      Multiplicative (ZMod n)) := by
+    -- complete cokernel proof inlined here
```

The local proof is the complete former cokernel proof, with no change to the parent
signature or visibility.

## Earlier second reading (a previous round; superseded)

1. Compared the adapted caller with the baseline: only the forced import replacement and
   local proof insertion are changed; the theorem signature and visibility are identical.
2. Compiled the adapted caller and the retired empty module with `lcompile.py`; both pass.
3. Checked the node JSON: its `lean.statement` is the exact multiline parent signature and
   its note still identifies the cokernel conjunct.
4. Confirmed no declaration with `sorry`, `axiom`, or unsafe feature was introduced.

## Second reading by A4

1. Compared both delivered modules with the repository versions. The parent theorem's
   signature and visibility are byte-for-byte unchanged; the retired module only removes
   its duplicate declaration, while the caller changes only the forced import and proof.
   Verdict: no accidental statement change.
2. Compiled the retired module and the adapted caller with `lcompile.py`; both compile
   without errors or warnings. The delivered files contain no `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by`, or `extern`. Verdict: the proof is accepted, and the local
   cokernel calculation is kernel-checked.
3. The local `hc` proof follows the node exactly: Picard decomposition, divisibility of
   the degree-zero factor, integer-cast map to `ZMod n`, kernel equality, and the first
   isomorphism theorem. The node records the parent declaration verbatim and identifies
   the cokernel conjunct. Verdict: the node and Lean proof agree, with no new split-off
   statement.
4. The standalone declaration duplicated the parent theorem's cokernel conjunct and had
   no independent downstream use. Retiring it removes its unused public imports; the
   caller keeps the required decomposition and TypeTags imports. Verdict: pruning is
   complete and the shortest available proof remains in the parent theorem.
5. The parent theorem remains the realized node for the unit route; its torsion and
   divisibility components are still called through their existing declarations, while
   the cokernel component is inlined without bypassing the decomposition/divisibility
   steps. Verdict: the unit route is preserved.

The second reading found no further repair. The forced adaptation of the A3-held caller
is necessary because the baseline imported and called the retired declaration; it compiles
against the changed dependency and preserves the public interface.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-qm1n25ia/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:70:13: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
/tmp/forced-adaptation-qm1n25ia/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:68:77: error: unsolved goals
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

(with the modules compiled into /tmp/forced-adaptation-qm1n25ia/.lbuild) [2.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
