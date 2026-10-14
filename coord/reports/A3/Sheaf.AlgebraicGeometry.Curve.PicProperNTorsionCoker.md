## What changed

Retire the duplicate `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker` in
`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker`, leaving an empty retirement
stub. Adapt its sole caller `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` by
inlining the exact cokernel proof as local hc; the parent's signature is unchanged.
Its proof-only imports now use PicardDecomposition and Mathlib.Algebra.Group.TypeTags.Hom.
Repoint the cokernel DAG node to the cokernel conjunct of the surviving parent.
Change record: `coord/changes/pic_proper_ntorsion_coker.md`.

## Proved and sorry left

Holes closed: none (0 of 0 local holes in the baseline item).
Holes added: none. Split-off declarations: none.
The standalone theorem was already locally proved; its proof is preserved in
`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion`, rather than claimed as new
progress. This is a duplicate repair and import pruning, not a decomposition.
The scratch axiom check of the original cokernel theorem reports propext,
Classical.choice, Quot.sound and sorryAx through existing imported dependencies.
There are no delivered local sorries, hollow definitions or arbitrary data choices.

## No longer needed

The parent no longer imports `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker`;
this module leaves the target import closure. All nine imports of that module
are removed because it now contains no declarations.
No old proof dependency is abandoned: `lem-sc-pic-proper-decomposition` and
`lem-sc-pic-proper-ntorsion-div` remain used in the parent's local hc calculation.
No DAG node is deleted and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The report described only a copied proof, while this item is queued as a duplicate
repair. Such a restoration does not resolve the repair. The first comparison saw
an already-retired module and inlined caller; the delivery tool refreshed its base,
where the declaration and caller still existed. The final adaptation covers that
base coherently and preserves the reviewed proof.
The upstream theorem name quoted in the repair was not found in this machine's
source checkout (direct rg; msearch.py grep was also recorded). No proof is based
on an unavailable declaration: the original decomposition/divisibility argument
is retained inside the parent, with no new hypothesis or mathematical shortcut.

## Second reading by A3

1. Statements and visibility: compared the complete original and sandbox modules
using diff. The only removed declaration is the explicitly documented duplicate.
The sole caller's existing signature, docstring and visibility are byte for byte
unchanged; all definitions and target statements are unchanged.

2. Proof and axioms: compiled the first worker's theorem (2.4 s, clean), and a
scratch copy with #print axioms (2.3 s), which showed only propext, Classical.choice,
Quot.sound and inherited sorryAx. The complete repaired set was compiled in import
order with lcompile.py (parent 3.4 s, empty stub 0.2 s). The dry run passes.
The launcher axiom probe runs on the adapted parent; on the empty stub its
run_cmd requires Lean.Elab.Command and cannot run. There are no declarations
in that stub, so axiom checking it is vacuous; no unused import was added
just to make the probe command available. No delivered local sorry or forbidden declaration occurs.
The original cokernel proof is copied verbatim, with only indentation changed,
into the parent's typed hc block. Its use of witnesses is in a proposition proof;
no data definition is created by choosing an arbitrary unproved witness.

3. Split statements: none. Read both imported component modules and checked the
modulo-degree kernel/image argument. n = 0 is excluded by (n : k) != 0; n = 1 gives
the trivial quotient. No statement is weakened and no new hole is introduced.

4. Top-down route and pruning: the original Picard splitting, degree-zero
divisibility and first-isomorphism argument is retained. Read
`dag/units/sk-thm-curveestimate.json`: its realized statement and steps are unchanged.
The only removed route module is the redundant standalone cokernel wrapper.
Its sole original caller is adapted in the same delivery; no caller is missed.

5. DAG agreement: read the cokernel node's proof, proof_deps, proof_origin and lean
record. The two proof dependencies remain accurate. Update lean to the surviving
parent's cokernel conjunct and proof_origin to local hc. No new nodes are needed.

Changed in this reading: retired the duplicate instead of restoring it, adapted
the sole caller without changing its signature, removed unused imports, updated
the cokernel node's Lean location, and corrected the report and change record.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion`: the original imports the retired
module and calls `Scheme.Hom.pic_proper_ntorsion_coker`; against the empty module
that identifier no longer exists. Replace that proof-only import with the two
imports needed by the inlined proof, and replace only the hc call with the exact
former proof. The delivery tool performs the counterfactual compile of the original
against the delivered dependencies and records its compiler error.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion
Original against changed dependencies failed:
```
/tmp/forced-adaptation-_mxfycw8/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:70:13: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
/tmp/forced-adaptation-_mxfycw8/lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsion.lean:68:77: error: unsolved goals
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

(with the modules compiled into /tmp/forced-adaptation-_mxfycw8/.lbuild) [2.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
