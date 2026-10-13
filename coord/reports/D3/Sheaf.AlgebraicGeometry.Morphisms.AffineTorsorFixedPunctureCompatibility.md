## What changed

Repaired the returned interface by replacing the false arbitrary-`θ`/arbitrary-`q`
statement with the canonical over-`Spec H` formulation. The parameter is now an
isomorphism in `CategoryTheory.Over`, whose two structural maps are the pullback
second projection and `V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B))`.
The proof is the defining commuting triangle `Over.w θ.hom`. The DAG node already
records this corrected statement and remains synchronized with the Lean module.

The only downstream source occurrence is `AffineTorsorFixedPunctureDescentCore`;
its theorem body was already `sorry` and therefore made no application of the old
interface. No caller signature could be adapted without changing a separate,
still-disputed theorem.

## Proved and sorry left

Closed `affine_torsor_fixed_orbits_compatibility` (the returned hole). The module
contains no remaining `sorry` in this declaration; the private counterexample is
also fully proved. The imported downstream `affine_torsor_fixed_orbits` theorem
remains a separate `sorry` in its own module and is unchanged.

## No longer needed

The arbitrary scheme morphism `q` parameter and the unrestricted scheme
isomorphism `θ` interface are no longer needed. The proof uses only
`Mathlib.AlgebraicGeometry.Limits` and `Mathlib.CategoryTheory.Comma.Over.Basic`.
The old counterexample is retained as certified historical evidence but is not a
proof dependency.

## Where the brief, the DAG or earlier work was wrong

The returned interface quantified over arbitrary `θ` and `q`, which is false (the
`Spec (ℤ × ℤ)` component-swap counterexample demonstrates this). The corrected
statement follows the human-approved repair recorded in the change record and the
DAG node: the structural map to `Spec H` is canonical and compatibility is encoded
by an isomorphism in `Over (Spec H)`.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

1. The corrected theorem statement matches the DAG node and the human-approved
   over-`Spec H` interface.
2. `lcompile.py` compiles both the repaired module and its downstream importer.
3. The proof is exactly `Over.w θ.hom`, with no new axioms or hollow definitions.
4. The forced adaptation is limited to the already-sorry downstream theorem; its
   public signature is unchanged.
5. Change record: `coord/changes/affine-torsor-fixed-puncture-over-H.md`.

## Second reading by D3

1. Compared the delivered compatibility module with the repository version. The
   corrected theorem has the same canonical over-`Spec H` statement recorded in
   the change record and node; no existing declaration signature was changed
   accidentally. The forced DescentCore adaptation preserves its public signature.
2. Compiled both delivered modules with `lcompile.py`; both compile without errors
   or warnings. The compatibility proof is exactly `Over.w θ.hom`, and the private
   counterexample is proved without the disputed theorem.
3. Checked the corrected statement against the counterexample and the canonical
   algebra map. It is true and precisely expresses the required over-base
   compatibility; no new theorem or hollow definition was added.
4. Checked that the proof uses only `Mathlib.AlgebraicGeometry.Limits` and the
   plain proof import `Mathlib.CategoryTheory.Comma.Over.Basic`; the node proof,
   declaration text, and proof origin now match the Lean proof.
5. The unit route remains unchanged: the compatibility node is still attached to
   `sk-prop-input-spreading`, and the descent-core caller is retained only as the
   forced adaptation required by the interface repair.

Changed during second reading: synchronized the delivered DAG node's statement,
Lean declaration text, proof steps, and proof origin with the repaired module, and
added this review record. No additional holes were introduced; the only remaining
hole is the pre-existing disputed `affine_torsor_fixed_orbits` theorem in the
forced-adaptation module.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore
Original against changed dependencies failed:
```
/tmp/forced-adaptation-yjvqoqxa/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescentCore.lean:78:76: error: Application type mismatch: The argument
  θ
has type
  pullback p (Spec.map (CommRingCat.ofHom ι)) ≅
    ↑(PrimeSpectrum.basicOpen ((algebraMap (↑H) ((k : Fin m) → ↥(⨅ ζ, (ρ ↑ζ).equalizer (AlgHom.id (↑H) C)))) (ι g)))
but is expected to have type
  Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
    Over.mk
      (Opens.ι (PrimeSpectrum.basicOpen ((algebraMap (↑H) B) (ι g))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (↑H) B)))
in the application
  affine_torsor_fixed_orbits_compatibility θ

Note: The following definitions were not unfolded because their definition is not exposed:
  getLimitCone ↦ 3

(with the modules compiled into /tmp/forced-adaptation-yjvqoqxa/.lbuild) [4.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
