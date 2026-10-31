/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover

/-! # The affine-line Artin–Schreier cover

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-lem-as-properties/
lem-fd-as-cover-affine-line.md, node statement (blueprint: lem-fd-as-cover-affine-line).

The affine-line cover is identified with affine one-space by sending the quotient
coordinate `T` to the affine coordinate `y`. The transported structural morphism
and prime-field translations are recorded explicitly.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

/-- The Artin–Schreier cover of the affine line is the affine line, with its
structural map and prime-field action in the displayed coordinates.

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-lem-as-properties/
lem-fd-as-cover-affine-line.proof.md, all four proof steps (blueprint: lem-fd-as-cover-affine-line).
Proof: (1) Apply `artinSchreierCover_affinePresentation` from lem-fd-as-cover and
`affine_morphism_relative_spec` from lem-weil-pbc-affine-morphism-relative-spec to
identify the cover with the spectrum of `B = k[x][T]/(T^p-T-x)`.
(2) By lem-asd-polynomial-quotient-hom-equivalence (`AdjoinRoot.liftAlgHom`),
evaluation `T ↦ y`, `x ↦ y^p-y` gives a map `B → k[y]`. The inverse sends
`y` to the class of `T`; it respects the base map because `x = T^p-T` in `B`.
(3) Both composites fix coefficients and the polynomial generators, so they are
identities, by the finite-sum description in def-weil-polynomial-ring.
(4) Apply contravariant spectrum (def-weil-affine-spectrum). The structural map
sends `x` to `y^p-y`. The translations of lem-fd-as-cover send `T` to `T+a`,
so their conjugates fix coefficients and send `y` to `y+a`, which determines
exactly the standard affine-space translation. -/
theorem artinSchreierCover_affineLine (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [Finite k] [CharP k p] :
    ∃ e : (artinSchreierCover p (AffineSpace PUnit (Spec (CommRingCat.of k)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)).left ≅
        AffineSpace PUnit (Spec (CommRingCat.of k)),
      (e.hom.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit) =
        artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (CommRingCat.of k)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)) ∧
      (e.inv ≫ (artinSchreierCover p (AffineSpace PUnit (Spec (CommRingCat.of k)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)).hom =
        AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) p) ∧
      ∃ σ : Multiplicative (ZMod p) →* Aut
          (artinSchreierCover p (AffineSpace PUnit (Spec (CommRingCat.of k)))
            (AffineSpace.coord (Spec (CommRingCat.of k)) PUnit.unit)),
        (∀ a : ZMod p, (σ (Multiplicative.ofAdd a)).hom.left.appTop
            (artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (.of k)))
              (AffineSpace.coord (Spec (.of k)) PUnit.unit)) =
          artinSchreierCoverCoordinate p (AffineSpace PUnit (Spec (.of k)))
              (AffineSpace.coord (Spec (.of k)) PUnit.unit) +
            (a.val : Γ((artinSchreierCover p (AffineSpace PUnit (Spec (.of k)))
              (AffineSpace.coord (Spec (.of k)) PUnit.unit)).left, ⊤))) ∧
        ∀ a : ZMod p,
          e.inv ≫ (σ (Multiplicative.ofAdd a)).hom.left ≫ e.hom =
            AffineSpace.translation (fun _ : PUnit.{u + 1} ↦
              (Scheme.ΓSpecIso (.of k)).inv.hom (a.val : k)) := by
  sorry

end AlgebraicGeometry
