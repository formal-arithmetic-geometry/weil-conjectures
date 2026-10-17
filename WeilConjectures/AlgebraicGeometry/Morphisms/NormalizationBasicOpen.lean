/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# The relative normalization over a basic open

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `U ⊆ S` an affine open with `f⁻¹ U`
affine, `B = Γ(S, U)`, `L = Γ(X, f⁻¹ U)` and `h ∈ B`. The relative normalization of `S` in
`X` is étale over the basic open `D(h)` if and only if the integral closure of `B_h` in `L_h` is
étale over `B_h`, where `B_h = Γ(S, D(h))` and `L_h = Γ(X, f⁻¹ D(h))`
(`AlgebraicGeometry.Scheme.Hom.exists_etale_integralClosure_away` and
`AlgebraicGeometry.Scheme.Hom.etale_fromNormalization_basicOpen`). The statements are phrased
for arbitrary localizations `B' = B[1/h]` and `L' = L[1/h]`, as in
`RingTheory.DepthTwo.exists_etale_integralClosure_of_two_le_height'`; they are used in the
depth-two step of the proof of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The sections over an open `V'` equal to the basic open `D(r)` of a section `r` over an affine
open `V` are the localization of `Γ(X, V)` at `r`. -/
lemma IsAffineOpen.isLocalization_away_of_eq {X : Scheme.{u}} {V V' : X.Opens}
    (hV : IsAffineOpen V) (r : Γ(X, V)) (hle : V' ≤ V) (e : V' = X.basicOpen r) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    IsLocalization.Away r Γ(X, V') := by
  subst e
  exact hV.isLocalization_basicOpen r

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/-- If the relative normalization of `S` in `X` is étale over the basic open `D(h)` of an affine
open `U ⊆ S` with `f⁻¹ U` affine, then, with `B = Γ(S, U)` and `L = Γ(X, f⁻¹ U)`, there
are localizations `B' = B[1/h]` and `L' = L[1/h]` such that the integral closure of `B'` in `L'` is
étale over `B'` (namely `B' = Γ(S, D(h))` and `L' = Γ(X, f⁻¹ D(h))`). -/
lemma exists_etale_integralClosure_away {U : S.Opens} (hU : IsAffineOpen U)
    (hfU : IsAffineOpen (f ⁻¹ᵁ U)) (h : Γ(S, U))
    (hE : Etale ((f.fromNormalization ⁻¹ᵁ S.basicOpen h).ι ≫ f.fromNormalization)) :
    letI := (f.app U).hom.toAlgebra
    ∃ (B' L' : Type u) (_ : CommRing B') (_ : CommRing L') (_ : Algebra Γ(S, U) B')
      (_ : IsLocalization.Away h B') (_ : Algebra Γ(X, f ⁻¹ᵁ U) L')
      (_ : IsLocalization.Away (algebraMap Γ(S, U) Γ(X, f ⁻¹ᵁ U) h) L') (_ : Algebra B' L')
      (_ : Algebra Γ(S, U) L') (_ : IsScalarTower Γ(S, U) B' L')
      (_ : IsScalarTower Γ(S, U) Γ(X, f ⁻¹ᵁ U) L'),
      Algebra.Etale B' (integralClosure B' L') := by
  let := (f.app U).hom.toAlgebra
  have hle : S.basicOpen h ≤ U := S.basicOpen_le h
  have hle' : f ⁻¹ᵁ S.basicOpen h ≤ f ⁻¹ᵁ U := f.preimage_mono hle
  let := (S.presheaf.map (homOfLE hle).op).hom.toAlgebra
  let := (X.presheaf.map (homOfLE hle').op).hom.toAlgebra
  let := (f.app (S.basicOpen h)).hom.toAlgebra
  let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    (f.app U ≫ X.presheaf.map (homOfLE hle').op).hom.toAlgebra
  have h1 : IsScalarTower Γ(S, U) Γ(S, S.basicOpen h) Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    .of_algebraMap_eq' congr(($(f.naturality (homOfLE hle).op)).hom).symm
  have h2 : IsScalarTower Γ(S, U) Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    .of_algebraMap_eq' rfl
  have h3 : IsLocalization.Away h Γ(S, S.basicOpen h) := hU.isLocalization_basicOpen h
  have h4 : IsLocalization.Away (algebraMap Γ(S, U) Γ(X, f ⁻¹ᵁ U) h)
      Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    hfU.isLocalization_away_of_eq _ hle' (Scheme.preimage_basicOpen f h)
  exact ⟨_, _, _, _, _, h3, _, h4, _, _, h1, h2,
    f.etale_integralClosure_of_etale_fromNormalization (hU.basicOpen h) hE⟩

set_option backward.isDefEq.respectTransparency false in
/-- Conversely to `AlgebraicGeometry.Scheme.Hom.exists_etale_integralClosure_away`, if for all
localizations `B' = B[1/h]` and `L' = L[1/h]` of `B = Γ(S, U)` and `L = Γ(X, f⁻¹ U)` the
integral closure of `B'` in `L'` is étale over `B'`, then the relative normalization of `S` in
`X` is étale over `D(h)`. -/
lemma etale_fromNormalization_basicOpen {U : S.Opens} (hU : IsAffineOpen U)
    (hfU : IsAffineOpen (f ⁻¹ᵁ U)) (h : Γ(S, U))
    (H : letI := (f.app U).hom.toAlgebra
      ∀ (B' L' : Type u) [CommRing B'] [CommRing L'] [Algebra Γ(S, U) B']
        [IsLocalization.Away h B'] [Algebra Γ(X, f ⁻¹ᵁ U) L']
        [IsLocalization.Away (algebraMap Γ(S, U) Γ(X, f ⁻¹ᵁ U) h) L'] [Algebra B' L']
        [Algebra Γ(S, U) L'] [IsScalarTower Γ(S, U) B' L']
        [IsScalarTower Γ(S, U) Γ(X, f ⁻¹ᵁ U) L'],
        Algebra.Etale B' (integralClosure B' L')) :
    Etale ((f.fromNormalization ⁻¹ᵁ S.basicOpen h).ι ≫ f.fromNormalization) := by
  let := (f.app U).hom.toAlgebra
  have hle : S.basicOpen h ≤ U := S.basicOpen_le h
  have hle' : f ⁻¹ᵁ S.basicOpen h ≤ f ⁻¹ᵁ U := f.preimage_mono hle
  let := (S.presheaf.map (homOfLE hle).op).hom.toAlgebra
  let := (X.presheaf.map (homOfLE hle').op).hom.toAlgebra
  let := (f.app (S.basicOpen h)).hom.toAlgebra
  let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    (f.app U ≫ X.presheaf.map (homOfLE hle').op).hom.toAlgebra
  have : IsScalarTower Γ(S, U) Γ(S, S.basicOpen h) Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    .of_algebraMap_eq' congr(($(f.naturality (homOfLE hle).op)).hom).symm
  have : IsScalarTower Γ(S, U) Γ(X, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    .of_algebraMap_eq' rfl
  have : IsLocalization.Away h Γ(S, S.basicOpen h) := hU.isLocalization_basicOpen h
  have : IsLocalization.Away (algebraMap Γ(S, U) Γ(X, f ⁻¹ᵁ U) h)
      Γ(X, f ⁻¹ᵁ S.basicOpen h) :=
    hfU.isLocalization_away_of_eq _ hle' (Scheme.preimage_basicOpen f h)
  exact f.etale_fromNormalization_of_isAffineOpen (hU.basicOpen h) (H _ _)

end Scheme.Hom

end AlgebraicGeometry
