/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The boundary exchange for the Verdier dual on `Dctf`

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k` and schemes
separated of finite type over `k`, this file proves

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom`:
  `Rf^! RHom(M, N) ≅ RHom(Lf^* M, Rf^! N)`;

- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`
  (`cor-weil-boundary-duality-discharge`): for a closed immersion `i : Z ⟶ T` the boundary
  exchange `i^* 𝔻_T L ≅ 𝔻_Z Ri^! L` holds on `Dctf(T)`.

The canonical exchange map of the blueprint is not constructed; the exchange is stated as the
existence of an isomorphism, as in `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- The exceptional inverse image of an internal hom: for `f : X ⟶ Y` admitting a
compactification and a finite ring `Λ`,

`Rf^! RHom_Y(M, N) ≅ RHom_X(Lf^* M, Rf^! N)`.

Both sides are right adjoint to functors of `Z ∈ D(X_ét)`: the left one to `M ⊗ᴸ Rf_! Z`, the
right one to `Rf_!(Lf^* M ⊗ᴸ Z)`, and these agree by the projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and the symmetry of `⊗ᴸ`. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj
        ((RHom(Y)[ModuleCat.{u + 1} Λ].obj (op M)).obj N) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M))).obj
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj N)) := by
  have := isIso_projectionMap_of_finite Λ f
  obtain ⟨βY⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Y
  obtain ⟨βX⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  let adj₁ := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).comp
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) M)
  let adj₂ := (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)).comp
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f)
  let P : R(f)_![ModuleCat.{u + 1} Λ] ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj M ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M) ⋙
        R(f)_![ModuleCat.{u + 1} Λ] :=
    NatIso.ofComponents (fun Z ↦ asIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app Z).app M))
      fun g ↦ NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} Λ) f).naturality g) M
  let e := Functor.isoWhiskerLeft (R(f)_![ModuleCat.{u + 1} Λ]) (βY.app M) ≪≫ P ≪≫
    Functor.isoWhiskerRight (βX.app _).symm (R(f)_![ModuleCat.{u + 1} Λ])
  exact ⟨(adj₁.rightAdjointUniq (adj₂.ofNatIsoLeft e.symm)).app N⟩

/-- Blueprint `cor-weil-boundary-duality-discharge`: Discharge of the boundary duality input.

Let `k` be algebraically closed, and let `i : Z ⟶ T` be a closed immersion of schemes
separated of finite type over `k` (for instance two locally closed pieces of a separated
finite-type `Y`). For every `L ∈ Dctf(T, Λ)` the boundary exchange
`β_L : i^* 𝔻_T L ⟶ 𝔻_Z Ri^! L` is an isomorphism; here it is stated as the existence of an
isomorphism. That `𝔻_T` preserves `Dctf(T, Λ)`, the first clause of the boundary duality input,
is `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem nonempty_iso_leftDerivedUpperStar_verdierDual [IsAlgClosed k] {Z T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasCompactification aT] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [HasCompactification (i ≫ aT)]
    {L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T L) :
    Nonempty ((L((i)^*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj (op L)) ≅
      (verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aT)).obj
        (op ((R(i)^![ModuleCat.{u + 1} Λ]).obj L))) := by
  -- `𝔻_Z (i^* K) ≅ Ri^! 𝔻_T K`, from `Ri^! RHom(K, ω_T) ≅ RHom(i^* K, Ri^! ω_T)` and
  -- `Ri^! ω_T ≅ ω_Z`
  have hex (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      Nonempty ((verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aT)).obj
          (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
        (R(i)^![ModuleCat.{u + 1} Λ]).obj ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj (op K))) := by
    obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ i K (dualizingComplex _ aT)
    obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ i aT
    exact ⟨((RHom(Z)[ModuleCat.{u + 1} Λ]).obj _).mapIso e₂.symm ≪≫ e₁.symm⟩
  have hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T
      ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj (op L)) :=
    constructibleFiniteTor_verdierDual Λ aT hL
  have hiD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z
      ((L((i)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj (op L))) :=
    constructibleFiniteTor_leftDerivedUpperStar _ i hD
  obtain ⟨e₁⟩ := hex ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj (op L))
  obtain ⟨b₁⟩ := nonempty_iso_verdierDual_verdierDual Λ aT hL
  obtain ⟨b₂⟩ := nonempty_iso_verdierDual_verdierDual Λ (i ≫ aT) hiD
  -- `𝔻_Z (i^* 𝔻_T L) ≅ Ri^! L`, then dualize once more on `Z`
  let e : (verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aT)).obj
      (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual (ModuleCat.{u + 1} Λ) aT).obj
        (op L)))) ≅ (R(i)^![ModuleCat.{u + 1} Λ]).obj L :=
    e₁ ≪≫ (R(i)^![ModuleCat.{u + 1} Λ]).mapIso b₁.symm
  exact ⟨b₂ ≪≫ (verdierDual (ModuleCat.{u + 1} Λ) (i ≫ aT)).mapIso e.symm.op⟩

end Etale

end AlgebraicGeometry
