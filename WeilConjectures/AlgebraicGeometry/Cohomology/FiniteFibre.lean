/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Coherent modules, and the higher direct images along a proper morphism with a finite fibre

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsCoherent`: coherent `𝒪_X`-modules in the sense of Stacks
  `01BV`: of finite type, and every map from a finite free module over an open has a kernel of
  finite type.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isCoherent_iff`: on a locally noetherian scheme, coherent
  means quasi-coherent of finite type.
- `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalk`: a module with vanishing stalks is
  zero.
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_restrict_of_isAffineOpen`: quasi-coherent
  modules have no higher cohomology on affine opens.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`: the direct image of a
  quasi-coherent module along a quasi-compact quasi-separated morphism is quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.isZero_stalk_higherDirectImage_of_finite_preimage`: for `f`
  proper with finite fibre over `y`, `(R^p f_* ℱ)_y = 0` for `p > 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A sheaf of `𝒪_X`-modules `ℱ` is *coherent* if it is of finite type and, for every open
`U ⊆ X`, every finite index type `ι` and every map `φ : 𝒪_U^{⊕ι} ⟶ ℱ|_U`, the kernel of `φ` is of
finite type.

This is the notion of Stacks `01BV`; `AlgebraicGeometry.Scheme.Modules.isCoherent` is the
(in general different) notion "quasi-coherent of finite presentation", and the two agree on
locally noetherian schemes (`AlgebraicGeometry.Scheme.Modules.isCoherent_iff`).

(blueprint: `pqf-def-coherent`) -/
class IsCoherent (ℱ : X.Modules) : Prop where
  isFiniteType : SheafOfModules.IsFiniteType (R := X.ringCatSheaf) ℱ
  isFiniteType_kernel (U : X.Opens) (ι : Type u) [Finite ι]
    (φ : SheafOfModules.free (R := U.toScheme.ringCatSheaf) ι ⟶ ℱ.restrict U.ι) :
    SheafOfModules.IsFiniteType (R := U.toScheme.ringCatSheaf) (kernel φ)

/-- **Coherent = quasi-coherent of finite type on a locally noetherian scheme.**

(blueprint: `pqf-lem-coherent-ft-locnoeth`) -/
theorem isCoherent_iff [IsLocallyNoetherian X] (ℱ : X.Modules) :
    ℱ.IsCoherent ↔ SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ ∧
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) ℱ :=
  sorry

/-- **A sheaf with vanishing stalks is zero.** If all stalks of the underlying abelian sheaf of an
`𝒪_X`-module `ℱ` vanish, then `ℱ = 0`.

(blueprint: `pqf-lem-sheaf-zero-stalks`) -/
theorem isZero_of_isZero_stalk (ℱ : X.Modules) (h : ∀ x : X, IsZero (ℱ.presheaf.stalk x)) :
    IsZero ℱ := by
  have h' : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) :=
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2 h
  rw [IsZero.iff_id_eq_zero]
  exact (SheafOfModules.toSheaf X.ringCatSheaf).map_injective (h'.eq_of_src _ _)

/-- **Vanishing of cohomology on affine opens.** For a quasi-coherent `𝒪_X`-module `ℱ` and an
affine open `U ⊆ X`, `H^p(U, ℱ|_U) = 0` for `p > 0`.

(blueprint: `pqf-lem-affine-vanishing`) -/
theorem subsingleton_H_restrict_of_isAffineOpen (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {U : X.Opens} (hU : IsAffineOpen U)
    (p : ℕ) : Subsingleton ((ℱ.restrict U.ι).H (p + 1)) :=
  have : IsAffine U := hU
  subsingleton_H_succ_of_isAffine _ p

/-- **Direct images of quasi-coherent modules.** For a quasi-compact quasi-separated morphism
`f : X ⟶ S`, the direct image `f_* ℱ` of a quasi-coherent `𝒪_X`-module is quasi-coherent.

(blueprint: `pqf-lem-pushforward-qcoh`) -/
theorem isQuasicoherent_pushforward {S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) ((pushforward f).obj ℱ) :=
  sorry

/-- **Higher direct images along a proper morphism vanish at points with finite fibre.** Let
`f : X ⟶ Y` be proper with `Y` locally noetherian, and let `y : Y` have a finite fibre
`f⁻¹{y}`. Then for every coherent `𝒪_X`-module `ℱ`, `(R^p f_* ℱ)_y = 0` for `p > 0`.

The blueprint deduces this from the theorem on formal functions. Here `f` is finite over an open
neighbourhood `V` of `y`
(`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`,
Stacks 02UP), so `(R^p f_* ℱ)|_V = R^p (f|_V)_* (ℱ|_{f⁻¹V})` vanishes, `f|_V` being affine.

(blueprint: `pqf-lem-fff-vanishing`) -/
theorem isZero_stalk_higherDirectImage_of_finite_preimage {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] [HasInjectiveResolutions X.Modules] (y : Y)
    (hy : (f ⁻¹' {y}).Finite) (ℱ : X.Modules) [ℱ.IsCoherent] {p : ℕ} (hp : 0 < p) :
    IsZero (((higherDirectImage f p).obj ℱ).presheaf.stalk y) := by
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := ((isCoherent_iff ℱ).1 inferInstance).1
  obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hy
  have := isGrothendieckAbelian (f ⁻¹ᵁ V).toScheme
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ V.ι _ _
    (isPullback_morphismRestrict f V).flip (p + 1)
  have hz : IsZero (((higherDirectImage f (p + 1)).obj ℱ).restrict V.ι) :=
    (isZero_higherDirectImage_of_isAffineHom (f ∣_ V) _ (Nat.succ_pos p)).of_iso e.symm
  have hz' := (TopCat.Presheaf.stalkFunctor _ (⟨y, hyV⟩ : V)).map_isZero
    ((toPresheaf _).map_isZero hz)
  exact hz'.of_iso ((restrictStalkNatIso V.ι ⟨y, hyV⟩).app _).symm

end AlgebraicGeometry.Scheme.Modules
