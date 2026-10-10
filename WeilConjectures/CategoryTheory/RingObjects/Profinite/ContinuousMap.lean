/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.Topology.ContinuousMap.Algebra
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.RingObjects.CommRingPresheaf

/-!

# The condensed ring of continuous maps into a topological ring

Let `T` be a commutative topological ring. The presheaf `S ↦ C(S, T)` of continuous maps on the
category `Profinite` of profinite sets, with the coherent topology (the "condensed site": its
sheaves of types are the condensed sets, `CondensedSet`), is a sheaf (it is the restriction of
mathlib's `TopCat.toSheafCompHausLike`), and it is a presheaf of commutative rings for the
pointwise operations. This file defines it as a sheaf of commutative rings
`Profinite.continuousMapRingSheaf T : Sheaf (coherentTopology Profinite) CommRingCat`, the
"condensed ring" associated with `T`. Its underlying abelian sheaf
`(Profinite.continuousMapRingSheaf T).toAb` is a commutative ring object of the category of
abelian sheaves on `Profinite`, for the monoidal structure given by the sheafification of the
objectwise tensor product
(`CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall`).

Following [Bhatt–Scholze, Section 4.2 and Definition 6.8.1], the pro-étale site of a point
`Spec k`, for `k` separably closed, is the category of profinite sets, and the coefficient
sheaves `ℤ_ℓ`, `ℚ_ℓ`, `𝒪_E`, `E` and `ℚ̄_ℓ` of `ℓ`-adic cohomology on the pro-étale site of a scheme
`X` are the pullbacks along `X → Spec ℤ` of the corresponding condensed rings, see
`WeilConjectures.CategoryTheory.RingObjects.Profinite.EllAdic` for the condensed rings and
`WeilConjectures.CategoryTheory.RingObjects.Pullback` for the pullbacks.

## Main definitions

* `Profinite.continuousMapRingPresheaf`: the presheaf of commutative rings `S ↦ C(S, T)` on
  `Profinite`.
* `Profinite.continuousMapRingSheaf`: the sheaf of commutative rings `S ↦ C(S, T)` for the
  coherent topology.
* `Profinite.continuousMapRingSheafMap`: the morphism of sheaves of commutative rings induced by
  a continuous ring homomorphism `T →+* T'`.

## Universes

The category `Profinite.{u}` has `Hom`-types in `Type u` and is essentially small in `u + 1`,
so sheaves on it take values in `CommRingCat.{u + 1}` and `Ab.{u + 1}`, following the convention
of the `SixFunctors` folder for the pro-étale site of a scheme in `Scheme.{u}`. The sections
`C(S, T)`, which live in `Type u` for `T : Type`, are therefore lifted to `Type (u + 1)`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace Profinite

/-- The category of abelian sheaves on `Profinite.{u}` for the coherent topology is Grothendieck
abelian: `Profinite.{u}` is essentially small in `u + 1`. -/
instance : IsGrothendieckAbelian.{u + 1} (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} Profinite.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (coherentTopology Profinite.{u}) Ab.{u + 1}

/-- Effective epimorphisms of profinite sets are surjective. -/
lemma surjective_of_effectiveEpi ⦃S T : Profinite.{u}⦄ (f : S ⟶ T) (hf : EffectiveEpi f) :
    Function.Surjective f :=
  ((Profinite.effectiveEpi_tfae f).out 0 2).mp hf

section Ring

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The presheaf of commutative rings `S ↦ C(S, T)` of continuous maps into the commutative
topological ring `T` on the category of profinite sets, lifted to `Type (u + 1)`. -/
noncomputable def continuousMapRingPresheaf : Profinite.{u}ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj S := CommRingCat.of (ULift.{u + 1} C(S.unop, T))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

lemma continuousMapRingPresheaf_obj (S : Profinite.{u}ᵒᵖ) :
    (continuousMapRingPresheaf T).obj S = CommRingCat.of (ULift.{u + 1} C(S.unop, T)) :=
  rfl

lemma continuousMapRingPresheaf_map_apply {S S' : Profinite.{u}ᵒᵖ} (f : S ⟶ S')
    (g : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingPresheaf T).map f g = ULift.up (g.down.comp f.unop.hom.hom) :=
  rfl

/-- The presheaf of types underlying `continuousMapRingPresheaf T` is mathlib's presheaf
`S ↦ C(S, T)` of continuous maps into the topological space `T` lifted to `Type (u + 1)`
(`TopCat.toSheafCompHausLike`), which is a sheaf for the coherent topology. -/
noncomputable def continuousMapRingPresheafForgetIso :
    continuousMapRingPresheaf T ⋙ forget CommRingCat.{u + 1} ≅
      (TopCat.toSheafCompHausLike.{u + 1, u} (fun X ↦ TotallyDisconnectedSpace X)
        (TopCat.of (ULift.{u + 1} T))
        surjective_of_effectiveEpi).obj :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun g := (⟨ULift.up, continuous_uliftUp⟩ : C(T, ULift.{u + 1} T)).comp g.down
      invFun h := ULift.up ((⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u + 1} T, T)).comp h)
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

/-- The presheaf `S ↦ C(S, T)` is a sheaf for the coherent topology on profinite sets. -/
lemma isSheaf_continuousMapRingPresheaf :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (continuousMapRingPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat.{u + 1}),
    Presheaf.isSheaf_of_iso_iff (continuousMapRingPresheafForgetIso T)]
  exact (TopCat.toSheafCompHausLike.{u + 1, u} (fun X ↦ TotallyDisconnectedSpace X)
    (TopCat.of (ULift.{u + 1} T))
    surjective_of_effectiveEpi).property

/-- The sheaf of commutative rings `S ↦ C(S, T)` of continuous maps into the commutative
topological ring `T` on the category of profinite sets with the coherent topology, the
"condensed ring" associated with `T`. Its underlying abelian sheaf
`(continuousMapRingSheaf T).toAb` is a commutative ring object with the pointwise
multiplication. -/
noncomputable def continuousMapRingSheaf :
    Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  ⟨continuousMapRingPresheaf T, isSheaf_continuousMapRingPresheaf T⟩

lemma continuousMapRingSheaf_obj :
    (continuousMapRingSheaf T).obj = continuousMapRingPresheaf T :=
  rfl

variable {T} {T' : Type} [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
presheaves of commutative rings `C(-, T) ⟶ C(-, T')`. -/
noncomputable def continuousMapRingPresheafMap :
    continuousMapRingPresheaf T ⟶ continuousMapRingPresheaf T' where
  app _ := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

lemma continuousMapRingPresheafMap_app_apply (S : Profinite.{u}ᵒᵖ)
    (g : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingPresheafMap φ hφ).app S g =
      ULift.up ((⟨φ, hφ⟩ : C(T, T')).comp g.down) :=
  rfl

/-- Postcomposition with a continuous ring homomorphism `φ : T →+* T'`, as a morphism of
sheaves of commutative rings `C(-, T) ⟶ C(-, T')` on profinite sets. -/
noncomputable def continuousMapRingSheafMap :
    continuousMapRingSheaf T ⟶ continuousMapRingSheaf T' :=
  ⟨continuousMapRingPresheafMap φ hφ⟩

lemma continuousMapRingSheafMap_hom :
    (continuousMapRingSheafMap φ hφ).hom = continuousMapRingPresheafMap φ hφ :=
  rfl

@[simp]
lemma continuousMapRingSheafMap_id :
    continuousMapRingSheafMap (RingHom.id T) continuous_id = 𝟙 (continuousMapRingSheaf T) :=
  rfl

lemma continuousMapRingSheafMap_comp {T'' : Type} [TopologicalSpace T''] [CommRing T'']
    [IsTopologicalRing T''] (ψ : T' →+* T'') (hψ : Continuous ψ) :
    continuousMapRingSheafMap (ψ.comp φ) (hψ.comp hφ) =
      continuousMapRingSheafMap φ hφ ≫ continuousMapRingSheafMap ψ hψ :=
  rfl

end Ring

section RingObject

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

noncomputable example : MonObj (continuousMapRingSheaf.{u} T).toAb := inferInstance

noncomputable example : IsCommMonObj (continuousMapRingSheaf.{u} T).toAb := inferInstance

end RingObject

end Profinite
