/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.AffineLineCondensedCohomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ForgetRightDerivedLowerStar

/-! # Ordinary module cohomology of the constant affine-line coefficient

Source: latest blueprint lem-fd-affine-line-constant-cohomology, used in the
zero-slope positive-degree case of lem-fd-cohomology-affine-line-character.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- The ordinary cohomology functor on actual condensed Qbar module sheaves.
Source: blueprint def-weil-ordinary-compact-cohomology, ordinary RΓ formula
(blueprint: lem-fd-cohomology-affine-line-regular-positive). -/
abbrev qlbarGeometricModuleCohomology (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (a : X ⟶ Spec (.of K)) (q : ℕ) :=
  DerivedCategory.singleFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) 0 ⋙
    WeilConjectures.condensedQbarOrdinarySections ℓ K a ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ℓ)) (q : ℤ)

private abbrev abelianSections (X : Scheme.{u}) :=
  Sheaf.sectionsFunctorAt (Scheme.ProEt.topology X) (Scheme.ProEt.mk (𝟙 X))

private def lowerStarAbelianSectionsIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ProEtale.lowerStar Ab.{u + 1} g ⋙ abelianSections Y ≅ abelianSections X :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId Y)).symm ≪≫
    ProEtale.globalSectionsLowerStarIso Ab.{u + 1} g ≪≫
      Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)

private theorem abelian_constant_cohomology_iso
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (e : X ≅ Y) (q : ℕ) :
    Nonempty (((abelianSections X).rightDerived q).obj
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ≅
        ((abelianSections Y).rightDerived q).obj
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := ProEtale.lowerStar Ab.{u + 1} e.inv
  let N := ProEtale.condensedRingObj Λ Y
  let eN : F.obj N ≅ ProEtale.condensedRingObj Λ X :=
    ((ProEtale.upperStarIsoLowerStarInv Ab.{u + 1} e).app N).symm ≪≫
      asIso (ProEtale.condensedPullbackHom Λ e.hom)
  let c := Functor.compRightDerivedObjIso F (abelianSections X)
    (fun I _ ↦ (abelianSections X).rightAcyclic_of_injective (F.obj I)) q N
  exact ⟨((abelianSections X).rightDerived q).mapIso eN.symm ≪≫ c.symm ≪≫
    Functor.rightDerivedObjIsoOfIso (lowerStarAbelianSectionsIso e.inv) q N⟩

private theorem abelian_line_positive
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (q : ℕ) (hq : q ≠ 0) :
    IsZero (((abelianSections (AffineSpace PUnit (Spec (.of K)))).rightDerived q).obj
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace PUnit (Spec (.of K))))) := by
  have hℓ : (ℓ : K) ≠ 0 := by
    intro h
    have hpdiv : p ∣ ℓ := (CharP.cast_eq_zero_iff K p ℓ).1 h
    exact hpℓ ((Nat.dvd_prime (Fact.out : ℓ.Prime)).1 hpdiv |>.resolve_left
      (Fact.out : p.Prime).ne_one)
  have hunit : IsUnit (ℓ : K) := isUnit_iff_ne_zero.mpr hℓ
  have h := (ProEtale.affineLine_condensedQbar_cohomology K (Or.inr inferInstance)
    ℓ hunit K).2 q (Nat.pos_of_ne_zero hq)
  let e := AffineSpace.reindexIso (Spec (.of K))
    (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)
  obtain ⟨eH⟩ := abelian_constant_cohomology_iso ℓ e q
  exact h.of_iso eH

private theorem ordinary_module_abelian_cohomology_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of K))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) (q : ℕ) :
    Nonempty ((forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}).obj
      ((qlbarGeometricModuleCohomology ℓ K X a q).obj N) ≅
        ((abelianSections X).rightDerived q).obj N.X) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let F := ProEtale.CondensedRing.lowerStar Λ a
  let E := ProEtale.CondensedQbarGeometricEvaluation.fieldFiber K ℓ
  let V := forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ProEtale.condensedRingObj Λ X)
  let EY := E ⋙ V
  let eunder : F ⋙ EY ≅ U ⋙ abelianSections X :=
    Functor.isoWhiskerLeft U (lowerStarAbelianSectionsIso a)
  let c₁ : V.obj ((qlbarGeometricModuleCohomology ℓ K X a q).obj N) ≅
      EY.obj ((F.rightDerived q).obj N) :=
    V.mapIso ((E.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).symm.app _ ≪≫
      E.mapIso ((F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso q).app N))
  let c₂ := Functor.rightDerivedCompObjIso F EY q N
  let c₃ := Functor.rightDerivedObjIsoOfIso eunder q N
  let c₄ := Functor.compRightDerivedObjIso U (abelianSections X)
    (fun I _ ↦ (abelianSections X).rightAcyclic_of_injective (U.obj I)) q N
  exact ⟨c₁ ≪≫ c₂.symm ≪≫ c₃ ≪≫ c₄⟩

set_option maxHeartbeats 1600000 in
-- Comparing exact geometric evaluation and injective-resolution sections is expensive.
/-- Positive ordinary cohomology of the regular coefficient module on a geometric
line vanishes.
Source: blueprint lem-fd-affine-line-constant-cohomology, transferred to module
cohomology as required in lem-fd-cohomology-affine-line-character
(blueprint: lem-fd-cohomology-affine-line-regular-positive).

Proof: the condensed coefficient ring is flat as an abelian sheaf, so the free
module functor is exact. Its right adjoint, the module forgetful functor, carries
injective modules to injective abelian sheaves. Thus a module injective resolution
also computes the underlying abelian derived sections. Compare the resulting
complex with module pushforward to Spec K followed by exact geometric evaluation:
underlying underived sections agree, and augmentation-compatible comparison maps
on resolutions give the same derived functor. This identifies the underlying
abelian group of the displayed homology with the abelian-sheaf cohomology of the
pulled-back condensed coefficient. Transport the affine-space coordinate index
from PUnit to ULift (Fin 1), and apply affineLine_condensedQbar_cohomology at K
with the identity algebraic closure. The integer ℓ is a unit since char K=p≠ℓ.
The faithful module forgetful functor reflects zero objects, proving the claim. -/
theorem qlbar_affineLine_regular_higher_cohomology
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (q : ℕ) (hq : q ≠ 0) :
    IsZero ((qlbarGeometricModuleCohomology ℓ K
      (AffineSpace PUnit (Spec (.of K)))
      (AffineSpace PUnit (Spec (.of K)) ↘ Spec (.of K)) q).obj
        (Mod.regular (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (AffineSpace PUnit (Spec (.of K)))))) := by
  let X := AffineSpace PUnit (Spec (.of K))
  let N := Mod.regular (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
  let V := forget₂ (ModuleCat.{u + 1} (PadicAlgCl ℓ)) Ab.{u + 1}
  obtain ⟨e⟩ := ordinary_module_abelian_cohomology_iso ℓ K X
    (X ↘ Spec (.of K)) N q
  have hz := abelian_line_positive p ℓ hpℓ K q hq
  apply (IsZero.iff_id_eq_zero _).2
  apply V.map_injective
  exact (hz.of_iso e).eq_of_src _ _

end AlgebraicGeometry.ArtinSchreierTrace
