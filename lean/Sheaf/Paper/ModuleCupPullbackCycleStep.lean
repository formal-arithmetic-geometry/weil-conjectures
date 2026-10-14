/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.ModuleCohomologyCupProduct
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.Paper.ModuleCupPairingExists
import Sheaf.Paper.ModuleCupPullbackResolutionMaps

/-! # Resolution-cycle compatibility of cup products with pullback

Source: Stacks Project, Tags 0FKV and 01FD.
(blueprint: lem-sc-module-cup-pullback-cycle-step).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

theorem moduleCup_pairing_exists {X : Scheme.{v}} (F G : X.Modules) :
    Nonempty (CupResolutionPairing F G) := by
  exact exists_moduleCupResolutionPairing F G

private theorem resolutionClass_surjective {X : Scheme.{v}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) : Function.Surjective (D.class n) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have : IsIso (HomologicalComplex.homologyMap (T.map D.comparison) n) := D.computes n
  have hcycles : Function.Surjective (cupCycleClass (T.obj D.K) n) :=
    (ModuleCat.epi_iff_surjective
      (((T.obj D.K).sc n).moduleCatCyclesIso.inv ≫ ((T.obj D.K).sc n).homologyπ)).mp
      inferInstance
  exact ((ModuleCat.epi_iff_surjective
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv).mp
      inferInstance).comp
    (((ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (T.map D.comparison) n)).mp inferInstance).comp
        hcycles)

private def pairedCycle {X : Scheme.{v}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K := by
  have ha := a.property
  have hb := b.property
  change (D.left.K.d p ((ComplexShape.up ℕ).next p)).val.app (op ⊤) a.val = 0 at ha
  change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at hb
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel p (p + 1))] at ha
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel q (q + 1))] at hb
  refine ⟨D.pair p q ⊤ a.val b.val, ?_⟩
  change (D.target.K.d (p + q) ((ComplexShape.up ℕ).next (p + q))).val.app (op ⊤)
    (D.pair p q ⊤ a.val b.val) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel (p + q) (p + q + 1))]
  rw [D.leibniz, ha, hb]
  simp

private def transportedCycle {R S : Type v} [Ring R] [Ring S]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (L : CochainComplex (ModuleCat.{v} S) ℕ)
    (φ : ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K ⟶
      ((forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L)
    (n : ℕ) (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (L.sc n).moduleCatLeftHomologyData.K := by
  refine ⟨φ.f n a.val, ?_⟩
  have ha := a.property
  change K.d n ((ComplexShape.up ℕ).next n) a.val = 0 at ha
  change L.d n ((ComplexShape.up ℕ).next n) (φ.f n a.val) = 0
  have h := ConcreteCategory.congr_hom (φ.comm n ((ComplexShape.up ℕ).next n)) a.val
  change L.d n _ (φ.f n a.val) =
    (φ.f ((ComplexShape.up ℕ).next n)) (K.d n _ a.val) at h
  rw [ha] at h
  simpa using h

/-! Resolution-level part of pullback compatibility. -/

set_option maxHeartbeats 400000 in
-- The three computing-resolution maps have large section-complex types.
/--
Resolution-level part of pullback compatibility.
Source: Stacks Project, Tag 0FKV, resolution-level cycle comparison.
(blueprint: lem-sc-module-cup-pullback-cycle-step)
Proof: transport the three complexes of a cup-paired acyclic resolution through
the pullback adjunction unit. The sectionwise tensor comparison identifies the
transported target pairing with the pairing of the transported inputs. Apply
the two `IsModuleCupProduct` characterizations to the resulting cycles.
-/
theorem moduleCup_pullback_cycle_step (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hc : IsModuleCupProduct F G p q cup)
    (cup' : (RingedSpace.moduleCohomology X'.toRingedSpace p).obj
        ((tensorPullback f).obj F) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace q).obj
        ((tensorPullback f).obj G) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).obj
        (@id X'.Modules ((tensorPullback f).obj F ⊗ (tensorPullback f).obj G)))
    (hc' : IsModuleCupProduct ((tensorPullback f).obj F) ((tensorPullback f).obj G)
      p q cup')
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).map
        ((Classical.choose (module_pullback_tensor f)) F G).hom
        (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) (p + q)
          (cup (D.left.class p a) (D.right.class q b))) =
      cup' (moduleCohomologyPullback f F p (D.left.class p a))
        (moduleCohomologyPullback f G q (D.right.class q b)) := by
  obtain ⟨P, E, l, r, t, hl, hr, ht, hpair⟩ :=
    moduleCup_pullback_resolution_maps X X' f F G
  obtain ⟨a₀, ha₀⟩ := resolutionClass_surjective P.left p (D.left.class p a)
  obtain ⟨b₀, hb₀⟩ := resolutionClass_surjective P.right q (D.right.class q b)
  let c₀ := pairedCycle P p q a₀ b₀
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let T' := (RingedSpace.globalSectionsFunctor X'.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let a' := transportedCycle (T.obj P.left.K) (T'.obj E.left.K) l p a₀
  let b' := transportedCycle (T.obj P.right.K) (T'.obj E.right.K) r q b₀
  let c' := transportedCycle (T.obj P.target.K) (T'.obj E.target.K) t (p + q) c₀
  have hc₀ : c₀.val = P.pair p q ⊤ a₀.val b₀.val := rfl
  have hc'cycle : c'.val = E.pair p q ⊤ a'.val b'.val :=
    hpair p q a₀.val b₀.val
  have hcup : cup (D.left.class p a) (D.right.class q b) =
      P.target.class (p + q) c₀ := by
    rw [← ha₀, ← hb₀]
    exact hc P a₀ b₀ c₀ hc₀
  rw [hcup, ← ht (p + q) c₀ c' rfl]
  have hE := (hc' E a' b' c' hc'cycle).symm
  rw [hl p a₀ a' rfl, hr q b₀ b' rfl, ha₀, hb₀] at hE
  exact hE


end
end AlgebraicGeometry.Scheme.Modules
