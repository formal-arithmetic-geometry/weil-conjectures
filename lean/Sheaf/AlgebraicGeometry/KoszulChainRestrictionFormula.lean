/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction
import Sheaf.AlgebraicGeometry.KoszulOpenHomChainEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Sheaf.AlgebraicGeometry.KoszulOpenSystem

/-! # The restriction formula for a Koszul chain representative

Source: Stacks Project, Tags 06Z0, 08DC and 08DD.
(blueprint: lem-sc-koszul-chain-restriction-formula).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem naturalEquiv_add
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] {A : Type*} [CommRing A]
    (R : C ⥤ D) [R.Additive] (S : C ⥤ ModuleCat A) [S.Additive] (P : D)
    (b : ∀ E : C, (P ⟶ R.obj E) ≃ S.obj E)
    (hb : ∀ (E E' : C) (g : E ⟶ E') (ψ : P ⟶ R.obj E),
      b E' (ψ ≫ R.map g) = S.map g (b E ψ))
    (E : C) (ψ ψ' : P ⟶ R.obj E) : b E (ψ + ψ') = b E ψ + b E ψ' := by
  let p : P ⟶ R.obj (E ⊞ E) := ψ ≫ R.map biprod.inl + ψ' ≫ R.map biprod.inr
  have hp₁ : p ≫ R.map biprod.fst = ψ := by simp [p, ← R.map_comp]
  have hp₂ : p ≫ R.map biprod.snd = ψ' := by simp [p, ← R.map_comp]
  have hp : p ≫ R.map (biprod.fst + biprod.snd) = ψ + ψ' := by
    rw [R.map_add, Preadditive.comp_add, hp₁, hp₂]
  rw [← hp, hb, S.map_add]
  change S.map biprod.fst (b (E ⊞ E) p) +
    S.map biprod.snd (b (E ⊞ E) p) = _
  rw [← hb, ← hb, hp₁, hp₂]

set_option maxHeartbeats 1000000 in
-- Nested derived functors and the affine adjunction require extra elaboration heartbeats.
/-- The canonical comparison on an actual chain representative is restriction followed
by inverse augmentation and evaluation at one.
Source: Stacks Project, Equation 36.9.4.1, Tag 08DC; Tags 08D1 and 08DD.
(blueprint: lem-sc-koszul-chain-restriction-formula)

Proof: On the principal intersection indexed by J, apply the canonical affine counit
s to the module chain map g. The Koszul-to-Cech cocone evaluates g on the ordered wedge
and divides by the product of the f_j to exponent e+1. Contracting the localized full
Koszul complex with a generator whose f_j is invertible shows that the same fraction
represents restriction composed with the inverse augmentation. The totalization sign
in the cocone is precisely the sign converting the negative tail differential into
the alternating Cech differential. Pass this equality to degree-zero homology; hz
identifies the cycle represented by g. The Cech-to-derived-sections map carries it to
the corresponding derived section. Evaluation at one identifies sections with Hom
from the restricted structure object, additively, and postcomposition by eF transports
the target. This supplies b and the equality for every psi satisfying the displayed
augmentation equation; invertibility is given by
affine_perfect_koszul_principal_unit_iso at exponent e+1. Empty cover and zero ring yield
zero groups; no exactness of
filtered colimits, regularity, boundedness of F or injectivity is used. -/
theorem koszulChain_restriction_formula
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (eF : DerivedCategory.Q.obj F ≅ E.obj)
    (s : ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
      (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F) ≅ F)
    (hs : ∀ n : ℤ, s.hom.f n = Scheme.Modules.fromTildeΓ (R := .of A) (F.X n)) :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u}
          ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
        (D := SheafOfModules.{u}
          (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
    let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
    let D := koszulCechHomDiagram A r f M
    let C := koszulCechHomColimit A r f M
    let β := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app C).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        (koszulCechDerivedComparison A r f F ≫
          (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map eF.hom)
    ∃ b : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃+
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.obj E.obj),
      ∀ (e : ℕ)
        (g : (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat ⟶ M)
        (z : (CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).cycles 0),
        (CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).iCycles 0 z =
            CochainComplex.HomComplex.Cochain.ofHom g →
        ∀ ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E.obj,
          R.map (koszulOpenUnit A r f e) ≫ ψ =
            R.map (DerivedCategory.Q.map
              (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).map g) ≫
                DerivedCategory.Q.map s.hom ≫ eF.hom) →
          b ψ = β (HomologicalComplex.homologyMap (colimit.ι D e) 0
            (HomologicalComplex.homologyMap (koszulCechHomObjIso A r f M e).inv 0
              ((CochainComplex.moduleHomComplex
                ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).homologyπ
                  0 z))) := by
  classical
  dsimp only
  let R := ((SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u}
        ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
      (D := SheafOfModules.{u}
        (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
  let M := ((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F
  let T := (koszulOpenTilde A).mapHomologicalComplex (.up ℤ)
  let D := koszulCechHomDiagram A r f M
  let C := koszulCechHomColimit A r f M
  let η := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0
  obtain ⟨b, hb, hchain⟩ := koszulOpenHom_chain_evaluation A r f
  let b' : (R.obj (koszulOpenStructure A) ⟶ R.obj E.obj) ≃+ H.obj (G.obj E.obj) :=
    { b E.obj with map_add' := naturalEquiv_add R (G ⋙ H) _ b hb E.obj }
  refine ⟨b', ?_⟩
  intro e g z hz ψ hψ
  let t : koszulOpenSheafComplex A r f e ⟶ F := T.map g ≫ s.hom
  have ht : koszulOpenHomTranspose A r f F e t = g := by
    let : (tilde.functor (.of A)).Additive :=
      ⟨fun {_ _} g h ↦ tilde.map_add g h⟩
    let : (moduleSpecΓFunctor (R := .of A)).Additive :=
      ⟨fun {_ _} _ _ ↦ rfl⟩
    let adj := (tilde.adjunction (R := .of A)).mapHomologicalComplex (.up ℤ)
    change adj.homEquiv _ _ t = g
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    have hc : adj.counit.app F = s.hom := by
      apply HomologicalComplex.Hom.ext
      funext n
      exact (hs n).symm
    rw [hc]
    rfl
  have hzclass : koszulHomChainClass g =
      (CochainComplex.moduleHomComplex
        ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M).homologyπ 0 z := by
    let K := CochainComplex.moduleHomComplex
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M
    let S := K.sc 0
    have hc : S.moduleCatCyclesIso.inv
        ⟨CochainComplex.HomComplex.Cochain.ofHom g,
          CochainComplex.HomComplex.δ_ofHom g⟩ = z := by
      apply (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance
      change ((S.moduleCatCyclesIso.inv ≫ S.iCycles) _) = _
      rw [S.moduleCatCyclesIso_inv_iCycles]
      exact hz.symm
    change (S.moduleCatCyclesIso.inv ≫ S.homologyπ) _ = _
    change S.homologyπ (S.moduleCatCyclesIso.inv _) = _
    rw [hc]
    rfl
  let ψ₀ := ψ ≫ R.map eF.inv
  have hψ₀ : R.map (koszulOpenUnit A r f e) ≫ ψ₀ =
      R.map (DerivedCategory.Q.map t) := by
    dsimp only [ψ₀]
    rw [← Category.assoc, hψ, ← R.map_comp]
    apply congrArg R.map
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (DerivedCategory.Q.map_comp (T.map g) s.hom).symm
  have hψ' : ψ₀ ≫ R.map eF.hom = ψ := by
    dsimp only [ψ₀]
    rw [Category.assoc, ← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id]
  change b E.obj ψ = _
  rw [← hψ', hb, hchain F hF e t ψ₀ hψ₀]
  dsimp only [koszulOpenHomStageClass]
  rw [ht, hzclass]
  let K := CochainComplex.moduleHomComplex
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M
  let j := (koszulCechHomObjIso A r f M e).inv
  have hj := η.inv.naturality j
  have hi := η.inv.naturality (colimit.ι D e)
  change HomologicalComplex.homologyMap j 0 ≫ (η.app (D.obj e)).inv =
    (η.app K).inv ≫ H.map (DerivedCategory.Q.map j) at hj
  change HomologicalComplex.homologyMap (colimit.ι D e) 0 ≫ (η.app C).inv =
    (η.app (D.obj e)).inv ≫ H.map (DerivedCategory.Q.map (colimit.ι D e)) at hi
  change (H.map (G.map eF.hom))
    ((H.map (koszulCechDerivedComparison A r f F))
      ((H.map (DerivedCategory.Q.map (colimit.ι D e)))
        ((H.map (DerivedCategory.Q.map j)) ((η.app K).inv (K.homologyπ 0 z))))) = _
  have hji : (η.app K).inv ≫ H.map (DerivedCategory.Q.map j) ≫
      H.map (DerivedCategory.Q.map (colimit.ι D e)) =
      HomologicalComplex.homologyMap j 0 ≫
        HomologicalComplex.homologyMap (colimit.ι D e) 0 ≫ (η.app C).inv := by
    rw [← Category.assoc, ← hj, Category.assoc, ← hi]
  change ((η.app K).inv ≫ H.map (DerivedCategory.Q.map j) ≫
    H.map (DerivedCategory.Q.map (colimit.ι D e)) ≫
    H.map (koszulCechDerivedComparison A r f F) ≫ H.map (G.map eF.hom))
      (K.homologyπ 0 z) = _
  have hall : (η.app K).inv ≫ H.map (DerivedCategory.Q.map j) ≫
      H.map (DerivedCategory.Q.map (colimit.ι D e)) ≫
      H.map (koszulCechDerivedComparison A r f F) ≫ H.map (G.map eF.hom) =
      HomologicalComplex.homologyMap j 0 ≫
        HomologicalComplex.homologyMap (colimit.ι D e) 0 ≫ (η.app C).inv ≫
          H.map (koszulCechDerivedComparison A r f F ≫ G.map eF.hom) := by
    calc
      _ = ((η.app K).inv ≫ H.map (DerivedCategory.Q.map j) ≫
          H.map (DerivedCategory.Q.map (colimit.ι D e))) ≫
          H.map (koszulCechDerivedComparison A r f F) ≫ H.map (G.map eF.hom) := by
            simp only [Category.assoc]
      _ = (HomologicalComplex.homologyMap j 0 ≫
          HomologicalComplex.homologyMap (colimit.ι D e) 0 ≫ (η.app C).inv) ≫
          H.map (koszulCechDerivedComparison A r f F) ≫ H.map (G.map eF.hom) := by
            rw [hji]
      _ = _ := by rw [H.map_comp]; simp only [Category.assoc]
  rw [hall]
  rfl

end AlgebraicGeometry
