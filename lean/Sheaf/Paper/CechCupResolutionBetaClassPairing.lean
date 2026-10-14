/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N3, U4 and S2
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct
import Sheaf.Paper.CechCupSignedAxisPairing

/-! # The augmentation axis of the signed total Cech pairing

Source: Stacks Project, Tags 07MB and 0FKV.
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

private theorem betaPairing_cycleClass_surjective {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem betaPairing_pair_exists_cycle {X : Scheme.{v}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    ∃ c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K,
      c.val = D.pair p q ⊤ a.val b.val := by
  have ha := a.property
  have hb := b.property
  change (D.left.K.d p ((ComplexShape.up ℕ).next p)).val.app (op ⊤) a.val = 0 at ha
  change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at hb
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel p (p + 1))] at ha
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel q (q + 1))] at hb
  refine ⟨⟨D.pair p q ⊤ a.val b.val, ?_⟩, rfl⟩
  change (D.target.K.d (p + q) ((ComplexShape.up ℕ).next (p + q))).val.app (op ⊤)
    (D.pair p q ⊤ a.val b.val) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel (p + q) (p + q + 1))]
  rw [D.leibniz, ha, hb]
  simp

private theorem betaPairing_alpha_surjective {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} {D : CupAcyclicResolution F}
    (A : CupCechResolutionComparison U D) (n : ℕ) :
    Function.Surjective (fun z ↦
      HomologicalComplex.homologyMap A.alpha n (cupCycleClass _ n z)) := by
  let := A.alpha_quasiIso
  exact ((ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap A.alpha n)).mp inferInstance).comp
      (betaPairing_cycleClass_surjective _ n)

/-- The augmentation axis computes the already characterized sheaf cup product.
Source: Stacks Project, Tag 07MB and Tag 0FKV, final comparison diagram.
(blueprint: lem-sc-cech-cup-resolution-beta-class-pairing)

Proof: form the signed Alexander--Whitney total pairing using D.pair on each
resolution/Cech summand, with sign (-1)^(i*s) for Cech degree i of the first
factor and resolution degree s of the second. Restriction compatibility and
D.leibniz give the cochain identity; the Cech differential cancels adjacent
omitted-vertex terms. Bilinearity and this identity give quotient descent to
homology. The alpha components lie in Cech degree zero, so their signs are one;
the resulting product is the D.pair product of global resolution cycles.
A.alpha_quasiIso and B.alpha_quasiIso let every total homology input be lifted
to a global resolution cycle. The alpha_class equations identify its class
with the inverse of A.iso or B.iso. The characterization hcup therefore
identifies the total pairing with cup transported along A.iso, B.iso, C.iso.
The beta components lie in resolution degree zero. Here the signs are also
one, and D.augmentation_pair identifies their product with the augmentation
of cechCupCochain. The beta_f equations identify these components with the
specified beta maps. Apply homology and then C.iso.inv to this beta equality.
This calculation is sectionwise and does not require a covering hypothesis:
the needed global comparison isomorphisms are explicitly part of A and B.
If an index set or an input is empty or zero, bilinearity gives the same formula.
The statement fixes cup by hcup, rather than asserting the formula for an
arbitrary bilinear map. -/
theorem cupCechResolution_beta_class_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hcup : IsModuleCupProduct F G p q cup)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
      p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
      q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    cup ((A.iso p).inv (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)))
      ((B.iso q).inv (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))) =
        (C.iso (p + q)).inv
          (HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c)) := by
  obtain ⟨t, halpha, hbeta⟩ := cupCech_signed_axis_pairing U D
    A.alpha A.beta A.alpha_f A.beta_f
    B.alpha B.beta B.alpha_f B.beta_f
    C.alpha C.beta C.alpha_f C.beta_f p q
  obtain ⟨a', ha'⟩ := betaPairing_alpha_surjective U A p
    (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a))
  obtain ⟨b', hb'⟩ := betaPairing_alpha_surjective U B q
    (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))
  dsimp only at ha' hb'
  obtain ⟨c', hc'⟩ := betaPairing_pair_exists_cycle D p q a' b'
  have ha : (A.iso p).inv
      (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)) =
      D.left.class p a' := by
    rw [← ha', ← A.alpha_class p a']
    simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  have hb : (B.iso q).inv
      (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b)) =
      D.right.class q b' := by
    rw [← hb', ← B.alpha_class q b']
    simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  have ht := halpha a' b' c' hc'
  rw [ha', hb', hbeta a b c hc] at ht
  have ht' := congrArg (fun z ↦ (C.iso (p + q)).inv z) ht
  rw [← C.alpha_class (p + q) c'] at ht'
  simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] at ht'
  rw [ha, hb, hcup D a' b' c' hc']
  exact ht'.symm

end
end AlgebraicGeometry.Scheme.Modules
