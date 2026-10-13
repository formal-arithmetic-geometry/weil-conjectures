/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups D4 and T3
-/
module

public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.Paper.CechCupResolutionComparisonExists
import Sheaf.Paper.CechCupResolutionTotalPairing

/-! # Resolution representatives for a Cech cup cocycle

Source: Stacks Project, Tag 0FKV, specialized to sheaves in degree zero.
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

private theorem cupCycleClass_surjective {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem cupResolutionClass_surjective {X : Scheme.{v}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) : Function.Surjective (D.class n) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have : IsIso (HomologicalComplex.homologyMap (T.map D.comparison) n) := D.computes n
  exact ((ModuleCat.epi_iff_surjective
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv).mp
      inferInstance).comp
    (((ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (T.map D.comparison) n)).mp inferInstance).comp
        (cupCycleClass_surjective (T.obj D.K) n))

private theorem cupPair_exists_cycle {X : Scheme.{v}} {F G : X.Modules}
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

set_option maxHeartbeats 800000 in
-- Computing identifications use several ring and functor instance conversions.
/-- Two Cech cocycles and their cup admit compatible representatives in a computing
resolution pairing. This statement concerns the pairing of actual resolution
sections, before any sheaf or Cech cup product on cohomology is chosen.
Source: Stacks Project, Tag 0FKV, proof of Lemma 20.31.4, and Tag 07MB
(blueprint: lem-sc-cech-cup-resolution-representatives).

Proof: exists_cupCechResolutionComparison supplies a computing resolution
pairing D and canonical alpha/beta comparison data for its three resolutions.
It uses Godement/flasque resolutions and their injective comparisons. The Cech-to-total beta
maps carry a, b and c to cocycles. The global-sections-to-total alpha maps are
quasi-isomorphisms for these flasque resolutions. The D-class maps are
surjective, being the projection from cycles followed by two isomorphisms;
choose global cocycles a' and b' with the prescribed canonical classes. Leibniz
makes D.pair p q top a'.val b'.val a cocycle c'. In the signed total Cech
pairing, alpha preserves the pairing. The augmentation preserves the tensor of
sections, hence beta preserves the Cech cup pairing. Tag 0FKV's commuting diagram
therefore identifies the class of c' with the canonical image of c. The classes
of a' and b' are likewise the canonical images of a and b. Comparison with
injective resolutions identifies these classes with D.left.class,
D.right.class and D.target.class and with the specified canonical comparisons.
Degree zero uses the augmentation pairing; vanishing classes or an empty scheme
cause no exception, since cycles representing zero can be chosen to be zero. -/
theorem cechCup_resolution_representatives (X : Scheme.{v}) {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cG : ((cechComplexFunctor U).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison U G q cG)
    (cFG : ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)))
    (hcFG : IsModuleCechComparison U (F ⊗ G) (p + q) cFG)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    ∃ (D : CupResolutionPairing F G)
      (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
      (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
      (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
      D.left.class p a' = cF (cupCycleClass _ p a) ∧
      D.right.class q b' = cG (cupCycleClass _ q b) ∧
      D.target.class (p + q) c' = cFG (cupCycleClass _ (p + q) c) ∧
      c'.val = D.pair p q ⊤ a'.val b'.val := by
  obtain ⟨D, ⟨A⟩, ⟨B⟩, ⟨C⟩⟩ := exists_cupCechResolutionComparison X U hU F G
  obtain ⟨a', ha⟩ := cupResolutionClass_surjective D.left p (cF (cupCycleClass _ p a))
  obtain ⟨b', hb⟩ := cupResolutionClass_surjective D.right q (cG (cupCycleClass _ q b))
  obtain ⟨c', hc'⟩ := cupPair_exists_cycle D p q a' b'
  obtain ⟨cup, halpha, hbeta⟩ := cupCechResolution_total_pairing U D A B C p q
  refine ⟨D, a', b', c', ha, hb, ?_, hc'⟩
  have hleft : HomologicalComplex.homologyMap A.alpha p (cupCycleClass _ p a') =
      HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a) := by
    rw [← A.alpha_class, ha, A.beta_class p cF hcF a]
  have hright : HomologicalComplex.homologyMap B.alpha q (cupCycleClass _ q b') =
      HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b) := by
    rw [← B.alpha_class, hb, B.beta_class q cG hcG b]
  have htarget : (C.iso (p + q)).hom (D.target.class (p + q) c') =
      (C.iso (p + q)).hom (cFG (cupCycleClass _ (p + q) c)) := by
    exact (C.alpha_class (p + q) c').trans
      ((halpha a' b' c' hc').symm.trans
        ((congrArg₂ (fun x y ↦ cup x y) hleft hright).trans
          ((hbeta a b c hc).trans (C.beta_class (p + q) cFG hcFG c).symm)))
  exact (ModuleCat.mono_iff_injective (C.iso (p + q)).hom).mp inferInstance htarget

end
end AlgebraicGeometry.Scheme.Modules
