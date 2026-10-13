/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.Paper.CupCechFlasquePairing
import Sheaf.Paper.CupCechFlasqueComparison
import Sheaf.Paper.CupCechTotalPairing

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

/-- Lift a homology class along a quasi-isomorphism to a kernel cocycle. -/
private theorem cupCech_lift {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) [QuasiIso f]
    (n : ℕ) (z : L.homology n) :
    ∃ a : (K.sc n).moduleCatLeftHomologyData.K,
      HomologicalComplex.homologyMap f n (cupCycleClass K n a) = z := by
  have hπ : Function.Surjective (cupCycleClass K n) :=
    (ModuleCat.epi_iff_surjective
      ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance
  exact ((ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap f n)).mp inferInstance).comp hπ z

/-- Leibniz makes the sectionwise product of two global cocycles a cocycle. -/
private theorem cupCech_pair_exists_cycle {X : Scheme.{v}} {F G : X.Modules}
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
-- Elaborating three total-complex lifts and their dependent cocycle types needs extra heartbeats.
/-- Two Cech cocycles and their cup admit compatible representatives in a computing
resolution pairing. This statement concerns the pairing of actual resolution
sections, before any sheaf or Cech cup product on cohomology is chosen.
Source: Stacks Project, Tag 0FKV, proof of Lemma 20.31.4, and Tag 07MB
(blueprint: lem-sc-cech-cup-resolution-representatives).

Proof: use Godement resolutions of F, G and F tensor G with their natural
sectionwise pairing. These are nonnegative flasque resolutions; compare them to
injective resolutions to obtain a CupResolutionPairing D. The Cech-to-total beta
maps carry a, b and c to cocycles. The global-sections-to-total alpha maps are
quasi-isomorphisms for these flasque resolutions, so choose global cocycles a'
and b' representing the two images under inverse alpha on homology. Leibniz
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
  obtain ⟨D, hD, hE, hT⟩ := exists_cupCechFlasquePairing F G
  obtain ⟨hαD, hcmpD⟩ := cupCech_flasque_comparison U hU D.left hD
  obtain ⟨hαE, hcmpE⟩ := cupCech_flasque_comparison U hU D.right hE
  obtain ⟨_, hcmpT⟩ := cupCech_flasque_comparison U hU D.target hT
  have := hαD
  have := hαE
  obtain ⟨a', ha⟩ := cupCech_lift (cupCechAlpha U D.left) p
    (HomologicalComplex.homologyMap (cupCechBeta U D.left) p (cupCycleClass _ p a))
  obtain ⟨b', hb⟩ := cupCech_lift (cupCechAlpha U D.right) q
    (HomologicalComplex.homologyMap (cupCechBeta U D.right) q (cupCycleClass _ q b))
  obtain ⟨c', hc'⟩ := cupCech_pair_exists_cycle D p q a' b'
  obtain ⟨t, htα, htβ⟩ := exists_cupCech_total_pairing U D p q
  refine ⟨D, a', b', c', hcmpD p cF hcF a a' ha, hcmpE q cG hcG b b' hb, ?_, hc'⟩
  apply hcmpT (p + q) cFG hcFG c c'
  calc
    _ = t (HomologicalComplex.homologyMap (cupCechAlpha U D.left) p
          (cupCycleClass _ p a'))
        (HomologicalComplex.homologyMap (cupCechAlpha U D.right) q
          (cupCycleClass _ q b')) := (htα a' b' c' hc').symm
    _ = t (HomologicalComplex.homologyMap (cupCechBeta U D.left) p
          (cupCycleClass _ p a))
        (HomologicalComplex.homologyMap (cupCechBeta U D.right) q
          (cupCycleClass _ q b)) := by rw [ha, hb]
    _ = _ := htβ a b c hc

end
end AlgebraicGeometry.Scheme.Modules
