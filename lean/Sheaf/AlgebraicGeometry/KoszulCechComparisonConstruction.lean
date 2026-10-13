/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # The canonical Koszul-to-Čech comparison

Source: Stacks Project, Tags 08CX, 08D0 and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
The power system, its colimit, and its comparison map retain the explicit basis formula
and the totalization sign of Tag 08D1. Existence proofs supply only verification data.
-/

@[expose] public section

universe uK wK vK

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

variable (A : Type uK) [CommRing A] (r : ℕ) (f : Fin r → A)

variable (M : CochainComplex (ModuleCat.{uK} A) ℤ)

/-- The directed Hom-complex diagram with transitions given by precomposition.
The exponent at index e is e+1. Source: Stacks, Tags 08CX and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
Proof: extend koszulOpenTransition by zero and precompose Mathlib's linear cochains.
The chain-map identity and the signed Hom differential give commutation with d.
Identity and composition follow from the diagonal exterior-power comparison laws. -/
theorem koszulCechHomDiagram_exists :
    ∃ D : ℕ ⥤ CochainComplex (ModuleCat.{uK} A) ℤ,
      (∀ e, D.obj e = CochainComplex.moduleHomComplex
        ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M) ∧
      (∀ (a b : ℕ) (h : a ≤ b) (n : ℤ)
        (z : CochainComplex.HomComplex.Cochain
          ((koszulOpenTail A r f a).extend ComplexShape.embeddingDownNat) M n)
        (ha : D.obj a = CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f a).extend ComplexShape.embeddingDownNat) M)
        (hb : D.obj b = CochainComplex.moduleHomComplex
          ((koszulOpenTail A r f b).extend ComplexShape.embeddingDownNat) M),
        ((eqToHom ha.symm ≫ D.map (homOfLE h) ≫ eqToHom hb).f n) z =
          (CochainComplex.HomComplex.Cochain.ofHom
            (HomologicalComplex.extendMap (koszulOpenTransition A r f a b h)
              ComplexShape.embeddingDownNat)).comp z (zero_add n)) := by
  sorry

/-- The specified filtered system of A-linear total Hom complexes.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechHomDiagram : ℕ ⥤ CochainComplex (ModuleCat.{uK} A) ℤ :=
  (koszulCechHomDiagram_exists A r f M).choose

/-- The object identification at every positive exponent.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechHomObjIso (e : ℕ) : (koszulCechHomDiagram A r f M).obj e ≅
    CochainComplex.moduleHomComplex
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat) M :=
  eqToIso ((koszulCechHomDiagram_exists A r f M).choose_spec.1 e)

/-- The direct limit in the category of complexes, hence computed degreewise.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechHomColimit : CochainComplex (ModuleCat.{uK} A) ℤ :=
  colimit (koszulCechHomDiagram A r f M)

/-- Cardinality identifies the Koszul term for a nonempty subset.
Source: Stacks, Tag 08D0 (blueprint: def-sc-koszul-cech-comparison-construction).
Proof: a nonempty finite set has positive cardinality, so truncated subtraction gives
card(J)-1+1 = card(J). -/
theorem koszulCech_basis_card (J : Finset (Fin r)) (hJ : J.Nonempty) :
    J.card = J.card - 1 + 1 := by
  have h : 0 < J.card := Finset.card_pos.mpr hJ
  omega

/-- The extended tail degree attached to the subset J.
Source: Stacks, Tag 08D0 (blueprint: def-sc-koszul-cech-comparison-construction).
Proof: card(J)>0, so negating card(J)-1 gives 1-card(J) in integer degrees. -/
theorem koszulCech_basis_degree (J : Finset (Fin r)) (hJ : J.Nonempty) :
    ComplexShape.embeddingDownNat.f (J.card - 1) = 1 - (J.card : ℤ) := by
  simp only [ComplexShape.embeddingDownNat_f]
  have h : 0 < J.card := Finset.card_pos.mpr hJ
  omega

/-- The ordered exterior basis vector in the Koszul tail, transported by extension.
Source: Stacks, Tag 08D0 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechBasis (e : ℕ) (J : Finset (Fin r)) (hJ : J.Nonempty) :
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X (1 - (J.card : ℤ)) :=
  ((koszulOpenTail A r f e).extendXIso ComplexShape.embeddingDownNat
    (koszulCech_basis_degree r J hJ)).inv
      (exteriorPower.ιMulti A (J.card - 1 + 1)
        (fun i ↦ Finsupp.single (J.orderEmbOfFin (koszulCech_basis_card r J hJ) i) (1 : A)))

/-- The degree equality for evaluating a homogeneous Hom cochain on a basis vector.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction).
Proof: rearrange addition in ℤ. -/
theorem koszulCech_evaluation_degree (J : Finset (Fin r)) (n : ℤ) :
    1 - (J.card : ℤ) + n = n + 1 - (J.card : ℤ) := by
  ring

variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Existence of the compatible Koszul-to-Čech cocone, with the denominator and sign formula.
The equation determines the localized value, since the product of the f_j is invertible
on its principal open. Source: Stacks, Tags 08D0 and 08D1
(blueprint: def-sc-koszul-cech-comparison-construction).
Proof: restrict evaluation on the ordered wedge e_J to D(product f_j), divide by
(product f_j)^(e+1), and multiply by (-1)^(pq+p(p-1)/2), where p=card(J)-1 and q=n-p.
The negative tail differential and the signed Hom differential turn into the alternating
Čech total differential with this sign. A power transition multiplies e_J by product f_j,
so the fractions are compatible. This constructs a cocone without any quasi-coherence
hypothesis; quasi-coherence is only needed for it to be an isomorphism. -/
theorem koszulCechCocone_exists :
    ∃ c : Cocone (koszulCechHomDiagram A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)),
      c.pt = (principalCechFunctor r f).obj F ∧
      ∀ (e : ℕ) (n : ℤ)
        (z : CochainComplex.HomComplex.Cochain
          ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
          (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n)
        (J : {J : Finset (Fin r) // J.Nonempty})
        (hc : c.pt = (principalCechFunctor r f).obj F),
        (∏ j ∈ J.val, f j) ^ (e + 1) •
          (((koszulCechHomObjIso A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
              e).inv ≫ c.ι.app e ≫ eqToHom hc ≫ (principalCechObjIso r f F).hom).f n) z J =
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          (modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
            (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
            ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ))
              (koszulCech_evaluation_degree r J.val n))
                (koszulCechBasis A r f e J.val J.property)) := by
  sorry

/-- The canonical cocone supplied by the explicit localization formula.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechCocone := (koszulCechCocone_exists A r f F).choose

/-- The canonical colimit comparison to alternating Čech totalization.
Source: Stacks, Tag 08D1 (blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechComparison :
    koszulCechHomColimit A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ⟶
        (principalCechFunctor r f).obj F :=
  colimit.desc _ (koszulCechCocone A r f F) ≫
    eqToHom (koszulCechCocone_exists A r f F).choose_spec.1

variable [HasDerivedCategory.{wK}
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace))]
  [HasDerivedCategory.{vK} (ModuleCat.{uK} A)]

/-- The canonical map from the Koszul Hom colimit to RΓ(U,F), through alternating Čech.
Source: Stacks, Tags 08D1 and 08D2
(blueprint: def-sc-koszul-cech-comparison-construction). -/
def koszulCechDerivedComparison :
    DerivedCategory.Q.obj (koszulCechHomColimit A r f
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)) ⟶
        (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map (koszulCechComparison A r f F) ≫
    principalCechDerivedComparison r f F

end
end AlgebraicGeometry
