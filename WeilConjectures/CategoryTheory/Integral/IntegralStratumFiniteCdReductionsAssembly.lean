/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.IntegralStratumFiniteCdReductionsHeartBound
public import WeilConjectures.CategoryTheory.IntegralStratumFiniteCdReductionsSectionsBound
public import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralStratumHomFormula
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
public import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.IntegralDualTorsionHeartSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution

/-!
# Hom bound for a bounded classical torsion complex on an integral stratum

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the dual-tensor and bounded-heart steps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

private theorem integral_ring_sheaf_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    DerivedNakayama.integerRingSheaf l E =
      letI := spectralNorm.normedField (Padic l) E
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E) := by
  have hmetric : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have htop := congrArg (fun m ↦ m.toUniformSpace.toTopologicalSpace) hmetric
  apply continuous_ring_eq_of_topology
  exact congrArg (fun t : TopologicalSpace E ↦ TopologicalSpace.induced
    (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) htop.symm

private theorem heart_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : supportModules (IntegralQuotient.integral l E) S)
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (F : supportModules (IntegralQuotient.integral l E) S)
    (hF : IsClassicalAbelian F.X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X) :
    ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
        ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
          (((derivedTensor (IntegralQuotient.integral l E) S).obj
            (stratumModuleDual (IntegralQuotient.integral l E) S L)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  let P (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
    ∀ [IsCommMonObj R.X] (M : supportModules R.X S),
      HasFiniteConstantLocalModel R.X S M →
      ∀ (G : supportModules R.X S),
        IsClassicalAbelian G.X ∧ IsEllPowerTorsionLocal l (Fact.out : l.Prime) G.X →
        ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
          IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
            ((stratumModuleDerivedSections R.X S).obj
              (((derivedTensor R.X S).obj (stratumModuleDual R.X S M)).obj
                ((DerivedCategory.singleFunctor _ 0).obj G))))
  have hP : P (Mon.mk (integralCoefficientRing l E)) := by
    intro _ M hM G hG
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
      (hs.trans_lt (WithTop.coe_lt_top s)).ne
    have hts : t ≤ s := WithTop.coe_le_coe.mp (ht ▸ hs)
    have h := integral_dual_torsion_heart_sections l E S M hM t ht G hG.1
      ((isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mpr hG.2)
    intro i hi
    exact h i (by rcases hi with hi | hi <;> omega)
  rw [integral_bundle_eq l E] at hP
  exact hP L hL F hF

private theorem sections_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (hD : D = stratumModuleDual (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (hheart : ∀ F,
      IsClassicalAbelian F.X ∧ IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X →
      ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
          ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
            (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
              ((DerivedCategory.singleFunctor _ 0).obj F)))))
    (r : ℤ) (hr : b + (s : ℤ) + 1 < r) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
        (((derivedHom (IntegralQuotient.integral l E) S).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj (K⟦r⟧)))) := by
  have _hcd := hs
  let A := Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)
  have hd : IsDualizable ((DerivedCategory.singleFunctor A 0).obj L) := by
    let Q (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
      ∀ [IsCommMonObj R.X] (M : supportModules R.X S),
        HasFiniteConstantLocalModel R.X S M →
          IsDualizable ((DerivedCategory.singleFunctor _ 0).obj M)
    have hQ : Q (Mon.mk (DerivedNakayama.integerRing l E)) := by
      intro _ M hM
      obtain ⟨V, hV⟩ := integral_constantModel_localResolution l E S M hM
      apply (condensed_dualizable_iff_proetale_cover
        (⟨integralCoefficientRing l E⟩ : Profinite.CondensedRing.{u}) S V
        ((DerivedCategory.singleFunctor _ 0).obj M)).mpr
      intro j
      obtain ⟨C, hC, h₁, h₂, ⟨e⟩⟩ := hV j
      have h := DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hC h₁ h₂
      exact h.of_iso
        ((DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
          (((upperStar (integralCoefficientRing l E) (V.f j)).mapDerivedCategorySingleFunctor
            0).app M).symm)
    have hQ' : Q (sfbCondensedIntegers l E) :=
      @Eq.mp (Q (Mon.mk (DerivedNakayama.integerRing l E)))
        (Q (sfbCondensedIntegers l E))
        (congrArg Q (integral_bundle_eq l E)) (@hQ)
    exact hQ' L hL
  let G := stratumModuleDerivedSections (IntegralQuotient.integral l E) S
  let U := (derivedTensor (IntegralQuotient.integral l E) S).obj D
  let T := U ⋙ G
  let : G.CommShift ℤ := by
    dsimp only [G, stratumModuleDerivedSections]
    infer_instance
  let : G.IsTriangulated := by
    dsimp only [G, stratumModuleDerivedSections]
    infer_instance
  let : U.CommShift ℤ := by
    dsimp only [U, derivedTensor]
    infer_instance
  let : U.IsTriangulated := by
    dsimp only [U, derivedTensor]
    infer_instance
  let : T.CommShift ℤ := Functor.CommShift.comp U G
  let : T.IsTriangulated := by infer_instance
  let P : A → Prop := fun F ↦
    ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
        (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))
  have hb := DerivedCategory.bounded_heart_amplitude A Ab.{u + 1} T P
    (fun M N e h i hi ↦ (h i hi).of_iso
      ((DerivedCategory.homologyFunctor Ab.{u + 1} i).mapIso
        (T.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e.symm))))
    (fun i _ ↦ (DerivedCategory.homologyFunctor Ab.{u + 1} i).map_isZero
      (T.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero (isZero_zero A))))
    0 ((s : ℤ) + 1) (by omega)
    (fun _ h ↦ h)
    a b hab K hK (fun q i hi ↦ hheart _ (hclass q) i hi)
  have hz := hb r (Or.inr (by omega : b + ((s : ℤ) + 1) < r))
  have e₁ : (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
        ((shiftFunctor _ r).obj (T.obj K)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} r).obj (T.obj K) := by
    exact ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).shiftIso r 0 r (by omega)).app
      (T.obj K)
  have e₂ : (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
        (T.obj (K⟦r⟧)) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
        ((shiftFunctor _ r).obj (T.obj K)) := by
    simpa only [Functor.comp_obj] using
      (DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso ((T.commShiftIso r).app K)
  have hz' := (hz.of_iso e₁).of_iso e₂
  obtain ⟨hdual⟩ := hd
  let := hdual
  let := BraidedCategory.exactPairing_swap
    ((DerivedCategory.singleFunctor A 0).obj L)
    (((DerivedCategory.singleFunctor A 0).obj L)ᘁ)
  let := MonoidalClosed.isIso_ihomUnitTensorToIhom
    (((DerivedCategory.singleFunctor A 0).obj L)ᘁ)
    ((DerivedCategory.singleFunctor A 0).obj L) (K⟦r⟧)
  have ec := asIso (MonoidalClosed.ihomUnitTensorToIhom
    ((DerivedCategory.singleFunctor A 0).obj L) (K⟦r⟧))
  subst D
  exact hz'.of_iso ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso
    (G.mapIso ec.symm))

private theorem subsingleton_hom_of_internal_sections
    {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{u + 1} A]
    [MonoidalCategory (DerivedCategory A)]
    (R : A) (eunit : (DerivedCategory.singleFunctor A 0).obj R ≅
      𝟙_ (DerivedCategory A))
    (P K : DerivedCategory A) (H : DerivedCategory A ⥤ DerivedCategory A)
    (adj : tensorLeft P ⊣ H)
    (hz : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((preadditiveCoyoneda.obj (op R)).rightDerivedFunctor.obj (H.obj K)))) :
    Subsingleton (P ⟶ K) := by
  obtain ⟨e⟩ := derived_coyoneda_evaluation R 0
  have hz' := hz.of_iso (e.app (H.obj K))
  have hzero : Subsingleton (((DerivedCategory.singleFunctor A 0).obj R) ⟶
      (H.obj K) ⟦(0 : ℤ)⟧) := AddCommGrpCat.subsingleton_of_isZero hz'
  let E' := (Iso.homCongr (ρ_ P) (Iso.refl K)).symm |>.trans
    ((adj.homEquiv _ _).trans
      (Iso.homCongr eunit.symm ((shiftFunctorZero (DerivedCategory A) ℤ).symm.app
        (H.obj K))))
  exact E'.injective.subsingleton

/-- A finite local integral model has bounded Hom into any bounded complex with
classical locally ell-power torsion cohomology. This assertion does not involve
an ambient scheme, a closed support, a reduction functor, or a constructible target.

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
dual-tensor and bounded-heart steps; Stacks Tag 08JJ.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions-assembly).

Proof: transport the continuous integral coefficient to integralCoefficientRing.
Since cd_ell(S) <= s, choose its finite natural value s0 <= s. The finite local
model makes L[0] perfect, including its torsion summands, by the length-one DVR
resolutions. Put D=RHom(L[0],A[0]). The integral dual-torsion heart-sections theorem
places RΓ(D tensor F[0]) in [0,s0+1] for every classical local torsion module F;
use the equivalence of local torsion with the filtered prime-power-kernel union.
A K-flat representative of D makes tensoring triangulated, and derived sections
are triangulated. Bounded-heart devissage along the truncation triangles of K
therefore puts RΓ(D tensor K) in [a,b+s0+1]. The perfect-dual tensor adjunction
and the derived internal-Hom sections comparison identify Hom(L[0],K[r]) with
its r-th cohomology. This is zero when r>b+s+1, hence that Hom type is a
subsingleton. The zero module, zero complex and empty scheme satisfy the same
argument; no uniform prime-power annihilator is required. -/
theorem integralStratumFiniteCdReductions_assembly
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hclass : ∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
    (r : ℤ) (hr : b + (s : ℤ) + 1 < r) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj L ⟶ K⟦r⟧)  := by
  let D := ((derivedHom (IntegralQuotient.integral l E) S).obj (op
    ((DerivedCategory.singleFunctor _ 0).obj L))).obj
      (MonoidalCategory.tensorUnit
        (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (IntegralQuotient.integral l E) S))))
  have hheart := fun F hF ↦ integralStratumFiniteCdReductions_heart_bound
    l E S L hL D rfl s hs F hF
  have hz := integralStratumFiniteCdReductions_sections_bound l E S L hL D rfl s hs K a b hab
    hK hclass hheart r hr
  let R := Mod.regular (condensedRingObj (IntegralQuotient.integral l E) S)
  let P := (DerivedCategory.singleFunctor _ 0).obj L
  let H := (derivedHom (IntegralQuotient.integral l E) S).obj (op P)
  have hadj : tensorLeft P ⊣ H :=
    (derivedTensorHomAdjunction (IntegralQuotient.integral l E) P)
  have hzH : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((preadditiveCoyoneda.obj (op R)).rightDerivedFunctor.obj (H.obj (K⟦r⟧)))) := by
    simpa only [stratumModuleDerivedSections, R, H, P] using hz
  exact subsingleton_hom_of_internal_sections R
    (DerivedCategory.singleFunctorObjUnitIso _).symm P (K⟦r⟧) H hadj hzH

end CategoryTheory
