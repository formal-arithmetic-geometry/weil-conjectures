/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.CohomologicalDimension
import Sheaf.Paper.IntegralReductionSupportAmplitude
import Sheaf.Paper.IntegralDualTorsionHeartSections
import Sheaf.CategoryTheory.BoundedHeartAmplitude
import Sheaf.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.CharP.CharAndCard

/-! # Finite reduction estimate for Hom from an integral stratum extension -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem amplitude_from_heart_images
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) (K : DerivedCategory A)
    (hK : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor A q).obj K))
    (hheart : ∀ q i : ℤ, i < c ∨ d < i →
      IsZero ((DerivedCategory.homologyFunctor B i).obj
        (T.obj ((DerivedCategory.singleFunctor A 0).obj
          ((DerivedCategory.homologyFunctor A q).obj K))))) :
    ∀ i : ℤ, i < a + c ∨ b + d < i →
      IsZero ((DerivedCategory.homologyFunctor B i).obj (T.obj K)) := by
  let P : A → Prop := fun F ↦ ∀ i : ℤ, i < c ∨ d < i →
    IsZero ((DerivedCategory.homologyFunctor B i).obj
      (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))
  apply DerivedCategory.bounded_heart_amplitude A B T P
    (fun M N e h i hi ↦ (h i hi).of_iso
      ((DerivedCategory.homologyFunctor B i).mapIso
        (T.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e))).symm)
    (fun i _ ↦ (DerivedCategory.homologyFunctor B i).map_isZero
      (T.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero (isZero_zero A))))
    c d hcd (fun _ h ↦ h) a b hab K hK hheart

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
  have : Subsingleton (((DerivedCategory.singleFunctor A 0).obj R) ⟶
      (H.obj K) ⟦(0 : ℤ)⟧) := AddCommGrpCat.subsingleton_of_isZero hz'
  let E := (Iso.homCongr (ρ_ P) (Iso.refl K)).symm |>.trans
    ((adj.homEquiv _ _).trans
      (Iso.homCongr eunit.symm ((shiftFunctorZero (DerivedCategory A) ℤ).symm.app (H.obj K))))
  exact E.injective.subsingleton

/-- Before taking the derived inverse limit, positive reductions satisfy the cutoff
`cd(j) + cd(S) + 2`, uniformly in the exponent and the constructible target sheaf.

Source: blueprint sk-lem-int-ext.proof.md, paragraph (2), its three bullets;
expanded steps 3--10 of det-lem-int-ext-bound; Stacks Tags 08JJ and 08J5.
(blueprint: lem-sf-integral-stratum-reduction-ext-bound).

Proof: the free quotient resolution represents each reduction of N by [N → N] in
[-1,0], even for torsion N. It is bounded constructible and classical by the
complete-reduction criterion and the constructible comparison theorem. The closed
support fibre of K → Rj_*j^*K has upper bound c+1: the relative cohomological
dimension bounds Rj_* on classical torsion sheaves, and finite truncation triangles
extend that bound to K. Exact inverse image to S preserves this bound and classicality.
The derived dual of L has Tor amplitude [0,1]; after reduction its local two-term
finite free models are classical. Tensoring the support fibre with that dual has
upper bound c+2, by its finite cohomology filtration and exactness of derived tensor.
Derived sections add at most s by absolute cohomological dimension and the classical
comparison, again applied to the finite filtration. The stratum derived Hom formula
identifies this cohomology with the asserted morphism group. Restriction of scalars
commutes with the support adjunction, its unit, inverse image, and sections; the
scalar-extension/restriction adjunction therefore identifies the finite-coefficient
calculation with the recorded integral derived reductions. No functor is commuted
with an inverse limit in this estimate. The same bounds hold for zero or empty strata. -/
theorem integral_stratum_reduction_ext_bound
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (S Z V : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
    [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hL : IsConstantModelConstructible (integralCoefficientRing l E) S L)
    (hmodel : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L)
    (c s : ℕ)
    (hc : (c : WithTop ℕ) = relativeCohomologicalDimension l (Fact.out : l.Prime) j)
    (hs : (s : WithTop ℕ) = cohomologicalDimension l (Fact.out : l.Prime) S)
    (N : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (hN : IsConstantModelConstructible (integralCoefficientRing l E) X N)
    (n : ℕ) (r : ℤ) (hr : (c : ℤ) + s + 2 < r) :
    Subsingleton (((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar (integralCoefficientRing l E) i).obj
          ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))) ⟶
      ((integralReductionFunctor l E X (n + 1)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N)) ⟦r⟧) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (v ≫ i)
  have : IsNoetherian S := ⟨⟩
  have hchar0 : ringChar D.k₀ = D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have hc₀ : Fintype.card D.k₀ = D.q := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc₀.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  have hchar : ringChar D.k = D.p :=
    (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0
  have : Fact (ringChar D.k).Prime := ⟨hchar ▸ D.prime⟩
  have : Fact (ringChar D.k ≠ l) := ⟨by rw [hchar]; exact hl.symm⟩
  obtain ⟨hAdd, ⟨e⟩, _⟩ := integral_stratum_hom_formula l E D.k i v j hij L hL hmodel
  let := hAdd
  let K := (integralReductionFunctor l E X (n + 1)).obj
    ((DerivedCategory.singleFunctor _ 0).obj N)
  let M := (upperStar (integralCoefficientRing l E) v).mapDerivedCategory.obj
    ((closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).rightDerivedFunctor.obj K)
  let : (integralStratumDualTensor l E S L).CommShift ℤ := by
    unfold integralStratumDualTensor stratumModuleDualTensor derivedTensor
    infer_instance
  let : (integralStratumDualTensor l E S L).IsTriangulated := by
    unfold integralStratumDualTensor stratumModuleDualTensor derivedTensor
    infer_instance
  let : (integralStratumDerivedSections l E S).CommShift ℤ := by
    unfold integralStratumDerivedSections
    infer_instance
  let : (integralStratumDerivedSections l E S).IsTriangulated := by
    unfold integralStratumDerivedSections
    infer_instance
  let T := integralStratumDualTensor l E S L ⋙ integralStratumDerivedSections l E S
  obtain ⟨hM, hclass⟩ :=
    integral_reduction_support_amplitude D l hl E X S Z V v i j hij hAdd c hc N hN n
  have hzero : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} r).obj (T.obj M)) :=
    amplitude_from_heart_images T (-1) ((c : ℤ) + 1) 0 ((s : ℤ) + 1)
      (by omega) (by omega) M hM
      (fun q ↦ integral_dual_torsion_heart_sections l E S L hmodel s hs
        ((DerivedCategory.homologyFunctor _ q).obj M) (hclass q).1 (hclass q).2)
      r (Or.inr (by omega))
  let F := (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).rightDerivedFunctor ⋙
    (upperStar (integralCoefficientRing l E) v).mapDerivedCategory ⋙ T
  have hshift : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      (F.obj (K⟦r⟧))) := hzero.of_iso
    ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso ((F.commShiftIso r).app K) ≪≫
      ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).isoShift r).app (F.obj K))
  have hhom : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((integralStratumDerivedSections l E X).obj
        (((derivedHom (integralCoefficientRing l E) X).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj
            ((lowerStar (integralCoefficientRing l E) i).obj
              ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))))).obj
          (K⟦r⟧)))) := hshift.of_iso
    ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).mapIso (e.app (K⟦r⟧)))
  exact subsingleton_hom_of_internal_sections
    (Mod.regular (condensedRingObj (integralCoefficientRing l E) X))
    (DerivedCategory.singleFunctorObjUnitIso _) _ (K⟦r⟧) _
    (derivedTensorHomAdjunction (integralCoefficientRing l E) _) hhom

end AlgebraicGeometry.ProEtale.CondensedRing
