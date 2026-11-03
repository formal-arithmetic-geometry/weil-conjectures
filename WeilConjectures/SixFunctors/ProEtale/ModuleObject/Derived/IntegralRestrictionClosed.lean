/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Integral exceptional inverse image along a closed immersion

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/
sk-thm-restriction/sk-thm-int-restriction-closed.md and its proof
(blueprint: det-thm-int-restriction-closed).

The support functor is the right derived functor of the existing kernel construction.
The formal closed-support theorem identifies it with the closed pullback of the fibre
of the canonical open restriction unit. The exceptional inverse image is any right
adjoint of the existing compactification lower shriek on localizing closures.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 800000 in
-- The proof transports coefficient data and compares functors on full derived subcategories.
private theorem integralRestrictionClosedCore
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hcd : BaseFieldFiniteCD ℓ k)
    (_hΛ : ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.padicIntegersRingObj ℓ E))
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (_hij : Set.range j = (Set.range i)ᶜ)
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K : DerivedCategory (supportModules R.X Z),
      localizingClosureProEtale R.X Z K → localizingClosureProEtale R.X X
        ((rightDerivedLowerShriekOfCompactification R.X c.obj.obj).obj K))
    (G : (localizingClosureProEtale R.X X).FullSubcategory ⥤
      (localizingClosureProEtale R.X Z).FullSubcategory)
    (_adj : localizingLowerShriek R.X c.obj.obj h ⊣ G) :
    (∀ K : DerivedCategory (supportModules R.X X),
      constantModelBoundedConstructible R.X X K →
        constantModelBoundedConstructible R.X Z
          ((closedSupport R.X i j).rightDerivedFunctor.obj K)) ∧
    ∃ hbc : constantModelBoundedConstructible R.X X ≤ localizingClosureProEtale R.X X,
      Nonempty
        (ObjectProperty.ιOfLE hbc ⋙ G ⋙ (localizingClosureProEtale R.X Z).ι ≅
          (constantModelBoundedConstructible R.X X).ι ⋙
            (closedSupport R.X i j).rightDerivedFunctor) := by
  classical
  obtain ⟨E, hE⟩ := _hΛ
  cases hE
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : IsNoetherian Z := ⟨⟩
  have : QuasiCompact j := inferInstance
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have : IsNoetherian U := ⟨⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) := by
    rw [← CategoryTheory.comp_over j (Spec (.of k))]
    infer_instance
  have : QuasiCompact (U ↘ Spec (.of k)) := by
    rw [← CategoryTheory.comp_over j (Spec (.of k))]
    infer_instance
  have : IsSeparated (U ↘ Spec (.of k)) := by
    rw [← CategoryTheory.comp_over j (Spec (.of k))]
    infer_instance
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ Z).2.1
  have htri : (constantModelBoundedConstructible Λ X).IsTriangulated := by
    rw [← (adicConstructibilityPredicateComparison ℓ X Λ (.integral E.val)).2]
    exact isTriangulated_boundedConstructible_ellAdic_padicIntegers X ℓ E.val
  let := htri
  have hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E'.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E'.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
    Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩))
  have hbc (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      constantModelBoundedConstructible Λ T ≤ localizingClosureProEtale Λ T := by
    have heq := (localizingClosure_ctf_equals_bc ℓ T Λ hcoeff).1.2.2.1
    intro K hK P _ hP
    apply hP K
    change (constantModelBoundedConstructible Λ T ⊓
      DerivedCategory.finiteTorAmplitude _) K
    rwa [heq]
  obtain ⟨F, ι, δ, hδ, ⟨eF⟩, _⟩ :=
    formalClosedSupportFiberAssertions Λ ℓ k hadm i j _hij
  have hc : ∀ K, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Z
        ((closedSupport Λ i j).rightDerivedFunctor.obj K) := by
    intro K hK
    have hJ := (integralModelsOperations ℓ E).1 j K hK
    have heq := (localizingClosure_ctf_equals_bc ℓ U Λ hcoeff).1.2.2.1
    have hJT : (constantModelBoundedConstructible Λ U ⊓
        DerivedCategory.finiteTorAmplitude _) ((upperStar Λ j).mapDerivedCategory.obj K) := by
      rw [heq]
      exact hJ
    have hopen := (integralOpenDirectImage ℓ E k j ⟨_, hJT⟩).1
    have hF : constantModelBoundedConstructible Λ X (F.obj K) :=
      (constantModelBoundedConstructible Λ X).ext_of_isTriangulatedClosed₁ _ (hδ K) hK hopen
    exact (constantModelBoundedConstructible Λ Z).prop_of_iso (eF.app K)
      ((integralModelsOperations ℓ E).1 i _ hF)
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    simp only [_hij, compl_compl]
  let := closedSupport_lowerStarExact Λ i j hij
  have heZ : localizingClosureProEtale Λ Z = IntegralCompactSupport.localizing Λ Z :=
    (localizingClosure_ctf_equals_bc ℓ Z Λ hcoeff).1.2.2.2.1
  obtain ⟨_, φ, _, _⟩ := IntegralCompactSupport.integralLocalizingCompactSupport ℓ E k
  let Z' : IntegralCompactSupport.Spaces k :=
    ⟨Over.mk (Z ↘ Spec (.of k)), by
      change IsSeparated (Z ↘ Spec (.of k)) ∧
        LocallyOfFiniteType (Z ↘ Spec (.of k)) ∧ QuasiCompact (Z ↘ Spec (.of k))
      exact ⟨inferInstance, inferInstance, inferInstance⟩⟩
  let X' : IntegralCompactSupport.Spaces k :=
    ⟨Over.mk (X ↘ Spec (.of k)), by
      change IsSeparated (X ↘ Spec (.of k)) ∧
        LocallyOfFiniteType (X ↘ Spec (.of k)) ∧ QuasiCompact (X ↘ Spec (.of k))
      exact ⟨inferInstance, inferInstance, inferInstance⟩⟩
  let f : Z' ⟶ X' := ObjectProperty.homMk (Over.homMk i (CategoryTheory.comp_over i _))
  let d : IntegralCompactSupport.Compactifications k f :=
    ⟨Compactification.ofIsProper i, by change QuasiCompact (𝟙 Z); infer_instance⟩
  let J := ObjectProperty.ιOfLE (le_of_eq heZ)
  have e : localizingLowerShriek Λ c.obj.obj h ⋙ (localizingClosureProEtale Λ X).ι ≅
      (localizingClosureProEtale Λ Z).ι ⋙ (lowerStar Λ i).mapDerivedCategory := by
    exact Functor.isoWhiskerLeft J (φ f c.obj d) ≪≫
      Functor.isoWhiskerLeft (localizingClosureProEtale Λ Z).ι
        (Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ Z) _ ≪≫
          Functor.leftUnitor _ ≪≫
          Functor.rightDerivedFunctorIsoMapDerivedCategory (lowerStar Λ i))
  exact ⟨hc, hbc X, ⟨comparison (localizingClosureProEtale Λ X)
    (localizingClosureProEtale Λ Z) (constantModelBoundedConstructible Λ X)
    (lowerStar Λ i).mapDerivedCategory (closedSupport Λ i j).rightDerivedFunctor
    (closedSupportDerivedAdjunction Λ i j hij) _ G _adj e (hbc X)
    (fun K hK ↦ hbc Z _ (hc K hK))⟩⟩

/-- Closed support preserves integral bounded constructibility and agrees naturally
with the Brown exceptional inverse image on those complexes.

Source: blueprint latest, det-thm-int-restriction-closed, complete statement and proof
(blueprint: det-thm-int-restriction-closed).

The coefficient condition selects exactly the condensed valuation rings of finite
extensions of Q_l. The arguments c, h, G and adj present the chosen Brown adjunction
of sk-prop-sf-existence, rather than assuming its desired support comparison. The
existential hbc only lifts the bounded constructible inclusion into its localizing
closure; the comparison is a natural isomorphism of functors on the full bounded
constructible category, so includes every morphism in K.

Proof:
1. Let j be the open complement. Finite type over k makes X Noetherian, hence j
   quasi-compact. The formal closed-support theorem gives the distinguished triangle
   i_* R Gamma_Z K -> K -> Rj_* j^* K -> i_* R Gamma_Z K[1], and identifies R Gamma_Z
   with the right derived functor of closedSupport.
2. Pullback preserves integral bounded constructibility and the open-direct-image
   theorem puts Rj_* j^* K in Dbc(X,O_E). Triangulated closure puts the first term
   there. Pull back along i and use i^* i_* = id to obtain R Gamma_Z K in Dbc(Z,O_E).
3. For these integral coefficients Loc(Dctf) = Loc(Dbc), so every bounded
   constructible K has the membership proof hbc. The identity compactification of
   the proper closed immersion identifies Ri_! with the exact closed direct image.
   For A in Loc(Dbc(Z)), Brown adjunction and formal-support adjunction identify
   Hom(A,i^! K) and Hom(A,R Gamma_Z K) with the same Hom(i_* A,K). The localizing
   closures are full. Yoneda gives the isomorphism, and naturality of both
   adjunctions gives naturality in K, including zero objects and empty schemes.
-/
theorem integralRestrictionClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (_hcd : BaseFieldFiniteCD ℓ k)
    (_hΛ : ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Mon.mk Λ = Mon.mk (Profinite.padicIntegersRingObj ℓ E))
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (_hij : Set.range j = (Set.range i)ᶜ)
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K : DerivedCategory (supportModules Λ Z),
      localizingClosureProEtale Λ Z K → localizingClosureProEtale Λ X
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Z).FullSubcategory)
    (_adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    (∀ K : DerivedCategory (supportModules Λ X),
      constantModelBoundedConstructible Λ X K →
        constantModelBoundedConstructible Λ Z
          ((closedSupport Λ i j).rightDerivedFunctor.obj K)) ∧
    ∃ hbc : constantModelBoundedConstructible Λ X ≤ localizingClosureProEtale Λ X,
      Nonempty
        (ObjectProperty.ιOfLE hbc ⋙ G ⋙ (localizingClosureProEtale Λ Z).ι ≅
          (constantModelBoundedConstructible Λ X).ι ⋙
            (closedSupport Λ i j).rightDerivedFunctor) := by
  exact integralRestrictionClosedCore (Mon.mk Λ) ℓ k _hcd _hΛ i j _hij c h G _adj

end AlgebraicGeometry.ProEtale.CondensedRing
