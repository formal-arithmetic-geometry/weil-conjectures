/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarPerfectCoefficientIso
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StratifiedScalarPerfectGeneration
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralScalarPerfectStratification
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteScalarPerfectStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RationalLocallyClosedPerfectGeneration
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated

/-! # Finite generation by scalar-perfect pieces

Source: current blueprint, internal-Hom stability proof, Steps 3--5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private def PerfectGenerated (Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Ω] [IsCommMonObj Ω] (X : Scheme.{u})
    (K : DerivedCategory (supportModules Ω X)) : Prop :=
  ∀ Q : ObjectProperty (DerivedCategory (supportModules Ω X)),
    Q.IsTriangulated → Q.IsClosedUnderIsomorphisms →
    (∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i] (P : DerivedCategory (supportModules Ω S)),
      IsLocallyConstantPerfectComplex Ω S P →
      Q (((openImmersionLowerShriek Ω j).mapDerivedCategory ⋙
        (lowerStar Ω i).rightDerivedFunctor).obj P)) → Q K

set_option maxHeartbeats 1600000 in
-- Deriving the three coefficient-restriction comparisons has large instance terms.
private theorem generation_coefficientIso
    {Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Ω] [IsCommMonObj Ω] (e : Mon.mk Λ ≅ Mon.mk Ω)
    (X : Scheme.{u}) [IsNoetherian X]
    (hgen : ∀ K : DerivedCategory (supportModules Ω X),
      (constantModelBoundedConstructible Ω X K ∧ _root_.DerivedCategory.finiteTorAmplitude _ K) →
        PerfectGenerated Ω X K)
    (K : DerivedCategory (supportModules Λ X))
    (hK : constantModelBoundedConstructible Λ X K ∧ _root_.DerivedCategory.finiteTorAmplitude _ K) :
    PerfectGenerated Λ X K := by
  intro Q htri hiso hQ
  let := htri
  let := hiso
  let F (T : Scheme.{u}) := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.hom.hom T)
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv.hom X)
  let L := G.mapDerivedCategory.obj K
  have hL : constantModelBoundedConstructible Ω X L ∧
      _root_.DerivedCategory.finiteTorAmplitude _ L := constantModelCtf_coefficientIso e X ⟨K, hK⟩
  let Q' := Q.inverseImage (F X).mapDerivedCategory
  have hL' : Q' L := hgen L hL Q' inferInstance inferInstance (by
    intro S Z j i _ _ P hP
    have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
    have : PreservesFiniteColimits (lowerStar Λ i) := closed_exact Λ i
    have : PreservesFiniteColimits (lowerStar Ω i) := closed_exact Ω i
    let A := openImmersionLowerShriek Ω j ⋙ lowerStar Ω i
    let B := openImmersionLowerShriek Λ j ⋙ lowerStar Λ i
    have : A.Additive := inferInstanceAs
      (openImmersionLowerShriek Ω j ⋙ lowerStar Ω i).Additive
    have : B.Additive := inferInstanceAs
      (openImmersionLowerShriek Λ j ⋙ lowerStar Λ i).Additive
    have : PreservesFiniteLimits A := by dsimp [A]; infer_instance
    have : PreservesFiniteColimits A := by dsimp [A]; infer_instance
    have : PreservesFiniteLimits B := by dsimp [B]; infer_instance
    have : PreservesFiniteColimits B := by dsimp [B]; infer_instance
    have hP' := scalarPerfect_comap e.hom.hom S P hP
    have hp := hQ S Z j i ((F S).mapDerivedCategory.obj P) hP'
    let a : A ⋙ F X ≅ F S ⋙ B :=
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (comapLowerStarIso e.hom.hom i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (comapOpenImmersionLowerShriekIso e.hom.hom j) _ ≪≫
      Functor.associator _ _ _
    let da : (F X).mapDerivedCategory.obj (A.mapDerivedCategory.obj P) ≅
        B.mapDerivedCategory.obj ((F S).mapDerivedCategory.obj P) :=
      (Functor.mapDerivedCategoryCompIso _ _).symm.app P ≪≫
      (Functor.mapDerivedCategoryNatIso a).app P ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).app P
    let eb := (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ j) (lowerStar Λ i)).app
      ((F S).mapDerivedCategory.obj P) ≪≫
      ((lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app _).symm
    let ea := (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Ω j) (lowerStar Ω i)).app P ≪≫
      ((lowerStar Ω i).rightDerivedFunctorIsoMapDerivedCategory.app _).symm
    exact Q.prop_of_iso ((F X).mapDerivedCategory.mapIso ea)
      (Q.prop_of_iso da.symm (Q.prop_of_iso eb.symm hp)))
  apply Q.prop_of_iso _ hL'
  exact (Functor.mapDerivedCategoryCompIso _ _).symm.app K ≪≫
    (Functor.mapDerivedCategoryNatIso ((Mod.comapComp _ _).symm ≪≫
      Mod.comapCongr (by
        dsimp [coefficientMap]
        rw [← Functor.map_comp]
        have he : e.hom.hom ≫ e.inv.hom = 𝟙 Λ :=
          congrArg (fun f ↦ f.hom) e.hom_inv_id
        rw [he]
        exact (upperStarFromPoint X).map_id Λ) ≪≫ Mod.comapId _)).app K ≪≫
    (Functor.mapDerivedCategoryIdIso _).app K

set_option maxHeartbeats 1600000 in
-- The six coefficient cases carry distinct internal-module presentations.
/-- Finite triangulated generation by locally closed scalar-perfect pieces.
Source: internal-Hom stability proof, Steps 3--5
(blueprint: lem-sfb-ctf-locally-closed-perfect-generation).

Proof: Make the finite locally closed stratification adapted to the finitely many terms
or cohomology sheaves an ordered refinement with open prefixes V_r. Extension by zero
of the open--closed short exact sequences gives distinguished triangles with vertices
C_(r-1), C_r and the extension of the restriction to stratum r. Start at zero and
induct over the finite number of strata. Coherence identifies these extensions with
open extension followed by closed direct image for the chosen factorization.
For finite coefficients descend to the etale site and use a bounded flat constructible
model. Its termwise local scalar models are finite flat modules over a Noetherian ring,
hence finitely presented projective. Pull back exactly to the pro-etale site. Apply
the preceding stratification induction to each term and then use the stupid truncation
triangles of the bounded model. For integral coefficients the local-model theorem gives
bounded completed finite free complexes on the strata, so apply the stratification
induction directly to the complex. For rational coefficients use the lisse finite free
quotients of the constructible-heart filtration, and then the finitely many cohomological
truncation triangles. Transport through coefficient isomorphisms. Every induction uses
only finitely many cones and shifts, never retracts. On an empty scheme the empty
filtration starts and ends at zero, which belongs to any triangulated Q. -/
theorem ctf_locallyClosedPerfect_generation
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (K : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hK : constantModelBoundedConstructible Λ X K ∧ _root_.DerivedCategory.finiteTorAmplitude _ K)
    (Q : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i] (P : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))),
      IsLocallyConstantPerfectComplex Λ S P →
      Q (((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (lowerStar Λ i).rightDerivedFunctor).obj P)) : Q K := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have hfield (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) : Q K := by
    apply generation_coefficientIso Λ e X _ K hK Q inferInstance inferInstance hQ
    intro L hL Q' ht hi hQ'
    let := ht
    let := hi
    exact rational_locallyClosedPerfect_generation ℓ
      (Profinite.padicSubfieldCondensedRing ℓ E.1) (Or.inl ⟨E.1, E.2, rfl⟩)
      X L hL.1 Q' hQ'
  have hintegral (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (e : Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) : Q K := by
    let : FiniteDimensional ℚ_[ℓ] E.1 := E.2
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
    let er := integerRingSheafIso.{u} ℓ ⟨E.1, E.2⟩
    let ea := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
    have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
    apply generation_coefficientIso Λ (e ≪≫ Mon.mkIso' ea) X _ K hK Q
      inferInstance inferInstance hQ
    intro L hL Q' ht hi hQ'
    let := ht
    let := hi
    exact scalarPerfectStratification_generation _ X L
      (integral_scalarPerfectStratification ℓ (ULift.{u} E.1) X L hL.1) Q' hQ'
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
    let : Finite A := hfin
    obtain ⟨j⟩ := AdmissibleTriangulated.finiteCoefficientLiftIso.{u} A
    apply generation_coefficientIso Λ (e ≪≫ j) X _ K hK Q inferInstance inferInstance hQ
    intro L hL Q' ht hi hQ'
    let := ht
    let := hi
    exact scalarPerfectStratification_generation _ X L
      (FiniteDiscreteOrdinary.finite_scalarPerfectStratification (ULift.{u} A)
        (ringChar k) ℓ (Fact.out : ringChar k ≠ ℓ) k X (X ↘ Spec (.of k)) L hL) Q' hQ'
  · obtain ⟨e⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, zIso, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact hintegral ⟨⊥, inferInstance⟩ (e ≪≫ zIso)
  · obtain ⟨e⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, qIso, _, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact hfield ⟨⊥, inferInstance⟩ (e ≪≫ qIso)
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact hfield E e
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact hintegral E e
  · obtain ⟨e⟩ := h
    apply generation_coefficientIso Λ e X _ K hK Q inferInstance inferInstance hQ
    intro L hL Q' ht hi hQ'
    let := ht
    let := hi
    exact rational_locallyClosedPerfect_generation ℓ (Profinite.padicAlgClCondensedRing ℓ)
      (Or.inr rfl) X L hL.1 Q' hQ'


end AlgebraicGeometry.ProEtale.CondensedRing
