/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.CategoryTheory.Abelian.DerivedBottomComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.CondensedCurve.CondensedCurveCalculus
public import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
public import WeilConjectures.AlgebraicGeometry.FieldExtensionComponentLocalDimension
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed

/-! # Dense restriction and punctual kernels on a condensed curve

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/
thm-a1-curve-perverse-heart.proof.md, Steps 0(i)--(ii)
(blueprint: lem-per-condensed-curve-punctual-kernel).

The ordinary units, kernels, quotients and subobjects are in the actual coefficient
module category. Punctuality uses the existing constructible finite-closed-support
predicate, shared with the perverse-heart statement through its definitions module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePunctualKernel

local notation "ModΩ[" ell ", " T "]" =>
  CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) T
local notation "Punctual[" ell ", " T "]" =>
  CondensedCurvePerverse.IsPunctual (Profinite.padicAlgClRingObj ell) T
local notation "NoPunctual[" ell ", " T "]" =>
  CondensedCurvePerverse.HasNoPunctualSubsheaf (Profinite.padicAlgClRingObj ell) T

/-- The actual ordinary coefficient-module adjunction unit.
Source: curve-heart proof Step 0(ii), displayed F to j_*j^*F
(blueprint: lem-per-condensed-curve-punctual-kernel). -/
abbrev unitMap (ell : ℕ) [Fact ell.Prime] {C U : Scheme.{u}} (j : U ⟶ C)
    (F : ModΩ[ell, C]) :=
  (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ell) j).unit.app F

/-- The kernel inclusion defining the punctual subobject, in all module sheaves.
Source: curve-heart proof Step 0(ii), displayed definition of F_p
(blueprint: lem-per-condensed-curve-punctual-kernel). -/
abbrev kernelArrow (ell : ℕ) [Fact ell.Prime] {C U : Scheme.{u}} (j : U ⟶ C)
    (F : ModΩ[ell, C]) :=
  kernel.ι (unitMap ell j F)

/-- The quotient arrow F to F/F_p, formed as the cokernel of the kernel inclusion.
Source: curve-heart proof Step 0(ii), punctual-free quotient
(blueprint: lem-per-condensed-curve-punctual-kernel). -/
abbrev quotientArrow (ell : ℕ) [Fact ell.Prime] {C U : Scheme.{u}} (j : U ⟶ C)
    (F : ModΩ[ell, C]) :=
  cokernel.π (kernelArrow ell j F)

private theorem maximal_transport {A : Type u} [Category.{v} A]
    (E : A ≌ A) (P : A → Prop)
    (hP : ∀ G, P G → P (E.functor.obj G))
    (hQ : ∀ G, P G → P (E.inverse.obj G))
    {F K : A} (i : K ⟶ F) [Mono i] (hK : P K)
    (hmax : ∀ (G : A) (f : G ⟶ F), Mono f → P G →
      ∃ q : G ⟶ K, q ≫ i = f)
    (φ : E.functor.obj F ≅ F) :
    ∃! e : E.functor.obj K ≅ K, e.hom ≫ i = E.functor.map i ≫ φ.hom := by
  let T := MonoOver.congr F E |>.trans (MonoOver.mapIso φ)
  let k : MonoOver F := MonoOver.mk i
  have hmax' (L : MonoOver F) (hL : P L.obj.left) : Nonempty (L ⟶ k) := by
    obtain ⟨q, hq⟩ := hmax L.obj.left L.arrow inferInstance hL
    exact ⟨MonoOver.homMk q hq⟩
  obtain ⟨a⟩ := hmax' (T.functor.obj k) (hP K hK)
  obtain ⟨b₀⟩ := hmax' (T.inverse.obj k) (hQ K hK)
  let b : k ⟶ T.functor.obj k := (T.counitIso.app k).inv ≫ T.functor.map b₀
  let e₀ : T.functor.obj k ≅ k :=
    ⟨a, b, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  let e := (MonoOver.forget F ⋙ Over.forget F).mapIso e₀
  have he : e.hom ≫ i = E.functor.map i ≫ φ.hom := a.hom.w
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact (cancel_mono i).mp (he'.trans he.symm)

private theorem quotient_transport {A : Type u} [Category.{v} A]
    [HasZeroMorphisms A] [HasCokernels A] (E : A ≌ A) {K F : A} (i : K ⟶ F)
    (ep : E.functor.obj K ≅ K) (φ : E.functor.obj F ≅ F)
    (hep : ep.hom ≫ i = E.functor.map i ≫ φ.hom) :
    ∃! e : E.functor.obj (cokernel i) ≅ cokernel i,
      E.functor.map (cokernel.π i) ≫ e.hom = φ.hom ≫ cokernel.π i := by
  let e := PreservesCokernel.iso E.functor i ≪≫
    cokernel.mapIso (E.functor.map i) i ep φ hep.symm
  have he : E.functor.map (cokernel.π i) ≫ e.hom = φ.hom ≫ cokernel.π i := by
    simp [e, cokernel.mapIso, cokernel.map]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact (cancel_epi (E.functor.map (cokernel.π i))).mp (he'.trans he.symm)

private def pull_equivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {C : Scheme.{u}} (g : C ≅ C) :
    CondensedCurvePerverse.Modules Λ C ≌ CondensedCurvePerverse.Modules Λ C :=
  CategoryTheory.Equivalence.mk
    (CondensedRing.upperStar Λ g.hom) (CondensedRing.upperStar Λ g.inv)
    ((CondensedRing.upperStarId Λ C).symm ≪≫
      CondensedRing.upperStarCongr Λ g.inv_hom_id.symm ≪≫
      CondensedRing.upperStarComp Λ g.inv g.hom)
    ((CondensedRing.upperStarComp Λ g.hom g.inv).symm ≪≫
      CondensedRing.upperStarCongr Λ g.hom_inv_id ≪≫ CondensedRing.upperStarId Λ C)

private theorem punctual_pull_of_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {C : Scheme.{u}} (f : C ⟶ C) [IsIso f]
    (G : CondensedCurvePerverse.Modules Λ C) (hG : CondensedCurvePerverse.IsPunctual Λ C G)
    (hc : IsConstantModelConstructible Λ C ((CondensedRing.upperStar Λ f).obj G)) :
    CondensedCurvePerverse.IsPunctual Λ C ((CondensedRing.upperStar Λ f).obj G) := by
  obtain ⟨_, U, hf, hclosed, hz⟩ := hG
  let W := f ⁻¹ᵁ U
  refine ⟨hc, W, ?_, ?_, ?_⟩
  · exact hf.preimage f.homeomorph.injective.injOn
  · intro x hx
    have he : f ⁻¹' ({f x} : Set C) = ({x} : Set C) := by
      ext y
      exact f.homeomorph.injective.eq_iff
    rw [← he]
    exact (hclosed (f x) hx).preimage f.continuous
  · exact CondensedRing.isZero_upperStar_restrict Λ f U W rfl G hz

private theorem punctual_pull_with_statement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C] (f : C ⟶ C) [IsIso f]
    (G : CondensedCurvePerverse.Modules Λ C) (hG : CondensedCurvePerverse.IsPunctual Λ C G) :
    CondensedCurvePerverse.IsPunctual Λ C ((CondensedRing.upperStar Λ f).obj G) := by
  exact punctual_pull_of_constructible Λ f G hG (hc f G hG.1).1

private theorem punctual_weil_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {C : Scheme.{u}} (g : C ≅ C)
    (hP : ∀ G, CondensedCurvePerverse.IsPunctual Λ C G →
      CondensedCurvePerverse.IsPunctual Λ C ((CondensedRing.upperStar Λ g.hom).obj G))
    (hQ : ∀ G, CondensedCurvePerverse.IsPunctual Λ C G →
      CondensedCurvePerverse.IsPunctual Λ C ((CondensedRing.upperStar Λ g.inv).obj G))
    {F K : CondensedCurvePerverse.Modules Λ C} (i : K ⟶ F) [Mono i]
    (hK : CondensedCurvePerverse.IsPunctual Λ C K)
    (hmax : ∀ (G : CondensedCurvePerverse.Modules Λ C) (f : G ⟶ F),
      Mono f → CondensedCurvePerverse.IsPunctual Λ C G → ∃ q : G ⟶ K, q ≫ i = f)
    (φ : (CondensedRing.upperStar Λ g.hom).obj F ≅ F) :
    (∃! e : (CondensedRing.upperStar Λ g.hom).obj K ≅ K,
      e.hom ≫ i = (CondensedRing.upperStar Λ g.hom).map i ≫ φ.hom) ∧
    (∃! e : (CondensedRing.upperStar Λ g.hom).obj (cokernel i) ≅ cokernel i,
      (CondensedRing.upperStar Λ g.hom).map (cokernel.π i) ≫ e.hom =
        φ.hom ≫ cokernel.π i) := by
  let E := pull_equivalence Λ g
  have hp := maximal_transport E (CondensedCurvePerverse.IsPunctual Λ C) hP hQ i hK hmax φ
  refine ⟨hp, ?_⟩
  obtain ⟨ep, hep, _⟩ := hp
  exact quotient_transport E i ep φ hep

private theorem geometric_pure (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (hPure : C₀.left.IsPureDimension 1) :
    (D.geometricFiber C₀).left.IsPureDimension 1 := by
  let e : ↥(⊤ : C₀.left.Opens) ≃ₜ C₀.left := Homeomorph.Set.univ _
  have ht : ∀ Z ∈ irreducibleComponents ↥(⊤ : C₀.left.Opens),
      topologicalKrullDim Z = (1 : WithBot ℕ∞) := by
    intro Z hZ
    have hZ' : e.symm ⁻¹' Z ∈ irreducibleComponents C₀.left := by
      apply preimage_mem_irreducibleComponents hZ e.symm.isOpenEmbedding
      simpa only [e.symm.surjective.range_eq, Set.inter_univ] using hZ.1.nonempty
    let eZ : Z ≃ₜ e.symm ⁻¹' Z := e.subtype (by simp)
    exact (IsHomeomorph.topologicalKrullDim_eq eZ eZ.isHomeomorph).trans (hPure _ hZ')
  exact (field_extension_component_local_dimension (L := D.k) C₀.hom).2.2.2 1
    (fun x ↦ topologicalKrullDimAt_eq_of_equidimensional_open C₀.hom ⊤ 1 ht x (by trivial))

end AlgebraicGeometry.ProEtale.CondensedCurvePunctualKernel
