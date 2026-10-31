/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.PointScalarSectionsExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.FiniteGeometricPointCohomology
import WeilConjectures.AlgebraicGeometry.FinitePointSectionsExact
import WeilConjectures.SixFunctors.NativeTerminalSectionsComparison
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import all WeilConjectures.CategoryTheory.DerivedCategory.RingIsoPerfectScalarEquivalence
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientExtComparison
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedPointDiscreteConstantComparison
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Perfect native terminal sections at an algebraically closed geometric point
Source: the first paragraph of sk-lem-finite
(blueprint: lem-sf-native-point-sections-perfect).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem perfect_iso {R : Type (u + 1)} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u + 1} R)}
    (e : K ≅ L) (h : DerivedCategory.IsPerfectRingComplex K) :
    DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ i⟩⟩

private theorem point_perfect_of_coarse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [IsAlgClosed k]
    (h : ∀ K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)),
      DerivedCategory.IsPerfectRingComplex
        ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj K.obj))
    (K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k))) :
    DerivedCategory.IsPerfectRingComplex
      ((CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory.obj K.obj) := by
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  let e := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
  let G := ModuleCat.restrictScalars e.symm.toRingHom
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  obtain ⟨q⟩ := native_terminalSectionsIso
    (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))
    ((condensedRingScalarSections Λ (Spec (.of k))).comp e.symm.toRingHom)
    (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale (Spec (.of k)))
  change F ⋙ G ≅ CohomologyTransport.sections Λ (Spec (.of k)) at q
  let r := (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso q
  have hp := CategoryTheory.RingDerivedScalarExtension.perfect_restrict
    (CommRingCat.of (condensedScalarRing Λ)) (CommRingCat.of (Γ Λ)) e.symm
    (F.rightDerivedFunctor.obj K.obj) (h K)
  exact perfect_iso ((G.mapDerivedCategory.mapIso
    (F.rightDerivedFunctorIsoMapDerivedCategory.app K.obj)) ≪≫ r.app K.obj) hp

private theorem point_coarse_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (k : Type u) [Field k] [IsAlgClosed k]
    (h : ∀ K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)),
      DerivedCategory.IsPerfectRingComplex
        ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj K.obj))
    (K : ConstantModelConstructibleFiniteTor Λ' (Spec (.of k))) :
    DerivedCategory.IsPerfectRingComplex
      ((condensedRingCoefficientSections Λ' (Spec (.of k))).rightDerivedFunctor.obj K.obj) := by
  let X := Spec (.of k)
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  let φ := coefficientMap e.hom.hom X
  have : IsIso φ := by change IsIso ((upperStarFromPoint X).map e.hom.hom); infer_instance
  let H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X) := Mod.comap φ
  have : H.IsEquivalence := (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  let p : H.obj (Mod.regular (condensedRingObj Λ' X)) ≅
      Mod.regular (condensedRingObj Λ X) := (Mod.comapUnitIso φ).symm
  let σ := Γ.map e.inv.hom
  have hσ : Function.Bijective σ := by
    have h₁ : Function.LeftInverse (Γ.map e.hom.hom) σ := by
      intro x
      apply Γ.ext
      change (x.hom ≫ e.inv.hom) ≫ e.hom.hom = x.hom
      rw [Category.assoc]
      change x.hom ≫ ((Mon.forget _).map (e.inv ≫ e.hom)) = x.hom
      simp
    have h₂ : Function.RightInverse (Γ.map e.hom.hom) σ := by
      intro x
      apply Γ.ext
      change (x.hom ≫ e.hom.hom) ≫ e.inv.hom = x.hom
      rw [Category.assoc]
      change x.hom ≫ ((Mon.forget _).map (e.hom ≫ e.inv)) = x.hom
      simp
    exact ⟨h₁.injective, h₂.surjective⟩
  let σe := RingEquiv.ofBijective σ hσ
  let c₁ := ((Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (condensedRingScalarSections Λ' X)))
  let c₂ := ((Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (condensedRingScalarSections Λ X)))
  have hp : ∀ a, p.inv ≫ H.map (c₁ a).unop = (c₂ (σ a)).unop ≫ p.inv := by
    intro a
    apply Mod.regular_hom_ext
    change η[condensedRingObj Λ X] ≫
      (φ ≫ (Mod.regularLift (Mod.regular (condensedRingObj Λ' X))
        (condensedRingScalarSections Λ' X a).hom).hom) =
      η[condensedRingObj Λ X] ≫
        ((Mod.regularLift (Mod.regular (condensedRingObj Λ X))
          (condensedRingScalarSections Λ X (σ a)).hom).hom ≫ φ)
    rw [← Category.assoc, IsMonHom.one_hom, Mod.one_comp_regularLift,
      ← Category.assoc, Mod.one_comp_regularLift]
    simp only [condensedRingScalarSections, σ, Γ.mapFunctor_hom, Γ.map_hom,
      Functor.map_comp, Category.assoc]
    dsimp only [φ, coefficientMap]
    rw [← Functor.map_comp]
    have he : e.inv.hom ≫ e.hom.hom = 𝟙 Λ' :=
      congrArg (fun z ↦ z.hom) e.inv_hom_id
    simp only [he, CategoryTheory.Functor.map_id, Category.comp_id]
  let q := coyonedaSectionsMap σ c₁ c₂ H p hp
  have (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) : IsIso (q.app M) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun f ↦ p.inv ≫ H.map f)
    exact (Iso.homCongr p (Iso.refl _)).bijective.comp
      ((Functor.FullyFaithful.ofFullyFaithful H).map_bijective _ _)
  have : IsIso q := NatIso.isIso_of_isIso_app q
  let F₁ := condensedRingCoefficientSections Λ' X
  let F₂ := condensedRingCoefficientSections Λ X
  let G := ModuleCat.restrictScalars σ
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  have := (finite_point_sections_exact Λ' k).1
  have := (finite_point_sections_exact Λ' k).2
  let M : ConstantModelConstructibleFiniteTor Λ X :=
    ⟨H.mapDerivedCategory.obj K.obj, constantModelCtf_coefficientIso e.symm X K⟩
  have hperf := CategoryTheory.RingDerivedScalarExtension.perfect_restrict
    (CommRingCat.of (Γ Λ')) (CommRingCat.of (Γ Λ)) σe
    (F₂.rightDerivedFunctor.obj M.obj) (h M)
  let z := Functor.mapDerivedCategoryNatIso (asIso q) ≪≫
    Functor.mapDerivedCategoryCompIso H (F₂ ⋙ G) ≪≫
      Functor.isoWhiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryCompIso F₂ G)
  exact perfect_iso
    ((G.mapDerivedCategory.mapIso
      (F₂.rightDerivedFunctorIsoMapDerivedCategory.app M.obj)) ≪≫
      (z.app K.obj).symm ≪≫ (F₁.rightDerivedFunctorIsoMapDerivedCategory.app K.obj).symm)
    hperf

private theorem norm_lift (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (x : E) :
    Padic.coefficientExtensionAbsoluteValue ell (ULift.{u} E) (ULift.up x) =
      Padic.coefficientExtensionAbsoluteValue ell E x := by
  change spectralNorm (Padic ell) (ULift.{u} E) (ULift.up x) =
    spectralNorm (Padic ell) E x
  exact congrArg spectralValue (minpoly.algEquiv_eq
    (ULift.algEquiv (R := Padic ell) (A := E)).symm x)

private def integers_lift (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    Padic.coefficientExtensionIntegers ell E ≃+*
      Padic.coefficientExtensionIntegers ell (ULift.{u} E) := by
  let h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
  let h' := (Padic.extension_integers_dvr ell (ULift.{u} E)
    (Padic.coefficientExtensionAbsoluteValue ell (ULift.{u} E))
    (spectralNorm_extends (K := Padic ell) (L := ULift.{u} E))).choose_spec.choose_spec
  exact RingEquiv.restrict ULift.ringEquiv.symm _ _ (fun x ↦ by
    exact (h.1 x).trans ((h'.1 (ULift.up x)).trans
      (by rw [norm_lift])).symm)

private def quotient_lift (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) :
    Padic.coefficientExtensionRing ell E n ≃+*
      Padic.coefficientExtensionRing ell (ULift.{u} E) n := by
  let e := integers_lift.{u} ell E
  let h := (Padic.extension_integers_dvr ell E
    (Padic.coefficientExtensionAbsoluteValue ell E)
    (spectralNorm_extends (K := Padic ell) (L := E))).choose_spec.choose_spec
  let h' := (Padic.extension_integers_dvr ell (ULift.{u} E)
    (Padic.coefficientExtensionAbsoluteValue ell (ULift.{u} E))
    (spectralNorm_extends (K := Padic ell) (L := ULift.{u} E))).choose_spec.choose_spec
  have hm : (Padic.coefficientExtensionMaximalIdeal ell E).map e.toRingHom =
      Padic.coefficientExtensionMaximalIdeal ell (ULift.{u} E) := by
    ext y
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (h'.2.1 _).mpr
      change Padic.coefficientExtensionAbsoluteValue ell (ULift.{u} E) (ULift.up x.val) < 1
      rw [norm_lift]
      exact (h.2.1 _).mp hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply (h.2.1 _).mpr
      have hh := (h'.2.1 y).mp hy
      have hn := norm_lift.{u} ell E (e.symm y).val
      have he : ULift.up (e.symm y).val = y.val :=
        congrArg Subtype.val (e.apply_symm_apply y)
      rw [he] at hn
      exact hn ▸ hh
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ell E} :
      Set (Padic.coefficientExtensionIntegers ell E)) =
      Padic.coefficientExtensionMaximalIdeal ell E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgen' : Ideal.span ({Padic.coefficientExtensionUniformizer ell (ULift.{u} E)} :
      Set (Padic.coefficientExtensionIntegers ell (ULift.{u} E))) =
      Padic.coefficientExtensionMaximalIdeal ell (ULift.{u} E) :=
    h'.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply Ideal.quotientEquiv _ _ e
  simp only [Padic.coefficientExtensionIdeal, hgen, hgen', Ideal.map_pow]
  change _ = (Ideal.map e.toRingHom (Padic.coefficientExtensionMaximalIdeal ell E)) ^ n
  rw [hm]

private theorem discrete_lift_iso (A : Type) [CommRing A]
    (B : Type u) [CommRing B] [TopologicalSpace B] [DiscreteTopology B]
    (e : A ≃+* B) :
    Nonempty (Mon.mk (IntegralModelsEmbedded.discreteObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj B)) := by
  let J := coherentTopology Profinite.{u}
  let a := (constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
    (CommRingCat.of (ULift.{u + 1} A))
  let a' := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso a
  have : IsMonHom a'.hom := Sheaf.isMonHom_sheafCompose_map _ a.hom
  let ee : ULift.{u + 1} A ≃+* ULift.{u + 1} B :=
    ULift.ringEquiv.trans (e.trans ULift.ringEquiv.symm)
  let b := (constantSheaf J RingCat.{u + 1}).mapIso ee.toRingCatIso
  let b' := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso b
  have : IsMonHom b'.hom := Sheaf.isMonHom_sheafCompose_map _ b.hom
  have : J.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification J _
  obtain ⟨c⟩ := AlgebraicGeometry.ProEtale.constantRingIso J (ULift.{u + 1} B)
  obtain ⟨d⟩ := AlgebraicGeometry.ProEtale.discreteCondensedRing_constant B
  exact ⟨Mon.mkIso' a' ≪≫ Mon.mkIso' b' ≪≫ c.symm ≪≫ d⟩

/-- Actual scalar terminal sections of a constructible finite-Tor point complex
are perfect in each of the four displayed coefficient coordinates.
Source: sk-lem-finite, first proof paragraph
(blueprint: lem-sf-native-point-sections-perfect).

Proof: geometric-point scalar realization gives a bounded finite-projective
representative for the regular-module section complex. Identify its global scalar
ring with terminal evaluation using the tensor-unit universal property; evaluation
at 1 identifies the regular-module sections with the specified sectionwise functor.
Restriction along a scalar ring isomorphism preserves finite projectivity and bounds.
Exactness identifies the right derived functor with the termwise functor. Transport
through the displayed coefficient isomorphisms, including the valuation-ring and
positive uniformizer quotients. No ambient module/scalar equivalence is asserted. -/
theorem native_pointSections_perfect (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Λ : ScalarSixRing.{u}) (E : PadicAlgCl.FiniteIntermediateField ell)
    (hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (K : ConstantModelConstructibleFiniteTor Λ.X (Spec (.of D.k))) :
    let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    DerivedCategory.IsPerfectRingComplex
      ((CohomologyTransport.sections Λ.X (Spec (.of D.k))).mapDerivedCategory.obj K.obj) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  apply point_perfect_of_coarse Λ.X D.k
  obtain ⟨n, hn, hΛ⟩ := hΛ
  let X := Over.mk (𝟙 (Spec (.of D.k)))
  have : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (𝟙 (Spec (.of D.k)))
    infer_instance
  have : QuasiCompact X.hom := by
    change QuasiCompact (𝟙 (Spec (.of D.k)))
    infer_instance
  have : IsSeparated X.hom := by
    change IsSeparated (𝟙 (Spec (.of D.k)))
    infer_instance
  obtain ⟨hfin, hint, hrat, hcl, _, _, _, _⟩ :=
    finite_geometric_point_cohomology D ell hEll E X
  rcases hΛ with h | h | h | h
  all_goals obtain ⟨e⟩ := h
  · let nf := (Padic.coefficientExtensionAbsoluteValue ell (ULift.{u} E)).toNormedField
    let : NormedField (ULift.{u} E) := nf
    let : TopologicalSpace (ULift.{u} E) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let := DerivedNakayama.quotientDiscrete ell (ULift.{u} E) n
    obtain ⟨q⟩ := discrete_lift_iso _ _ (quotient_lift.{u} ell E n)
    exact point_coarse_iso (e ≪≫ q).symm D.k (hfin n hn).1.choose
  · let eR := AlgebraicGeometry.ProEtale.integerRingSheafIso.{u} ell ⟨E.val, E.property⟩
    let q := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
    have : IsMonHom q.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
    exact point_coarse_iso (e ≪≫ Mon.mkIso' q).symm D.k hint.1.choose
  · exact point_coarse_iso e.symm D.k hrat.1.choose
  · exact point_coarse_iso e.symm D.k hcl.1.choose

end AlgebraicGeometry.ProEtale.CondensedRing
