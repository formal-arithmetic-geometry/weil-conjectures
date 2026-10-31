/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
import WeilConjectures.AlgebraicGeometry.EtaleAdicPathNaturality
import WeilConjectures.AlgebraicGeometry.EtaleAdicPathPullback
import all WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
import WeilConjectures.AlgebraicGeometry.RationalFinitePathContinuity
import all WeilConjectures.RepresentationTheory.LAdicSubrepresentation

/-!
# The Weil fundamental representation on actual etale adic fibres

Source: Weil II (1.1.6), (1.1.10)
(blueprint: def-wf-fundamental-representation).

The path constructions are reexported from `EtaleAdicPathData`. The extension uses
only naturality, pullback compatibility, and the existing degree-datum group lift.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme
open FiniteEtale

attribute [local irreducible] etaleFinitePathIso etaleIntegralPathIso
  etaleRationalPathIso etaleAlgebraicPathIso

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y z : Spec (.of Ω) ⟶ Y}
variable (l : ℕ) [Fact l.Prime]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]

/-- The degree-one operator is path transport, inverse pullback-fibre identification,
then the actual etale Weil descent datum on the fibre.
Source: Weil II (1.1.10)(i) (blueprint: def-wf-fundamental-representation). -/
def etaleWeilFrobenius (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (β : fiber t ≅ fiber (t ≫ h.hom)) (F : EtaleLisseWeilSheaf l Q h) :
    lisseAlgebraicFiber l Y Q t F.carrier ≃ₗ[Q] lisseAlgebraicFiber l Y Q t F.carrier :=
  (etaleAlgebraicPathIso l Q F.carrier β ≪≫
    (lisseAlgebraicAutomorphismFiberIso h l Q t F.carrier).symm ≪≫
    (eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q _)).symm ≪≫
    (lisseAlgebraicFiberFunctor l Y t Q).mapIso F.str ≪≫
    eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q _)).toLinearEquiv

/-- General degree data and the canonical finite-fibre path for the chosen arithmetic
lift. This is the source's homotopy-exact-sequence interface, independent of dimension.
Source: blueprint def-wf-fundamental-representation, conjugation convention
(blueprint: def-wf-fundamental-representation). -/
structure EtaleWeilDegreeData (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (G : Type v) [Group G] (d : Monodromy.DegreeDatum G) where
  /-- The geometric group identification. -/
  geom : Aut (fiber t) ≃* d.deg.ker
  /-- Transport from t to its Frobenius image, inverse to lambda_s in the source. -/
  path : fiber t ≅ fiber (t ≫ h.hom)
  /-- The finite-fibre conjugation rule fixes the lift convention. -/
  conjugation (g : Aut (fiber t)) :
    (geom (path ≪≫ pullbackPathIso h.hom g ≪≫ path.symm) : G) =
      d.degreeOneElement⁻¹ * geom g * d.degreeOneElement

set_option backward.isDefEq.respectTransparency true in
private theorem etaleWeilDescent_path (h : Y ≅ Y) (F : EtaleLisseWeilSheaf l Q h)
    (τ : fiber y ≅ fiber z) :
    (etaleAlgebraicPathIso l Q F.carrier (pullbackPathIso h.hom τ)).hom ≫
        (lisseAlgebraicAutomorphismFiberIso h l Q z F.carrier).inv ≫
        etaleAlgebraicFiberMap l Q z F.str.hom =
      (lisseAlgebraicAutomorphismFiberIso h l Q y F.carrier).inv ≫
        etaleAlgebraicFiberMap l Q y F.str.hom ≫
        (etaleAlgebraicPathIso l Q F.carrier τ).hom := by
  have e₂ := etaleAlgebraicPath_pullback l Q h F.carrier τ
  have e₃ := etaleAlgebraicPath_naturality l Q F.str.hom τ
  apply (cancel_epi (lisseAlgebraicAutomorphismFiberIso h l Q y F.carrier).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← e₂]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact e₃

set_option backward.isDefEq.respectTransparency true in
private theorem etaleWeilFrobenius_postPath (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (β : fiber t ≅ fiber (t ≫ h.hom)) (F : EtaleLisseWeilSheaf l Q h)
    (g : Aut (fiber t)) (x : lisseAlgebraicFiber l Y Q t F.carrier) :
    etaleWeilFrobenius l Q h t (β ≪≫ pullbackPathIso h.hom g) F x =
      etaleGeometricRep l Q F.carrier t g (etaleWeilFrobenius l Q h t β F x) := by
  have e := etaleWeilDescent_path l Q h F g
  have key := congrArg (fun f ↦ (etaleAlgebraicPathIso l Q F.carrier β).hom ≫ f) e
  rw [← Category.assoc, ← Iso.trans_hom, ← etaleAlgebraicPathIso_trans] at key
  simpa only [etaleWeilFrobenius, etaleGeometricRep, etaleAlgebraicPath,
    etaleAlgebraicFiberMap, CategoryTheory.Iso.toLinearEquiv_apply, Iso.trans_hom,
    ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    Functor.mapIso_hom, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_coe] using
      ConcreteCategory.congr_hom key x

set_option backward.isDefEq.respectTransparency true in
private theorem etaleWeilFrobenius_basePath (h : Y ≅ Y)
    (t t' : Spec (.of Ω) ⟶ Y)
    (β : fiber t ≅ fiber (t ≫ h.hom))
    (β' : fiber t' ≅ fiber (t' ≫ h.hom)) (F : EtaleLisseWeilSheaf l Q h)
    (τ : fiber t ≅ fiber t')
    (hpath : β ≪≫ pullbackPathIso h.hom τ = τ ≪≫ β')
    (x : lisseAlgebraicFiber l Y Q t F.carrier) :
    etaleAlgebraicPath l Q F.carrier τ (etaleWeilFrobenius l Q h t β F x) =
      etaleWeilFrobenius l Q h t' β' F (etaleAlgebraicPath l Q F.carrier τ x) := by
  have e := etaleWeilDescent_path l Q h F τ
  have key := congrArg (fun f ↦ (etaleAlgebraicPathIso l Q F.carrier β).hom ≫ f) e
  have e₁ := congrArg (fun γ ↦ (etaleAlgebraicPathIso l Q F.carrier γ).hom) hpath
  rw [etaleAlgebraicPathIso_trans, etaleAlgebraicPathIso_trans] at e₁
  simp only [Iso.trans_hom] at e₁
  rw [← Category.assoc, ← Category.assoc, e₁] at key
  simpa only [etaleWeilFrobenius, etaleGeometricRep, etaleAlgebraicPath,
    etaleAlgebraicFiberMap, CategoryTheory.Iso.toLinearEquiv_apply, Iso.trans_hom,
    ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    Functor.mapIso_hom, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_coe] using
      (ConcreteCategory.congr_hom key x).symm

set_option backward.isDefEq.respectTransparency true in
private theorem etaleWeilFrobenius_twisted (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (β : fiber t ≅ fiber (t ≫ h.hom)) (F : EtaleLisseWeilSheaf l Q h)
    (g : Aut (fiber t)) (x : lisseAlgebraicFiber l Y Q t F.carrier) :
    etaleWeilFrobenius l Q h t β F
        (etaleGeometricRep l Q F.carrier t
          (β ≪≫ pullbackPathIso h.hom g ≪≫ β.symm) x) =
      etaleGeometricRep l Q F.carrier t g (etaleWeilFrobenius l Q h t β F x) := by
  have h₁ : (β ≪≫ pullbackPathIso h.hom g ≪≫ β.symm) ≪≫ β =
      β ≪≫ pullbackPathIso h.hom g := by simp
  have e₁ := congrArg (fun τ ↦ (etaleAlgebraicPathIso l Q F.carrier τ).hom) h₁
  rw [etaleAlgebraicPathIso_trans l Q F.carrier
    (β ≪≫ pullbackPathIso h.hom g ≪≫ β.symm) β,
    etaleAlgebraicPathIso_trans l Q F.carrier β (pullbackPathIso h.hom g)] at e₁
  simp only [Iso.trans_hom] at e₁
  have e₂ := etaleWeilDescent_path l Q h F g
  have key :
      (etaleAlgebraicPathIso l Q F.carrier
        (β ≪≫ pullbackPathIso h.hom g ≪≫ β.symm)).hom ≫
          (etaleAlgebraicPathIso l Q F.carrier β).hom ≫
          (lisseAlgebraicAutomorphismFiberIso h l Q t F.carrier).inv ≫
          etaleAlgebraicFiberMap l Q t F.str.hom =
        (etaleAlgebraicPathIso l Q F.carrier β).hom ≫
          (lisseAlgebraicAutomorphismFiberIso h l Q t F.carrier).inv ≫
          etaleAlgebraicFiberMap l Q t F.str.hom ≫
          (etaleAlgebraicPathIso l Q F.carrier g).hom := by
    rw [reassoc_of% e₁, e₂]
  simpa only [etaleWeilFrobenius, etaleGeometricRep, etaleAlgebraicPath,
    etaleAlgebraicFiberMap, CategoryTheory.Iso.toLinearEquiv_apply, Iso.trans_hom,
    ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    Functor.mapIso_hom, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_coe] using
      ConcreteCategory.congr_hom key x

/-- A representation is uniquely determined by its geometric restriction and the
specified degree-one operator; this verifies the general extension construction.
Source: Weil II (1.1.10), blueprint def-wf-fundamental-representation
(blueprint: def-wf-fundamental-representation).
Proof: naturality of descent and finite-path conjugation give T rho(g) T^-1 =
rho(sgs^-1), first at finite level and then after both coefficient extensions.
Every w is uniquely a s^n with a geometric. Set rho(w)=rho(a)T^n. The relation
proves multiplicativity, the geometric and degree-one rules, and uniqueness. -/
theorem etaleFundamentalRep_exists (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    ∃! ρ : Representation Q G (lisseAlgebraicFiber l Y Q t F.carrier),
      (∀ g : Aut (fiber t), ρ (D.geom g) = etaleGeometricRep l Q F.carrier t g) ∧
      ρ d.degreeOneElement = (etaleWeilFrobenius l Q h t D.path F).toLinearMap := by
  let V := lisseAlgebraicFiber l Y Q t F.carrier
  let f : d.deg.ker →* (Module.End Q V)ˣ :=
    (etaleGeometricRep l Q F.carrier t).asGroupHom.comp D.geom.symm.toMonoidHom
  let T : (Module.End Q V)ˣ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Q V).symm
      (etaleWeilFrobenius l Q h t D.path F)
  have hT : ∀ u (hu : u ∈ d.deg.ker), T * f ⟨u, hu⟩ * T⁻¹ =
      f ⟨d.degreeOneElement * u * d.degreeOneElement⁻¹,
        d.deg.normal_ker.conj_mem u hu _⟩ := by
    intro u hu
    let g := D.geom.symm
      ⟨d.degreeOneElement * u * d.degreeOneElement⁻¹,
        d.deg.normal_ker.conj_mem u hu _⟩
    have hk : D.geom.symm ⟨u, hu⟩ =
        D.path ≪≫ pullbackPathIso h.hom g ≪≫ D.path.symm := by
      apply D.geom.injective
      apply Subtype.ext
      rw [D.geom.apply_symm_apply, D.conjugation]
      change u = d.degreeOneElement⁻¹ *
        (D.geom (D.geom.symm _) : G) * d.degreeOneElement
      rw [D.geom.apply_symm_apply]
      group
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (etaleWeilFrobenius l Q h t D.path F).surjective w
    change etaleWeilFrobenius l Q h t D.path F
      (etaleGeometricRep l Q F.carrier t (D.geom.symm ⟨u, hu⟩)
        ((etaleWeilFrobenius l Q h t D.path F).symm
          (etaleWeilFrobenius l Q h t D.path F x))) =
      etaleGeometricRep l Q F.carrier t g
        (etaleWeilFrobenius l Q h t D.path F x)
    rw [LinearEquiv.symm_apply_apply, hk, etaleWeilFrobenius_twisted]
  let ρ : Representation Q G V := (Units.coeHom _).comp (d.lift f T hT)
  have hgeom : ∀ g : Aut (fiber t),
      ρ (D.geom g) = etaleGeometricRep l Q F.carrier t g := by
    intro g
    simp only [ρ, MonoidHom.comp_apply, Units.coeHom_apply]
    rw [d.lift_apply_of_mem_ker f T hT (D.geom g).property]
    have hfg : f (D.geom g) = (etaleGeometricRep l Q F.carrier t).asGroupHom g :=
      congrArg (etaleGeometricRep l Q F.carrier t).asGroupHom
        (D.geom.symm_apply_apply g)
    exact (congrArg Units.val hfg).trans
      ((etaleGeometricRep l Q F.carrier t).asGroupHom_apply g)
  have hfrob : ρ d.degreeOneElement =
      (etaleWeilFrobenius l Q h t D.path F).toLinearMap := by
    simp only [ρ, MonoidHom.comp_apply, Units.coeHom_apply]
    rw [d.lift_degreeOneElement]
    rfl
  refine ⟨ρ, ⟨hgeom, hfrob⟩, ?_⟩
  intro σ hσ
  have he : σ.asGroupHom = d.lift f T hT := by
    apply d.eq_lift f T hT
    · ext u : 1
      apply Units.ext
      have hg := hσ.1 (D.geom.symm u)
      rw [D.geom.apply_symm_apply] at hg
      exact (σ.asGroupHom_apply u.val).trans (hg.trans
        ((etaleGeometricRep l Q F.carrier t).asGroupHom_apply
          (D.geom.symm u)).symm)
    · apply Units.ext
      exact hσ.2
  exact MonoidHom.ext fun g ↦ congrArg Units.val (congrArg (fun r ↦ r g) he)


/-- The unique extension, on actual etale adic fibres, with the source's prescribed
geometric action and degree-one operator. This choice is uniquely determined by the
preceding theorem, not data chosen from a bare existence assertion.
Source: Weil II (1.1.10) (blueprint: def-wf-fundamental-representation). -/
def etaleFundamentalRep (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    Representation Q G (lisseAlgebraicFiber l Y Q t F.carrier) :=
  (etaleFundamentalRep_exists l Q h t d D F).exists.choose

private theorem etaleFundamentalRep_spec (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    (∀ g : Aut (fiber t), etaleFundamentalRep l Q h t d D F (D.geom g) =
      etaleGeometricRep l Q F.carrier t g) ∧
    etaleFundamentalRep l Q h t d D F d.degreeOneElement =
      (etaleWeilFrobenius l Q h t D.path F).toLinearMap :=
  (etaleFundamentalRep_exists l Q h t d D F).exists.choose_spec

private theorem scalar_model_isLAdic
    (l : ℕ) [Fact l.Prime] (Q : Type u) [Field Q] [Algebra ℚ_[l] Q]
    [IsAlgClosure ℚ_[l] Q] (G : ProfiniteGrp.{v})
    (E : IntermediateField ℚ_[l] Q) [FiniteDimensional ℚ_[l] E]
    (M : Type w) [AddCommGroup M] [Module E M]
    (σ : G →* (M ≃ₗ[E] M)) (hc : Representation.IsContinuousCoefficient l E G M σ) :
    Representation.IsLAdic l Q G (Q ⊗[E] M)
      (Representation.coefficientScalarExtension E Q G M σ) := by
  classical
  have : FiniteDimensional E M := hc.1
  let b := Module.finBasis E M
  let c := b.baseChange Q
  let τ : G →* ((Fin (Module.finrank E M) → E) ≃ₗ[E]
      (Fin (Module.finrank E M) → E)) :=
    { toFun g := (b.equivFun.symm.trans (σ g)).trans b.equivFun
      map_one' := by
        apply LinearEquiv.ext
        intro x
        change b.equivFun (σ 1 (b.equivFun.symm x)) = x
        rw [map_one]
        exact b.equivFun.apply_symm_apply x
      map_mul' g h := by
        apply LinearEquiv.ext
        intro x
        simp only [LinearEquiv.trans_apply, map_mul, LinearEquiv.mul_apply,
          LinearEquiv.symm_apply_apply] }
  have hτ : Representation.IsContinuousCoefficient l E G _ τ := by
    refine ⟨inferInstance, ?_⟩
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace M := moduleTopology E M
    let : TopologicalSpace (Fin (Module.finrank E M) → E) := moduleTopology E _
    have : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup E M
    have : IsTopologicalAddGroup (Fin (Module.finrank E M) → E) :=
      IsModuleTopology.topologicalAddGroup E _
    have : ContinuousSMul E M := IsModuleTopology.toContinuousSMul E M
    have : ContinuousSMul E (Fin (Module.finrank E M) → E) :=
      IsModuleTopology.toContinuousSMul E _
    have : ContinuousAdd M := (IsModuleTopology.topologicalAddGroup E M).toContinuousAdd
    have : ContinuousAdd (Fin (Module.finrank E M) → E) :=
      (IsModuleTopology.topologicalAddGroup E _).toContinuousAdd
    have hf := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    have hi := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
    exact hf.comp (hc.2.comp (continuous_fst.prodMk (hi.comp continuous_snd)))
  let := Module.compHom (Q ⊗[E] M) (algebraMap E Q)
  apply Representation.isLAdic_of_basis_model l Q G _
    (Representation.coefficientScalarExtension E Q G M σ) E c τ hτ
  intro g x
  have hcomb (x : Fin (Module.finrank E M) → E) :
      Fintype.linearCombination E c x = 1 ⊗ₜ[E] (b.equivFun.symm x) := by
    rw [Module.Basis.equivFun_symm_apply, TensorProduct.tmul_sum]
    simp only [Fintype.linearCombination_apply, c, Module.Basis.baseChange_apply,
      TensorProduct.tmul_smul]
    rfl
  rw [hcomb (τ g x), hcomb x]
  change (1 : Q) ⊗ₜ[E] b.equivFun.symm (b.equivFun (σ g (b.equivFun.symm x))) =
    LinearMap.baseChange Q (σ g).toLinearMap (1 ⊗ₜ[E] b.equivFun.symm x)
  simp

/-- The extension has the source's finite-dimensional l-adic geometric restriction;
with the discrete-degree Weil topology this is continuity of the whole representation.
Source: Weil II (1.1.6), (1.1.10)
(blueprint: def-wf-fundamental-representation).
Proof: the finite-cover germ normalization identifies the geometric restriction
with the evaluation action in cor-galois-lisse-representations. Its integral system
has a finite coefficient-field model, so inverse limits give a continuous integral
action and rationalization gives a continuous E-action. Extend to Q using precisely
the finite model in F's coefficient pair. This proves IsLAdic and finite dimension.
Each degree coset is a translate of the open geometric subgroup; multiplication by
a fixed power of the degree-one operator is a continuous linear automorphism. -/
theorem etaleFundamentalRep_isLAdic (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (F : EtaleLisseWeilSheaf l Q h) :
    Representation.IsLAdic l Q (ProfiniteGrp.of (Aut (fiber t)))
      (lisseAlgebraicFiber l Y Q t F.carrier)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv Q _).toMonoidHom.comp
        (Representation.asGroupHom
          ((etaleFundamentalRep l Q h t d D F).comp
            (d.deg.ker.subtype.comp D.geom.toMonoidHom)))) := by
  let E := (lisseAlgebraicPair l Y Q F.carrier).base
  let M := lisseCoefficientPairModel l Y Q (lisseAlgebraicPair l Y Q F.carrier)
  let ρ : Aut (fiber t) →*
      (lisseRationalFiber l E.val Y t M ≃ₗ[E.val] lisseRationalFiber l E.val Y t M) :=
    { toFun g := (etaleRationalPathIso l E.val M g).toLinearEquiv
      map_one' := by
        apply LinearEquiv.toLinearMap_injective
        unfold etaleRationalPathIso
        change ((ModuleCat.extendScalars _).mapIso
          (etaleIntegralPathIso l E.val M.integral
            (Iso.refl (fiber t)))).toLinearEquiv.toLinearMap = _
        rw [etaleIntegralPath_refl, Functor.mapIso_refl]
        rfl
      map_mul' g h := by
        apply LinearEquiv.toLinearMap_injective
        change (etaleRationalPathIso l E.val M (h ≪≫ g)).toLinearEquiv.toLinearMap = _
        unfold etaleRationalPathIso
        rw [etaleIntegralPath_trans l E.val M.integral h g, Functor.mapIso_trans]
        rfl }
  have hc : Representation.IsContinuousCoefficient l E.val
      (ProfiniteGrp.of (Aut (fiber t))) (lisseRationalFiber l E.val Y t M) ρ := by
    apply rationalFinitePathAction_continuous l E.val t M
      (fun g ↦ (etaleIntegralPathIso l E.val M.integral g).toLinearEquiv)
      (fun n g ↦ (etaleFinitePathIso (Padic.coefficientExtensionIntegers l E.val)
        (M.integral.obj.obj (op n)) (M.integral.property.1 n)
        (etaleIntegralLevel_finite l E.val M.integral n) g).toLinearEquiv)
    · intro n g P a s
      exact etaleFinitePath_germ _ _ _ _ g P a s
    · intro g n x
      exact ConcreteCategory.congr_hom
        (etaleIntegralPath_projection l E.val M.integral g n) x
    · intro g a x
      change (etaleRationalPathIso l E.val M g).toLinearEquiv _ = _
      unfold etaleRationalPathIso
      rfl
  have hres :
      (etaleFundamentalRep l Q h t d D F).comp
          (d.deg.ker.subtype.comp D.geom.toMonoidHom) =
        etaleGeometricRep l Q F.carrier t := by
    apply MonoidHom.ext
    intro g
    exact (etaleFundamentalRep_exists l Q h t d D F).exists.choose_spec.1 g
  rw [hres]
  have he :
      (LinearMap.GeneralLinearGroup.generalLinearEquiv Q _).toMonoidHom.comp
          (etaleGeometricRep l Q F.carrier t).asGroupHom =
        Representation.coefficientScalarExtension E.val Q (Aut (fiber t))
          (lisseRationalFiber l E.val Y t M) ρ := by
    apply MonoidHom.ext
    intro g
    apply LinearEquiv.toLinearMap_injective
    change (etaleAlgebraicPathIso l Q F.carrier g).toLinearEquiv.toLinearMap = _
    unfold etaleAlgebraicPathIso
    rfl
  rw [he]
  exact scalar_model_isLAdic l Q (ProfiniteGrp.of (Aut (fiber t))) E.val
    (lisseRationalFiber l E.val Y t M) ρ hc

/-- Changing the degree-one lift with its prescribed finite-fibre path leaves the
extension unchanged. Source: Weil II (1.1.10), the node's lift-change formula
(blueprint: def-wf-fundamental-representation).
Proof: finite path naturality for the descent map gives T' = rho_geom(a) T.
The geometric actions coincide. The first extension therefore has the second
extension's geometric restriction and its value on s'=a s. Uniqueness of the
extension gives equality, without assuming a Frobenius-stable integral lattice. -/
theorem etaleFundamentalRep_liftChange (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    {G : Type v} [Group G] (d d' : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (D' : EtaleWeilDegreeData h t G d')
    (a : Aut (fiber t))
    (hgeom : ∀ g : Aut (fiber t), (D.geom g : G) = (D'.geom g : G))
    (hlift : d'.degreeOneElement = (D.geom a : G) * d.degreeOneElement)
    (hpath : D'.path = D.path ≪≫ pullbackPathIso h.hom a)
    (F : EtaleLisseWeilSheaf l Q h) :
    etaleFundamentalRep l Q h t d D F = etaleFundamentalRep l Q h t d' D' F := by
  apply (etaleFundamentalRep_exists l Q h t d' D' F).unique
  · constructor
    · intro g
      rw [← hgeom]
      exact (etaleFundamentalRep_spec l Q h t d D F).1 g
    · rw [hlift, map_mul,
        (etaleFundamentalRep_spec l Q h t d D F).1,
        (etaleFundamentalRep_spec l Q h t d D F).2, hpath]
      apply LinearMap.ext
      intro x
      exact (etaleWeilFrobenius_postPath l Q h t D.path F a x).symm
  · exact (etaleFundamentalRep_exists l Q h t d' D' F).exists.choose_spec

/-- Change of geometric base point is the normalized etale adic path isomorphism.
Source: Weil II (1.1.6), (1.1.10)
(blueprint: def-wf-fundamental-representation).
Proof: the geometric intertwining equation is the finite-cover path conjugation
identity, then its inverse limit and scalar extensions. The finite-path square
with Frobenius, naturality of descent and the pullback-fibre identification give
the degree-one intertwining equation. Every Weil element is a geometric element
times a power of the degree-one element, so these two equations give the result. -/
theorem etaleFundamentalRep_changeBasePoint (h : Y ≅ Y)
    (t t' : Spec (.of Ω) ⟶ Y) {G : Type v} [Group G] (d : Monodromy.DegreeDatum G)
    (D : EtaleWeilDegreeData h t G d) (D' : EtaleWeilDegreeData h t' G d)
    (τ : fiber t ≅ fiber t')
    (hgeom : ∀ g : Aut (fiber t),
      D'.geom (τ.symm ≪≫ g ≪≫ τ) = D.geom g)
    (hpath : D.path ≪≫ pullbackPathIso h.hom τ = τ ≪≫ D'.path)
    (F : EtaleLisseWeilSheaf l Q h) :
    ∀ (g : G) (x : lisseAlgebraicFiber l Y Q t F.carrier),
      etaleAlgebraicPath l Q F.carrier τ (etaleFundamentalRep l Q h t d D F g x) =
        etaleFundamentalRep l Q h t' d D' F g (etaleAlgebraicPath l Q F.carrier τ x) := by
  let ρ := etaleFundamentalRep l Q h t d D F
  let ρ' := etaleFundamentalRep l Q h t' d D' F
  let S := (etaleAlgebraicPath l Q F.carrier τ).toLinearMap
  have hgeom' (a : Aut (fiber t)) (x : lisseAlgebraicFiber l Y Q t F.carrier) :
      S (ρ (D.geom a) x) = ρ' (D.geom a) (S x) := by
    have ha := congrArg Subtype.val (hgeom a)
    change etaleAlgebraicPath l Q F.carrier τ
      (etaleFundamentalRep l Q h t d D F (D.geom a) x) =
        etaleFundamentalRep l Q h t' d D' F (D.geom a)
          (etaleAlgebraicPath l Q F.carrier τ x)
    rw [(etaleFundamentalRep_spec l Q h t d D F).1,
      ← ha, (etaleFundamentalRep_spec l Q h t' d D' F).1 (τ.symm ≪≫ a ≪≫ τ)]
    have he : a ≪≫ τ = τ ≪≫ (τ.symm ≪≫ a ≪≫ τ) := by simp
    have e := congrArg (fun γ ↦ (etaleAlgebraicPathIso l Q F.carrier γ).hom) he
    rw [etaleAlgebraicPathIso_trans l Q F.carrier a τ,
      etaleAlgebraicPathIso_trans l Q F.carrier τ (τ.symm ≪≫ a ≪≫ τ)] at e
    simpa only [etaleGeometricRep, etaleAlgebraicPath, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearEquiv.coe_coe, CategoryTheory.Iso.toLinearEquiv_apply,
      Iso.trans_hom, ModuleCat.comp_apply] using ConcreteCategory.congr_hom e x
  have hfrob (x : lisseAlgebraicFiber l Y Q t F.carrier) :
      S (ρ d.degreeOneElement x) = ρ' d.degreeOneElement (S x) := by
    change etaleAlgebraicPath l Q F.carrier τ
      (etaleFundamentalRep l Q h t d D F d.degreeOneElement x) =
        etaleFundamentalRep l Q h t' d D' F d.degreeOneElement
          (etaleAlgebraicPath l Q F.carrier τ x)
    rw [(etaleFundamentalRep_spec l Q h t d D F).2,
      (etaleFundamentalRep_spec l Q h t' d D' F).2]
    exact etaleWeilFrobenius_basePath l Q h t t' D.path D'.path F τ hpath x
  let H : Subgroup G :=
    { carrier := {g | ∀ x, S (ρ g x) = ρ' g (S x)}
      mul_mem' := fun {a b} ha hb x ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [ha, hb]
      one_mem' := fun x ↦ by simp
      inv_mem' := fun {a} ha x ↦ by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have hx := ha (ρ a⁻¹ x)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at hx
        rw [hx, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] }
  intro g x
  have hg : g = (g * (d.degreeOneElement ^ (d.deg g).toAdd)⁻¹) *
      d.degreeOneElement ^ (d.deg g).toAdd := by group
  have hmem : g ∈ H := by
    rw [hg]
    apply H.mul_mem
    · let a := D.geom.symm ⟨_, d.mul_inv_zpow_mem_ker g⟩
      have ha : (D.geom a : G) = g * (d.degreeOneElement ^ (d.deg g).toAdd)⁻¹ :=
        congrArg Subtype.val (D.geom.apply_symm_apply _)
      exact ha ▸ hgeom' a
    · exact H.zpow_mem hfrob _
  exact hmem x

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.WeilGroup
open AlgebraicGeometry.Scheme Scheme.FiniteEtale
/-- The coefficient-free finite-path data already used upstream, now applied to etale
adic fibres. There is no new choice of arithmetic lift or geometric action.
Source: blueprint def-wf-fundamental-representation
(blueprint: def-wf-fundamental-representation). -/
def WeilMonodromyData.toEtale
    {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
    [C.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))]
    {W : WeilGroup (C ↘ Spec (.of K))} {B : BasePointData W}
    (D : WeilMonodromyData B) :
    EtaleWeilDegreeData (C ↘ Spec (.of K)).geometricGaloisFrobenius B.t
      W.carrier D.degreeDatum where
  geom := D.geomEquiv.toMulEquiv
  path := B.frobPath
  conjugation := D.geomEquiv_conj
end AlgebraicGeometry.WeilGroup
