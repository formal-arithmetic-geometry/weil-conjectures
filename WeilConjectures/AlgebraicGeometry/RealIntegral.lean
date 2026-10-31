/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Module.Lattice
import WeilConjectures.AlgebraicGeometry.IntegralPresentationFibreLattice
import WeilConjectures.AlgebraicGeometry.IntegralLocalModelsFixedRank
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import all WeilConjectures.AlgebraicGeometry.SplitCoefficientDerivedFaithfulSupplement

/-! # Integral models for lisse sheaves on geometric curves

Source: current blueprint, sec-purity-real-sheaves/sk-p-real-integral,
`p-real-integral.md` and `p-real-integral.proof.md` (blueprint: p-real-integral).

The auxiliary predicates describe the lattice in the given monodromy representation and
identify it with the actual geometric fibre of the integral sheaf. Coefficient extension
is required to be the adjoint of its inclusion, and reductions use the recorded cokernels
and finite-coefficient monodromy correspondence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.LisseQlbar

namespace AlgebraicGeometry.ProEtale.RealIntegral

variable (l : ℕ) [Fact l.Prime]

/-- The canonical inclusion of integral coefficients into algebraic-closure coefficients.
Source: blueprint p-real-integral, the final scalar-extension clause
(blueprint: p-real-integral). -/
abbrev coefficientInclusion (E : PadicAlgCl.FiniteIntermediateField l) :
    integerRing.{u} l E ⟶ Profinite.padicAlgClRingObj l :=
  integerInclusion l E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
  (c : Correspondence l x G)

set_option maxHeartbeats 0 in
-- These types contain the canonical module-object coefficient transports.
/-- The inclusion on geometric fibres, transported by the recorded natural comparisons.
It is the fibre of the supplied sheaf map; no independent linear map is chosen.
Source: blueprint p-real-integral, the geometric stalk of the integral model
(blueprint: p-real-integral). -/
@[irreducible] def fibreInclusion
    (F : (integralClosure l X).FullSubcategory)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)))
    (i : L.obj ⟶ (Mod.comap (coefficientMap (coefficientInclusion l E) X)).obj F.obj) :
    AddCommGrpCat.of (((c.integral E).functor.obj L).V) ⟶
      AddCommGrpCat.of ((c.algebraic.functor.obj F).V) :=
  (c.integral E).comparison.hom.app L ≫
    fibreMap (integerRing l E) (Profinite.padicAlgClRingObj l) x L.obj F.obj i.hom ≫
    c.algebraic.comparison.inv.app F

set_option maxHeartbeats 0 in
-- Keep canonical coefficient and fibre transports opaque during elaboration.
/-- The lattice is an actual submodule of the specified geometric representation.
Its identification with the integral sheaf's fibre is normalized by `fibreInclusion`.
The finite-image formula uses maps into `V / m^n L`, as in the upstream integral-lattice
interface; stability makes this exactly finiteness of the image on `L / m^n L`.
Source: blueprint p-real-integral, lattice, stability, tensor and finite-image clauses
(blueprint: p-real-integral). -/
@[irreducible] def FibreLattice
    (F : (integralClosure l X).FullSubcategory)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)))
    (i : L.obj ⟶ (Mod.comap (coefficientMap (coefficientInclusion l E) X)).obj F.obj) :
    Prop :=
  let A := Padic.coefficientExtensionIntegers l E
  let V := (c.algebraic.functor.obj F).V
  let M := ((c.integral E).functor.obj L).V
  let a := (algebraMap E (PadicAlgCl l)).comp A.subtype
  letI : Algebra A (PadicAlgCl l) := a.toAlgebra
  letI : Module A V := Module.compHom V a
  FiniteDimensional (PadicAlgCl l) V ∧
    ∃ N : Submodule A V,
      Nonempty (Module.Basis (Fin (Module.finrank (PadicAlgCl l) V)) A N) ∧
      Submodule.IsLattice (PadicAlgCl l) N ∧
      (∀ g : G, (c.algebraic.functor.obj F).ρ g '' (N : Set V) = (N : Set V)) ∧
      (∃ e : M ≃ₗ[A] N, ∀ z : M, (e z : V) = fibreInclusion l x G c F E L i z) ∧
      (∃ t : (PadicAlgCl l ⊗[A] N) ≃ₗ[PadicAlgCl l] V,
        ∀ (b : PadicAlgCl l) (z : N), t (b ⊗ₜ[A] z) = b • (z : V)) ∧
      (∀ (g : G) (z : M),
        fibreInclusion l x G c F E L i (((c.integral E).functor.obj L).ρ g z) =
          (c.algebraic.functor.obj F).ρ g (fibreInclusion l x G c F E L i z)) ∧
      ∀ n : ℕ,
        (Set.range fun g : G ↦ fun z : N ↦
          Submodule.Quotient.mk
            (p := (Padic.coefficientExtensionMaximalIdeal l E ^ n) • N)
            ((c.algebraic.functor.obj F).ρ g z)).Finite

set_option maxHeartbeats 0 in
-- The local models and normalized finite reductions contain large functor types.
/-- The integral model has the fixed local rank of its geometric fibre, and its positive
reductions are the actual finite locally constant sheaves with the corresponding quotient
fibres and actions. The level-zero quotient is the zero sheaf.
Source: blueprint p-real-integral, the integral sheaf and its reductions
(blueprint: p-real-integral). -/
@[irreducible] def SheafModel
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X))) : Prop :=
  (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
    ∀ j : 𝒰.I₀, Nonempty
      ((((ProEtale.upperStar Ab.{u + 1} (𝒰.f j)).mapMod
        (condensedRingObj (integerRing l E) X)).obj L.obj) ≅
      Mod.finiteFree
        ((ProEtale.upperStar Ab.{u + 1} (𝒰.f j)).obj
          (condensedRingObj (integerRing l E) X))
        (Module.finrank (Padic.coefficientExtensionIntegers l E)
          (((c.integral E).functor.obj L).V)))) ∧
  Nonempty (∀ n : ℕ, integralFiniteReduction l x G c.finite E (c.integral E) L n) ∧
  IsZero (cokernel (scalarEnd (integerRing l E) X (integerScalar l E 1) L.obj))

/-- The usual fundamental-group condition, with the connected-space instance bundled
rather than imposed as a separate assumption on a nonempty geometric open curve.
Source: blueprint p-real-integral, geometric fundamental group pi_1(U)
(blueprint: p-real-integral). -/
def IsGeometricFundamentalGroup : Prop :=
  ∃ h : ConnectedSpace X,
    letI := h
    PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber x) G

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj in
private theorem constantSection_one
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : constantSection Λ 1 = η[Λ] := by
  apply ((constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    terminalIsTerminal).homEquiv (𝟙_ Ab.{u + 1}) Λ).injective
  rw [constantSection, Equiv.apply_symm_apply]
  ext ⟨n⟩
  change (n : condensedScalarRing Λ) * 1 =
    (η[(sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj Λ].app
      (op (⊤_ Profinite.{u}))).hom (ULift.up n)
  calc
    _ = (n : condensedScalarRing Λ) := _root_.mul_one _
    _ = n • (1 : condensedScalarRing Λ) := (zsmul_one n).symm
    _ = _ := (InternalAbelianSheafModule.sectionOne_zsmul _
      (op (⊤_ Profinite.{u})) n).symm

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj in
private theorem continuousScalar_one (T : Type) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] :
    continuousScalar T 1 = (1 : condensedScalarRing (Profinite.continuousMapRingObj.{u} T)) := by
  let S := Profinite.continuousMapRingObj.{u} T
  let : MonObj S.obj :=
    Functor.monObjCompForget₂ (Profinite.continuousMapRingPresheaf.{u} T)
  let U := op (⊤_ Profinite.{u})
  change ULift.up (ContinuousMap.const _ 1) =
    ((Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map η[S]).app U).hom
      (ULift.up 1)
  erw [Sheaf.ε_comp_map_one, Functor.one_compForget₂_app,
    AddCommGrpCat.ringMonObj_one_apply]
  simp only [Int.cast_one]
  rfl

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj in
private theorem scalarEnd_one
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    scalarEnd Λ X 1 L = 𝟙 L.X := by
  rw [scalarEnd, constantSection_one]
  change Mod.globalSmul η[condensedRingObj Λ X] L = _
  exact Mod.globalSmul_one L

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj in
private theorem rational_adjunct_mono
    (E : PadicAlgCl.FiniteIntermediateField l)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (fieldRing l E) X)) :
    Mono ((Mod.extendRestrictAdjunction (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).unit.app M) := by
  let H := upperStarFromPoint X
  let a := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  let r := H.map (Profinite.condensedProjection l E)
  have hlin := CategoryTheory.mapLinear H _ _ (Profinite.condensedProjection_linear l E)
  have hret : a ≫ r = 𝟙 _ := by
    change H.map _ ≫ H.map _ = 𝟙 _
    rw [← H.map_comp, Profinite.condensedProjection_retract, H.map_id]
  have hs := unit_retract _ _ a r hlin hret
  have hsM := congr_app hs M
  exact mono_of_mono_fac hsM

include c in
private theorem model_above
    (F : (integralClosure l X).FullSubcategory)
    (E₀ : PadicAlgCl.FiniteIntermediateField l) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField l), E₀ ≤ E ∧
      ∃ (M : (integralField l E X).FullSubcategory),
        Nonempty ((Mod.extendScalars (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj M.obj ≅ F.obj) := by
  obtain ⟨E₁, M₁, hM₁, ⟨e⟩⟩ := F.property.2
  let : FiniteDimensional ℚ_[l] E₁ := E₁.2
  let : FiniteDimensional ℚ_[l] E₀ := E₀.2
  let E : PadicAlgCl.FiniteIntermediateField l := ⟨E₁.1 ⊔ E₀.1, inferInstance⟩
  have h₁ : E₁ ≤ E := show E₁.1 ≤ E₁.1 ⊔ E₀.1 from le_sup_left
  have h₀ : E₀ ≤ E := show E₀.1 ≤ E₁.1 ⊔ E₀.1 from le_sup_right
  let a := coefficientMap (Profinite.padicSubfieldRingObjMap l h₁) X
  let b := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  have hab : a ≫ b =
      coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E₁) X := by
    rw [← coefficientMap_comp, Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl]
  let := (IntermediateField.inclusion h₁).toRingHom.toAlgebra
  have hM := (c.fieldExtension E₁ E h₁).closed ⟨M₁, hM₁⟩
  refine ⟨E, h₀, ⟨(Mod.extendScalars a).obj M₁, hM⟩, ⟨?_⟩⟩
  exact ((Mod.extendScalarsComp a b).app M₁).symm ≪≫
    (Mod.extendScalarsIsoOfEq hab).app M₁ ≪≫ e

set_option maxHeartbeats 0 in
-- Comparing the canonical scalar adjunctions unfolds large module-object functor types.
private theorem integral_presentation
    (F : (integralClosure l X).FullSubcategory)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (M : (integralField l E X).FullSubcategory)
    (e : (Mod.extendScalars (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj M.obj ≅ F.obj) :
    hasLattice (integerRing l E) (Profinite.padicAlgClRingObj l)
      (coefficientInclusion l E) X F.obj := by
  obtain ⟨L, hL, i₁, hi₁, he₁⟩ := M.property.2
  let a := coefficientMap (integerInclusion l E) X
  let b := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  let aAdj := Mod.extendRestrictAdjunction a
  let bAdj := Mod.extendRestrictAdjunction b
  let abAdj := Mod.extendRestrictAdjunction (a ≫ b)
  let compAdj := (aAdj.comp bAdj).ofNatIsoRight (Mod.comapComp a b).symm
  let := he₁
  let e₁ := asIso ((aAdj.homEquiv L M.obj).symm i₁)
  let t : (Mod.extendScalars (a ≫ b)).obj L ≅ F.obj :=
    (Mod.extendScalarsComp a b).app L ≪≫ (Mod.extendScalars b).mapIso e₁ ≪≫ e
  let j := bAdj.homEquiv M.obj F.obj e.hom
  have : Mono (bAdj.unit.app M.obj) := rational_adjunct_mono l E M.obj
  have : Mono j := by
    dsimp only [j]
    rw [Adjunction.homEquiv_unit]
    infer_instance
  have hcomp (f : (Mod.extendScalars b).obj ((Mod.extendScalars a).obj L) ⟶ F.obj) :
      abAdj.homEquiv L F.obj ((Mod.extendScalarsComp a b).hom.app L ≫ f) =
        compAdj.homEquiv L F.obj f := by
    rw [abAdj.homEquiv_naturality_right]
    change abAdj.homEquiv _ _ ((abAdj.leftAdjointUniq compAdj).hom.app L) ≫ _ = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  have ht : abAdj.homEquiv L F.obj t.hom =
      i₁ ≫ (Mod.comap a).map j ≫ (Mod.comapComp a b).inv.app F.obj := by
    change abAdj.homEquiv L F.obj
      ((Mod.extendScalarsComp a b).hom.app L ≫
        (Mod.extendScalars b).map e₁.hom ≫ e.hom) = _
    rw [hcomp, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change aAdj.homEquiv L _ (bAdj.homEquiv _ _
      ((Mod.extendScalars b).map e₁.hom ≫ e.hom)) ≫ _ = _
    rw [bAdj.homEquiv_naturality_left, aAdj.homEquiv_naturality_right]
    simp only [e₁, asIso_hom, Equiv.apply_symm_apply]
    rfl
  let γ := coefficientMap (coefficientInclusion l E) X
  let γAdj := Mod.extendRestrictAdjunction γ
  have hγ : γ = a ≫ b := coefficientMap_comp _ _ X
  let t' : (Mod.extendScalars γ).obj L ≅ F.obj :=
    (Mod.extendScalarsIsoOfEq hγ).app L ≪≫ t
  have ht' : γAdj.homEquiv L F.obj t'.hom =
      abAdj.homEquiv L F.obj t.hom ≫ (Mod.comapCongr hγ).inv.app F.obj := by
    change γAdj.homEquiv L F.obj
      ((Mod.extendScalarsIsoOfEq hγ).hom.app L ≫ t.hom) = _
    rw [γAdj.homEquiv_naturality_right]
    change γAdj.homEquiv _ _ ((γAdj.leftAdjointUniq
      (abAdj.ofNatIsoRight (Mod.comapCongr hγ).symm)).hom.app L) ≫ _ = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      ← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply]
    rfl
  refine ⟨L, hL, γAdj.homEquiv L F.obj t'.hom, ?_, ?_⟩
  · rw [ht', ht]
    let := hi₁
    infer_instance
  · rw [Equiv.symm_apply_apply]
    infer_instance

set_option maxHeartbeats 0 in
-- The statement combines the sheaf, representation and canonical scalar-extension clauses.
/-- A lisse algebraic-closure sheaf on the base change of a nonempty open in a chapter
curve admits an integral model after enlarging any prescribed finite coefficient field.
The chosen correspondence is the one of `thm-lisse-qlbar-representations`; the representation
is its algebraic-closure monodromy of `F`, with its actual geometric-fibre comparison.

Source: current blueprint sec-purity-real-sheaves/sk-p-real-integral/p-real-integral.md,
all clauses (blueprint: p-real-integral).

Proof:
1. Smoothness of the geometric open gives regular, hence normal, stalks. The
normalAlgebraic clause of the correspondence supplies an integral finite-field model.
Enlarge its field to the compositum with E₀, using fieldExtension.closed.
2. Take an integral lattice of that model. Compose the canonical scalar adjunctions
and its scalar-extension isomorphisms. The adjunct inclusion is monic: the first
lattice inclusion is monic and the rational-to-Qlbar unit has a coefficient-linear
retraction. The proof checks the homEquiv identities for the composed adjunctions.
3. The normalized presentation-fibre lattice lemma identifies this particular map
with a stable full lattice in the specified representation, with all finite images.
4. Connectedness is contained in the geometric-fundamental-group hypothesis. The
fixed-rank local-model lemma supplies local trivializations with the fibre rank;
the positive normalized finite reductions are supplied directly by c.reductions.
5. Constant scalar one acts as the identity on an internal module. Its cokernel is
zero, giving the level-zero clause. Combine these data without changing any of the
canonical fibre or scalar-extension maps in the statement. -/
theorem exists_integral_model
    (D : RealSheaves.Setup.{u, v}) (C₀ : Scheme.{u}) [C₀.Over (Spec (.of D.k₀))]
    (_hC : D.IsCurve C₀) (U₀ : C₀.Opens) (_hU₀ : Nonempty U₀)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ D.geometricCurve U₀.toScheme)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
    (_hG : IsGeometricFundamentalGroup x G)
    (c : Correspondence D.l x G)
    (F : Mod (Sheaf (Scheme.ProEt.topology (D.geometricCurve U₀.toScheme)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj D.l) (D.geometricCurve U₀.toScheme)))
    (_hF : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.padicAlgClRingObj D.l) (D.geometricCurve U₀.toScheme)) F)
    (E₀ : PadicAlgCl.FiniteIntermediateField D.l) :
    ∃ (h : integralClosure D.l (D.geometricCurve U₀.toScheme) F)
      (E : PadicAlgCl.FiniteIntermediateField D.l), E₀ ≤ E ∧
      ∃ (L : ObjectProperty.FullSubcategory (CondensedRing.LocallyFree
          (condensedRingObj (integerRing D.l E) (D.geometricCurve U₀.toScheme))))
        (i : L.obj ⟶ (Mod.comap (coefficientMap (coefficientInclusion D.l E)
          (D.geometricCurve U₀.toScheme))).obj F),
        Mono i ∧ IsIso
          (((Mod.extendRestrictAdjunction (coefficientMap (coefficientInclusion D.l E)
            (D.geometricCurve U₀.toScheme))).homEquiv L.obj F).symm i) ∧
        FibreLattice D.l x G c ⟨F, h⟩ E L i ∧ SheafModel D.l x G c E L := by
  classical
  have : Smooth (C₀ ↘ Spec (.of D.k₀)) := _hC.2.2.1
  have : Smooth (U₀.toScheme ↘ Spec (.of D.k₀)) := by
    change Smooth (U₀.ι ≫ (C₀ ↘ Spec (.of D.k₀)))
    infer_instance
  let f : D.geometricCurve U₀.toScheme ⟶ Spec (.of D.k) :=
    pullback.snd (U₀.toScheme ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have : Smooth f := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsRegular (D.geometricCurve U₀.toScheme) := IsRegular.of_smooth f
  have hn : ∀ p : D.geometricCurve U₀.toScheme,
      IsDomain ((D.geometricCurve U₀.toScheme).presheaf.stalk p) ∧
      IsIntegrallyClosed ((D.geometricCurve U₀.toScheme).presheaf.stalk p) :=
    fun p ↦ ⟨inferInstance, IsRegular.isIntegrallyClosed_stalk p⟩
  have h : integralClosure D.l (D.geometricCurve U₀.toScheme) F :=
    c.normalAlgebraic hn F _hF
  obtain ⟨E, hE, M, ⟨eM⟩⟩ := model_above D.l x G c ⟨F, h⟩ E₀
  obtain ⟨L, hL, i, hi, he⟩ := integral_presentation D.l ⟨F, h⟩ E M eM
  refine ⟨h, E, hE, ⟨L, hL⟩, i, hi, he, ?_, ?_⟩
  · unfold FibreLattice fibreInclusion
    have hrep : definedRep D.l G (c.algebraic.functor.obj ⟨F, h⟩) :=
      (c.algebraic.image _).mp ⟨⟨F, h⟩, ⟨Iso.refl _⟩⟩
    exact ⟨hrep.1,
      integralPresentation_fibre_lattice D.l x G c ⟨F, h⟩ E ⟨L, hL⟩ i hi he⟩
  · unfold SheafModel
    refine ⟨?_, ?_, ?_⟩
    · have : ConnectedSpace (D.geometricCurve U₀.toScheme) := _hG.choose
      exact integralLocalModels_fixedRank D.l x G c E ⟨L, hL⟩
    · obtain ⟨r, _⟩ := c.reductions E ⟨L, hL⟩
      exact ⟨r⟩
    · have hs : integerScalar D.l E 1 = 1 :=
        continuousScalar_one (Padic.coefficientExtensionIntegers D.l E)
      have heq : scalarEnd (integerRing D.l E) _ (integerScalar D.l E 1) L = 𝟙 L.X := by
        rw [hs, scalarEnd_one]
      have : Epi (scalarEnd (integerRing D.l E) _ (integerScalar D.l E 1) L) := by
        rw [heq]
        infer_instance
      exact isZero_cokernel_of_epi _

end AlgebraicGeometry.ProEtale.RealIntegral
