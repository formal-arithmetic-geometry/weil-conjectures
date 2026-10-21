/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.HomComplexToSingle
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Category.ModuleCat.Products
import Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact

/-! # Scalar finite-projective dual realization

Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ, scalar
finite-free-retract calculation (blueprint: lem-sfb-scalar-perfect-dual-realization).
The realization uses the existing constant-module sheaf and ordinary change of rings.
The scalar dual is the existing module-valued Hom complex into R[0].
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ScalarPerfectDual

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Type u) [CommRing R] (B : Sheaf J CommRingCat.{u})
  (α : (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of R) ⟶ B)

/-- The existing category of B-module sheaves.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev Modules := ringedSiteModules.{u} ((sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj B)

/-- Ordinary scalar realization, by constant sheafification and sheaf change of rings.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def realize (V : ModuleCat.{u} R) : Modules J B :=
  SheafOfModules.changeOfRings.{u, u, u} α ((SheafOfModules.constantCoefficientModule J R).obj V)

/-- Realization of a linear map is the sheafified map id_B tensor f.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def realizeMap {V W : ModuleCat.{u} R} (f : V ⟶ W) :
    realize J R B α V ⟶ realize J R B α W :=
  SheafOfModules.changeOfRingsHom.{u, u, u} α _
    ((SheafOfModules.constantCoefficientModule J R).map f)

/-- The maps of scalar realization satisfy the additive functor laws.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: constant sheafification is additive. Before the second sheafification,
id_B tensor f preserves identities, composites and sums, by evaluation on pure tensors.
The additive module sheafification functor preserves these three equalities. -/
theorem realizeMap_laws :
    (∀ V : ModuleCat.{u} R, realizeMap J R B α (𝟙 V) = 𝟙 _) ∧
    (∀ {V W T : ModuleCat.{u} R} (f : V ⟶ W) (g : W ⟶ T),
      realizeMap J R B α (f ≫ g) = realizeMap J R B α f ≫ realizeMap J R B α g) ∧
    (∀ {V W : ModuleCat.{u} R} (f g : V ⟶ W),
      realizeMap J R B α (f + g) = realizeMap J R B α f + realizeMap J R B α g) := by
  let K := SheafOfModules.constantCoefficientModule J R
  let A := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)
  let : A.Additive :=
    (PresheafOfModules.sheafificationAdjunction (R :=
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).left_adjoint_additive
  let : (PresheafOfModules.sheafification
      (SheafOfModules.constantCoefficientUnit J R)).Additive :=
    (PresheafOfModules.sheafificationAdjunction
      (SheafOfModules.constantCoefficientUnit J R)).left_adjoint_additive
  have hK : K.Additive := by
    dsimp [K, SheafOfModules.constantCoefficientModule]
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · intro V
    unfold realizeMap SheafOfModules.changeOfRingsHom
    rw [K.map_id]
    change A.map _ = 𝟙 _
    convert A.map_id _ using 1
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  · intro V W T f g
    unfold realizeMap SheafOfModules.changeOfRingsHom
    rw [K.map_comp, ← A.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _
  · intro V W f g
    unfold realizeMap SheafOfModules.changeOfRingsHom
    rw [K.map_add, ← A.map_add]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    let := (α.hom.app U).hom.toAlgebra
    change (1 : B.obj.obj U) ⊗ₜ[_] ((K.map f).val.app U x + (K.map g).val.app U x) =
      (1 : B.obj.obj U) ⊗ₜ[_] ((K.map f).val.app U x) +
        (1 : B.obj.obj U) ⊗ₜ[_] ((K.map g).val.app U x)
    exact TensorProduct.tmul_add _ _ _


/-- The canonical additive scalar-realization functor.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def realization : ModuleCat.{u} R ⥤ Modules J B where
  obj := realize J R B α
  map := realizeMap J R B α
  map_id := (realizeMap_laws J R B α).1
  map_comp := (realizeMap_laws J R B α).2.1

/-- Scalar realization is additive, so it acts termwise on complexes.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: this is the sum clause of realizeMap_laws. -/
instance realization_additive : (realization J R B α).Additive where
  map_add {_V _W} {f g} := (realizeMap_laws J R B α).2.2 f g

/-- Termwise scalar realization, including the differential.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev complexRealization :=
  (realization J R B α).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The image of a scalar in the sheaf B.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def scalar (U : Cᵒᵖ) (r : R) : B.obj.obj U :=
  α.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U r)

/-- A constant local section of the existing constant-module sheaf.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def constantElement (V : ModuleCat.{u} R) (U : Cᵒᵖ) (v : V) :
    ((SheafOfModules.constantCoefficientModule J R).obj V).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (SheafOfModules.constantCoefficientUnit J R)).unit.app
      ((SheafOfModules.strictPerfectConstantPresheaf (C := C) R).obj V)).app U) v

/-- The actual local pure tensor b tensor v in scalar realization.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def tensorElement (V : ModuleCat.{u} R) (U : Cᵒᵖ) (b : B.obj.obj U) (v : V) :
    (realize J R B α V).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} α
        ((SheafOfModules.constantCoefficientModule J R).obj V))).app U)
    (@TensorProduct.tmul _ _ (B.obj.obj U)
      (((SheafOfModules.constantCoefficientModule J R).obj V).val.obj U) _ _
      (Module.compHom _ (α.hom.app U).hom)
      (((SheafOfModules.constantCoefficientModule J R).obj V).val.obj U).isModule
      b (constantElement J R V U v))


/-- The scalar dual uses the existing total Hom complex, with its signed differential.
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev dual (F : CochainComplex (ModuleCat.{u} R) ℤ) :=
  CochainComplex.moduleHomComplex F
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- Projection of the total scalar Hom complex onto its unique nonzero target factor.
This specifies both its terms and its precise differential sign.
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: evaluate a degree-q cochain at (-q,0), then use the canonical single-complex
identification in degree zero. All other factors have zero target. The inverse extends
by zero, so this is a linear isomorphism. The Hom differential has zero target term;
its surviving term is -(-1)^q times precomposition by d_F. -/
theorem dual_coordinates (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ τ : ∀ q : ℤ, (dual R F).X q ≅ ModuleCat.of R (Module.Dual R (F.X (-q))),
      (∀ (q : ℤ) (z : (dual R F).X q),
        (τ q).hom z =
          (z.v (-q) 0 (neg_add_cancel q) ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (ModuleCat.of R R)).hom).hom) ∧
      ∀ q : ℤ, (dual R F).d q (q + 1) ≫ (τ (q + 1)).hom =
        (τ q).hom ≫ ModuleCat.ofHom
          (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap) := by
  classical
  let M := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let s : M.X 0 ≅ ModuleCat.of R R :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)
  let e (q : ℤ) : (dual R F).X q →ₗ[R] Module.Dual R (F.X (-q)) :=
    { toFun := fun z ↦ (z.v (-q) 0 (neg_add_cancel q) ≫ s.hom).hom
      map_add' := by
        intro z w
        change ((z.v (-q) 0 _ + w.v (-q) 0 _) ≫ s.hom).hom = _
        simp only [Preadditive.add_comp, ModuleCat.hom_add]
      map_smul' := by
        intro r z
        change ((r • z.v (-q) 0 _) ≫ s.hom).hom = _
        simp only [Linear.smul_comp, ModuleCat.hom_smul, RingHom.id_apply] }
  have hinj (q : ℤ) : Function.Injective (e q) := by
    intro z w h
    apply CochainComplex.HomComplex.Cochain.ext
    intro p t hpt
    by_cases ht : t = 0
    · have h' : ∀ t (ht : t = 0) (hp : -q + q = t),
          z.v (-q) t hp = w.v (-q) t hp := by
        intro t ht hp
        subst t
        apply (cancel_mono s.hom).1
        exact ModuleCat.hom_ext h
      have hp : p = -q := by omega
      subst p
      exact h' _ ht _
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 (ModuleCat.of R R) t ht).eq_of_tgt _ _
  have hsurj (q : ℤ) : Function.Surjective (e q) := by
    intro φ
    refine ⟨CochainComplex.HomComplex.Cochain.single
      (ModuleCat.ofHom φ ≫ s.inv) q, ?_⟩
    dsimp [e]
    rw [CochainComplex.HomComplex.Cochain.single_v]
    change (ModuleCat.ofHom φ ≫ s.inv ≫ s.hom).hom = φ
    simp only [s.inv_hom_id, Category.comp_id, ModuleCat.hom_ofHom]
  let τ (q : ℤ) := (LinearEquiv.ofBijective (e q) ⟨hinj q, hsurj q⟩).toModuleIso
  refine ⟨τ, fun q z ↦ rfl, ?_⟩
  intro q
  apply ModuleCat.hom_ext
  ext z x
  change ((CochainComplex.HomComplex.δ q (q + 1) z).v (-(q + 1)) 0
    (by omega) ≫ s.hom) x = _
  rw [CochainComplex.HomComplex.δ_v q (q + 1) rfl z _ _ (by omega)
    (-1) (-q) rfl (by omega)]
  simp [τ, e, Int.negOnePow_add, LinearMap.dualMap_apply]


/-- The canonical evaluation formula determines a unique scalar-dual comparison.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: the formula is balanced, B-linear, additive and commutes with restriction.
Extend first over the constant-module sheafification, then over the scalar tensor
sheafification. Uniqueness follows from local tensor generators. -/
theorem evaluation_existsUnique (V : ModuleCat.{u} R) :
    ∃! β : realize J R B α (ModuleCat.of R (Module.Dual R V)) ⟶
        SheafOfModules.homObj (R := B) (realize J R B α V)
          (SheafOfModules.unit.{u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
      ∀ (U : Cᵒᵖ) (b b' : B.obj.obj U) (φ : Module.Dual R V) (v : V),
        (β.val.app U (tensorElement J R B α _ U b φ)).app
          (op (Over.mk (𝟙 U.unop))) (tensorElement J R B α V U b' v) =
            b * b' * scalar J R B α U (φ v) := by
  sorry

/-- The evaluation comparison, uniquely characterized by its formula on local generators.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def evaluation (V : ModuleCat.{u} R) :=
  (evaluation_existsUnique J R B α V).exists.choose

/-- Evaluation is natural under scalar module maps and invertible on finite projectives.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: both naturality composites send b tensor ψ, evaluated at b' tensor v, to
bb'ψ(f(v)). Uniqueness of sheafification gives equality. For a finite projective V,
choose a finite free splitting, with dual generators v_j, λ_j. The inverse sends h
to the finite sum of h(1 tensor v_j) tensor λ_j. The identities v=Σλ_j(v)v_j and
φ=Σφ(v_j)λ_j prove both inverse relations. Rank zero and V=0 are included. -/
theorem evaluation_natural_isIso :
    (∀ {V W : ModuleCat.{u} R} (f : V ⟶ W),
      (realization J R B α).map (ModuleCat.ofHom f.hom.dualMap) ≫
          evaluation J R B α V =
        evaluation J R B α W ≫ SheafOfModules.homObjMap (R := B)
          ((realization J R B α).map f) (𝟙 _)) ∧
    ∀ (V : ModuleCat.{u} R), Module.Finite R V → Module.Projective R V →
      IsIso (evaluation J R B α V) := by
  sorry

/-- The canonical scalar degree coordinates, specified by evaluation at (-q,0).
Source: Stacks 0A8X (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def coordinates (F : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (dual_coordinates R F).choose

/-- B in degree zero, in the existing cochain-complex category.
Source: Stacks 08JH (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
abbrev unitComplex := (CochainComplex.singleFunctor (Modules J B) 0).obj
  (SheafOfModules.unit.{u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

/-- Constant module sheafification identifies the scalar unit with the ring sheaf. -/
private def constantUnitIso :
    (SheafOfModules.constantCoefficientModule J R).obj (ModuleCat.of R R) ≅
      SheafOfModules.unit (SheafOfModules.constantCoefficientRing J R) := by
  let A₀ := SheafOfModules.constantCoefficientRing J R
  let P := (SheafOfModules.strictPerfectConstantPresheaf (C := C) R).obj (ModuleCat.of R R)
  let η := SheafOfModules.constantCoefficientUnit J R
  let a : P ⟶ (PresheafOfModules.restrictScalars η).obj (SheafOfModules.unit A₀).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars η).obj (SheafOfModules.unit A₀).val).obj U)
        { toFun := η.app U
          map_add' := (η.app U).hom.map_add
          map_smul' := (η.app U).hom.map_mul }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        exact (ConcreteCategory.congr_hom (η.naturality f) b) }
  let g : P.presheaf ⟶ (SheafOfModules.unit A₀).val.presheaf :=
    (PresheafOfModules.toPresheaf.{u} _).map a
  have : Presheaf.IsLocallyInjective J g := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem J η x y h
  have : Presheaf.IsLocallySurjective J g := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J η x
  let e : (SheafOfModules.constantCoefficientModule J R).obj (ModuleCat.of R R) ⟶
      SheafOfModules.unit A₀ :=
    (PresheafOfModules.sheafificationHomEquiv.{u} η (P := P) (F := SheafOfModules.unit A₀)).symm a
  let q := (SheafOfModules.toSheaf A₀).map e
  have hfac : toSheafify J P.presheaf ≫ q.hom = g := by
    have h := congrArg ((PresheafOfModules.toPresheaf.{u} _).map)
      ((PresheafOfModules.sheafificationHomEquiv.{u} η
        (P := P) (F := SheafOfModules.unit A₀)).apply_symm_apply a)
    exact h
  have : Presheaf.IsLocallyInjective J q.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J g hfac
  have : Presheaf.IsLocallySurjective J q.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).1 ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (SheafOfModules.toSheaf A₀)
  exact asIso e

/-- Ordinary sheaf change of rings, with its functor laws proved sectionwise. -/
private def extension :
    SheafOfModules.{u} (SheafOfModules.constantCoefficientRing J R) ⥤ Modules J B where
  obj := SheafOfModules.changeOfRings.{u, u, u} α
  map f := SheafOfModules.changeOfRingsHom.{u, u, u} α _ f
  map_id M := by
    unfold SheafOfModules.changeOfRingsHom
    let A := PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B) (𝟙 _)
    change A.map _ = 𝟙 _
    convert A.map_id _ using 1
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  map_comp f g := by
    unfold SheafOfModules.changeOfRingsHom
    rw [← Functor.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor multiplication identifies the extended scalar unit. -/
private def extensionUnitIso :
    SheafOfModules.changeOfRings.{u, u, u} α
      (SheafOfModules.unit (SheafOfModules.constantCoefficientRing J R)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) := by
  let A := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of R)
  let A₀ := SheafOfModules.constantCoefficientRing J R
  let B₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let M := SheafOfModules.unit A₀
  let e : SheafOfModules.changeOfRingsPresheaf.{u, u, u} α M ≅
      (SheafOfModules.unit B₀).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      let := (α.hom.app U).hom.toAlgebra
      exact (TensorProduct.AlgebraTensorModule.rid
        (A.obj.obj U) (B.obj.obj U) (B.obj.obj U)).toModuleIso) (by
      intro U V i
      let := (α.hom.app U).hom.toAlgebra
      let := (α.hom.app V).hom.toAlgebra
      apply ModuleCat.ExtendScalars.hom_ext
      intro a
      change (TensorProduct.AlgebraTensorModule.rid
          (A.obj.obj V) (B.obj.obj V) (B.obj.obj V))
          (SheafOfModules.changeOfRingsMap α M i _) = _
      dsimp only [SheafOfModules.changeOfRingsMap]
      rw [Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap α M i) 1 a]
      change α.hom.app V (A₀.obj.map i a) * B.obj.map i 1 =
        B.obj.map i (α.hom.app U a * 1)
      simp only [map_one, mul_one]
      exact ConcreteCategory.congr_hom (α.hom.naturality i) a)
  exact (PresheafOfModules.sheafification (R := B₀) (𝟙 _)).mapIso e ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := B₀) (𝟙 _)).counit).app
      (SheafOfModules.unit B₀)

private def realizationUnitIso :
    (realization J R B α).obj (ModuleCat.of R R) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  (extension J R B α).mapIso (constantUnitIso J R) ≪≫ extensionUnitIso J R B α

private def finiteFreeIso (n : ℕ) :
    (realization J R B α).obj (ModuleCat.of R (Fin n → R)) ≅
      ∏ᶜ fun _ : Fin n ↦
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
  (realization J R B α).mapIso (ModuleCat.piIsoPi
    (fun _ : Fin n ↦ ModuleCat.of R R)).symm ≪≫
    PreservesProduct.iso (realization J R B α) (fun _ : Fin n ↦ ModuleCat.of R R) ≪≫
    Pi.mapIso (fun _ : Fin n ↦ realizationUnitIso J R B α)

private def productFreeIso (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ≅
      SheafOfModules.free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
        (ULift.{u} (Fin n)) :=
  (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.reindex (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n))
      (fun _ : ULift.{u} (Fin n) ↦
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

attribute [local irreducible] constantUnitIso extension extensionUnitIso realizationUnitIso
  finiteFreeIso productFreeIso

/-- A bounded scalar finite-projective complex realizes to finite-free retract terms;
internal sheaf Hom out of each term is exact, and every K-injective resolution of B[0]
gives a quasi-isomorphism of Hom complexes. No flatness hypothesis is used.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof:
1. Use the supplied scalar splittings i_r,p_r, as in the coefficient-package node.
Constant sheafification and ordinary scalar extension preserve their splitting relation.
The coordinate maps identify C_B(R^N) with B^N, including N=0. This constructs the package.
2. Apply lem-sfb-ringed-site-finite-retract-dual-exact to each resulting term. It gives
exactness on short exact sequences of sheaves, not exactness of global sections.
3. Additivity gives C_B(0)=0, so the realized complex has the same finite bounds.
Apply lem-pc-bounded-exact-term-hom-quasi-iso to B[0]→I for any K-injective resolution.
Its target can be unbounded. This is the canonical comparison used in derived Hom. -/
theorem scalarPerfectDualRealization
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F)
    (a b : ℤ) (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)) :
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackage
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      ((complexRealization J R B α).obj F)) ∧
    (∀ (q : ℤ) (S : ShortComplex (Modules J B)), S.ShortExact →
      ∃ hz : SheafOfModules.homObjMap (R := B)
          (𝟙 (((complexRealization J R B α).obj F).X q)) S.f ≫
        SheafOfModules.homObjMap (R := B)
          (𝟙 (((complexRealization J R B α).obj F).X q)) S.g = 0,
        (ShortComplex.mk
          (SheafOfModules.homObjMap (R := B)
            (𝟙 (((complexRealization J R B α).obj F).X q)) S.f)
          (SheafOfModules.homObjMap (R := B)
            (𝟙 (((complexRealization J R B α).obj F).X q)) S.g) hz).ShortExact) ∧
    ∀ (I : CochainComplex (Modules J B) ℤ) (ι : unitComplex J B ⟶ I),
      QuasiIso ι → I.IsKInjective →
        QuasiIso (((homComplexFunctor (R := B)).obj
          (op ((complexRealization J R B α).obj F))).map ι) := by
  classical
  let T := realization J R B α
  let P' : SheafOfModules.StrictPerfectCoefficientPackage
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
      ((complexRealization J R B α).obj F) :=
    { N := P.N
      i := fun r ↦ T.map (P.i r) ≫ (finiteFreeIso J R B α (P.N r)).hom
      p := fun r ↦ (finiteFreeIso J R B α (P.N r)).inv ≫ T.map (P.p r)
      splitting := by
        intro r
        change (T.map (P.i r) ≫ (finiteFreeIso J R B α (P.N r)).hom) ≫
          ((finiteFreeIso J R B α (P.N r)).inv ≫ T.map (P.p r)) =
            𝟙 (T.obj (F.X r))
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← T.map_comp, P.splitting,
          T.map_id] }
  have hexact (q : ℤ) (S : ShortComplex (Modules J B)) (hS : S.ShortExact) :
      ∃ hz : SheafOfModules.homObjMap (R := B) (𝟙 (((complexRealization J R B α).obj F).X q))
            S.f ≫ SheafOfModules.homObjMap (R := B)
              (𝟙 (((complexRealization J R B α).obj F).X q)) S.g = 0,
        (ShortComplex.mk
          (SheafOfModules.homObjMap (R := B) (𝟙 _) S.f)
          (SheafOfModules.homObjMap (R := B) (𝟙 _) S.g) hz).ShortExact := by
    let e := productFreeIso J B (P.N q)
    have hs : (P'.i q ≫ e.hom) ≫ (e.inv ≫ P'.p q) = 𝟙 _ := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, P'.splitting]
    exact (SheafOfModules.ringedSite_finite_retract_dual_exact.{u, u, u}
      (R := B) (P.N q) _ (P'.i q ≫ e.hom) (e.inv ≫ P'.p q) hs).2.2.2.2.2.1 S hS
  refine ⟨⟨P'⟩, hexact, ?_⟩
  intro I ι hι _
  have := hι
  apply quasiIso_homComplex_map_of_bounded_exact_terms J B _ _ hexact ι
  exact ⟨a, b, fun q hq ↦ T.map_isZero (hbounded q hq)⟩


/-- The degreewise scalar evaluation maps form the uniquely normalized complex isomorphism.
Source: Stacks 08JJ and 0A8X (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: in degree q the only surviving Hom factor is Hom_B(E^(-q),B).
Use evaluation at F^(-q), preceded by the scalar Hom coordinate isomorphism.
Finite-projective evaluation is invertible by evaluation_natural_isIso. Naturality
for d_F identifies the two differentials, both -(-1)^q times precomposition.
The product projections therefore assemble these components into a chain isomorphism.
The surviving projection is invertible, so the component equation determines it uniquely. -/
theorem comparison_existsUnique
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F) :
    ∃! κ : (complexRealization J R B α).obj (dual R F) ≅
        signedSheafDualComplex (R := B) ((complexRealization J R B α).obj F)
          (SheafOfModules.unit.{u, u, u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
      ∀ q : ℤ, HEq (κ.hom.f q)
        ((realization J R B α).map ((coordinates R F q).hom) ≫
          evaluation J R B α (F.X (-q))) := by
  classical
  let T := realization J R B α
  have hfp (r : ℤ) : Module.Finite R (F.X r) ∧ Module.Projective R (F.X r) := by
    have hp : Function.Surjective (P.p r) := by
      intro x
      exact ⟨P.i r x, ConcreteCategory.congr_hom (P.splitting r) x⟩
    constructor
    · exact Module.Finite.of_surjective (P.p r).hom hp
    · exact Module.Projective.of_split (P.i r).hom (P.p r).hom
        (congrArg ModuleCat.Hom.hom (P.splitting r))
  have hi (q : ℤ) : IsIso (evaluation J R B α (F.X (-q))) :=
    (evaluation_natural_isIso J R B α).2 _ (hfp (-q)).1 (hfp (-q)).2
  let e (q : ℤ) := T.mapIso (coordinates R F q) ≪≫
    @asIso _ _ _ _ (evaluation J R B α (F.X (-q))) (hi q)
  let κ : (complexRealization J R B α).obj (dual R F) ≅
      signedSheafDualComplex (R := B) ((complexRealization J R B α).obj F)
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro q r hqr
      have hr : r = q + 1 := hqr.symm
      subst r
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
      simp only [signedSheafDualComplex, CochainComplex.of_d]
      change (T.map (coordinates R F q).hom ≫ evaluation J R B α (F.X (-q))) ≫
          (-q.negOnePow • SheafOfModules.homObjMap
            (T.map (F.d (-(q + 1)) (-q))) (𝟙 _)) =
        T.map ((dual R F).d q (q + 1)) ≫
          (T.map (coordinates R F (q + 1)).hom ≫
            evaluation J R B α (F.X (-(q + 1))))
      have hd : (dual R F).d q (q + 1) ≫ (coordinates R F (q + 1)).hom =
          (coordinates R F q).hom ≫ ModuleCat.ofHom
            (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap) :=
        (dual_coordinates R F).choose_spec.2 q
      have hn := (evaluation_natural_isIso J R B α).1 (F.d (-(q + 1)) (-q))
      have hs : evaluation J R B α (F.X (-q)) ≫
            (-q.negOnePow • SheafOfModules.homObjMap
              (T.map (F.d (-(q + 1)) (-q))) (𝟙 _)) =
          T.map (ModuleCat.ofHom
            (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap)) ≫
              evaluation J R B α (F.X (-(q + 1))) := by
        rw [show ModuleCat.ofHom (-q.negOnePow •
            (F.d (-(q + 1)) (-q)).hom.dualMap) =
            -q.negOnePow • ModuleCat.ofHom (F.d (-(q + 1)) (-q)).hom.dualMap from rfl]
        simp only [Units.neg_smul, Functor.map_neg, Functor.map_units_smul,
          Preadditive.neg_comp, Preadditive.comp_neg, Linear.units_smul_comp,
          Linear.comp_units_smul]
        exact congrArg (fun k ↦ -(q.negOnePow • k)) hn.symm
      calc
        _ = T.map (coordinates R F q).hom ≫
            (T.map (ModuleCat.ofHom
              (-q.negOnePow • (F.d (-(q + 1)) (-q)).hom.dualMap)) ≫
                evaluation J R B α (F.X (-(q + 1)))) := by rw [Category.assoc, hs]
        _ = _ := by rw [← Category.assoc, ← T.map_comp, ← hd, T.map_comp, Category.assoc])
  refine ⟨κ, fun q ↦ HEq.rfl, ?_⟩
  intro κ' hκ'
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext q
  exact eq_of_heq (hκ' q)


/-- The cochain comparison is determined by the displayed signed degreewise evaluations.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization). -/
def comparison (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F) :=
  (comparison_existsUnique J R B α F P).exists.choose

/-- Scalar duality and the cochain comparison are contravariantly natural.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: precompose scalar cochains by f to construct g. The scalar coordinates identify
its components with the linear dual of f^(-q). The chain-map law follows from that of f.
For the comparison square, project to the unique nonzero Hom factor; both sides are
scalar evaluation precomposed with f^(-q), equal by evaluation_natural_isIso.
The invertible surviving projections give the equality of chain maps. -/
theorem comparison_natural
    (F G : CochainComplex (ModuleCat.{u} R) ℤ)
    (PF : ModuleCat.StrictPerfectCoefficientPackage F)
    (PG : ModuleCat.StrictPerfectCoefficientPackage G) (f : F ⟶ G) :
    ∃ g : dual R G ⟶ dual R F,
      (∀ q : ℤ, g.f q ≫ (coordinates R F q).hom =
        (coordinates R G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap) ∧
      ∀ q : ℤ,
        ((complexRealization J R B α).map g).f q ≫ (comparison J R B α F PF).hom.f q =
          (comparison J R B α G PG).hom.f q ≫
            SheafOfModules.homObjMap (R := B)
              (((complexRealization J R B α).map f).f (-q)) (𝟙 _) := by
  let g : dual R G ⟶ dual R F :=
    { f := fun q ↦ ModuleCat.ofHom
        { toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add q)
          map_add' := fun z w ↦ CochainComplex.HomComplex.Cochain.comp_add _ _ _ _
          map_smul' := fun r z ↦ CochainComplex.HomComplex.Cochain.comp_smul _ _ _ _ }
      comm' := by
        intro q r hqr
        apply ModuleCat.hom_ext
        ext z
        exact CochainComplex.HomComplex.δ_ofHom_comp f z r }
  have hg (q : ℤ) : g.f q ≫ (coordinates R F q).hom =
      (coordinates R G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap := by
    apply ModuleCat.hom_ext
    ext z x
    change ((coordinates R F q).hom (g.f q z)) x =
      ((coordinates R G q).hom z) ((f.f (-q)) x)
    dsimp only [coordinates]
    rw [(dual_coordinates R F).choose_spec.1 q,
      (dual_coordinates R G).choose_spec.1 q]
    dsimp only [g, ModuleCat.ofHom_apply]
    change (((CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add q)).v
      (-q) 0 _ ≫ _).hom x = _
    rw [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc]
    rfl
  refine ⟨g, hg, ?_⟩
  intro q
  have hF : (comparison J R B α F PF).hom.f q =
      (realization J R B α).map (coordinates R F q).hom ≫
        evaluation J R B α (F.X (-q)) :=
    eq_of_heq ((comparison_existsUnique J R B α F PF).exists.choose_spec q)
  have hG : (comparison J R B α G PG).hom.f q =
      (realization J R B α).map (coordinates R G q).hom ≫
        evaluation J R B α (G.X (-q)) :=
    eq_of_heq ((comparison_existsUnique J R B α G PG).exists.choose_spec q)
  change (realization J R B α).map (g.f q) ≫ _ = _
  rw [hF, hG, ← Category.assoc, ← Functor.map_comp, hg q, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun k ↦ (realization J R B α).map (coordinates R G q).hom ≫ k)
    ((evaluation_natural_isIso J R B α).1 (f.f (-q)))


/-- The signed, degreewise normalized comparison is an isomorphism to the recorded Hom complex.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: compose comparison with the inverse of homComplex_to_single_iso. That existing
isomorphism projects the Hom product to its only nonzero target factor (-q,0), and
identifies its differential with exactly the signedSheafDualComplex differential.
Thus this is the same degreewise evaluation isomorphism in the product-Hom presentation. -/
theorem ordinary_comparison
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (P : ModuleCat.StrictPerfectCoefficientPackage F) :
    Nonempty ((complexRealization J R B α).obj (dual R F) ≅
      homComplex (R := B) ((complexRealization J R B α).obj F) (unitComplex J B)) := by
  obtain ⟨e⟩ := homComplex_to_single_iso
    ((complexRealization J R B α).obj F)
    (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  exact ⟨(comparison J R B α F P) ≪≫ e.symm⟩


/-- Both ordinary dual complexes have the reversed degree bounds, including empty intervals.
Source: Stacks 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof: outside [-b,-a], the term F^(-q) is zero. Its scalar linear dual is zero;
the unique-factor description of both Hom complexes and C_B(0)=0 imply both vanish. -/
theorem dual_bounds (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)) :
    ∀ q : ℤ, q < -b ∨ -a < q →
      IsZero (((complexRealization J R B α).obj (dual R F)).X q) ∧
      IsZero ((homComplex (R := B) ((complexRealization J R B α).obj F)
        (unitComplex J B)).X q) := by
  intro q hq
  have hz : IsZero (F.X (-q)) := hbounded (-q) (by omega)
  have : Subsingleton (F.X (-q)) := ModuleCat.isZero_iff_subsingleton.mp hz
  have hdual : IsZero (ModuleCat.of R (Module.Dual R (F.X (-q)))) :=
    ModuleCat.isZero_of_subsingleton _
  have hc : IsZero ((dual R F).X q) := hdual.of_iso (coordinates R F q)
  have hr : IsZero (((complexRealization J R B α).obj (dual R F)).X q) :=
    (realization J R B α).map_isZero hc
  refine ⟨hr, ?_⟩
  obtain ⟨e⟩ := homComplex_to_single_iso
    ((complexRealization J R B α).obj F)
    (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  apply IsZero.of_iso _ ((HomologicalComplex.eval _ _ q).mapIso e)
  have he : IsZero (((complexRealization J R B α).obj F).X (-q)) :=
    (realization J R B α).map_isZero hz
  change IsZero (SheafOfModules.homObj (R := B)
    (((complexRealization J R B α).obj F).X (-q))
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := B)
    (M := ((complexRealization J R B α).obj F).X (-q))
    (N := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
    he.eq_of_src (𝟙 _) 0]
  apply SheafOfModules.hom_ext
  ext U φ : 3
  let N := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
  change (PresheafOfModules.restrictOver B.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver B.obj U.unop).map (𝟙 N : N ⟶ N).val = 0
  ext W x
  change ((φ.app W).hom) 0 = 0
  exact map_zero _


variable [HasDerivedCategory.{w} (Modules J B)]

/-- The realized scalar dual naturally represents derived internal Hom into B.
Source: Stacks 08JH, 08JJ (blueprint: lem-sfb-scalar-perfect-dual-realization).
Proof:
1. Use scalarPerfectDualRealization: for every K-injective resolution B[0]→I the ordinary
Hom comparison is a quasi-isomorphism. Its image under Q is an isomorphism.
2. The target computes the recorded derivedInternalHomOfUniverses, independently of
resolution. Use its comparison with the fixed functorial K-injective replacement.
3. Use ordinary_comparison to pass from the signed model to the product Hom model,
then compose its image under Q with the preceding isomorphism. Naturality of
the fixed resolution and comparison_natural give the displayed naturality square.
The scalar cochain-coordinate condition fixes g as precomposition by f.
There is no flatness condition on the scalar morphism to B. -/
theorem derived_comparison_natural :
    ∃ e : ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ)
        (P : ModuleCat.StrictPerfectCoefficientPackage F)
        (a b : ℤ) (hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)),
      DerivedCategory.Q.obj ((complexRealization J R B α).obj (dual R F)) ≅
        (derivedInternalHomOfUniverses.{u, u, u, w} J B).obj
          (op (DerivedCategory.Q.obj ((complexRealization J R B α).obj F)),
            DerivedCategory.Q.obj (unitComplex J B)),
      ∀ (F G : CochainComplex (ModuleCat.{u} R) ℤ)
        (PF : ModuleCat.StrictPerfectCoefficientPackage F)
        (PG : ModuleCat.StrictPerfectCoefficientPackage G)
        (a b c d : ℤ)
        (hF : ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
        (hG : ∀ q : ℤ, q < c ∨ d < q → IsZero (G.X q))
        (f : F ⟶ G) (g : dual R G ⟶ dual R F),
        (∀ q : ℤ, g.f q ≫ (coordinates R F q).hom =
          (coordinates R G q).hom ≫ ModuleCat.ofHom (f.f (-q)).hom.dualMap) →
        DerivedCategory.Q.map ((complexRealization J R B α).map g) ≫
            (e F PF a b hF).hom =
          (e G PG c d hG).hom ≫
            (derivedInternalHomOfUniverses.{u, u, u, w} J B).map
              ((DerivedCategory.Q.map ((complexRealization J R B α).map f)).op,
                𝟙 (DerivedCategory.Q.obj (unitComplex J B))) := by
  sorry

end CategoryTheory.ScalarPerfectDual
