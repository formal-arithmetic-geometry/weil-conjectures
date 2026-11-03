/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.RankOne
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Topology.LocallyConstantMapsPresheaf
public import WeilConjectures.CategoryTheory.Sites.PointConstantSheafMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# Automorphisms of the constant finite trace line

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
 sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1, sentence identifying the
translation action on the trace line with multiplication by a locally constant unit
(blueprint: lem-pur-constant-trace-line-automorphism-unit).

The scalar is a section of the constant sheaf of units, represented by a
`LocallyConstant` function through `AlgebraicGeometry.constantSheaf_sections_locallyConstant`.
The multiplication automorphism is characterized stalkwise, so the definition does not
choose an unrelated endomorphism.  Pullback is composition with the underlying continuous
map of the scheme morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Etale

/-- The constant finite trace line on the small étale site of `X`.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
 sk-prop-sp-orientation-vector-bundle.proof.md`, Step 1
(blueprint: lem-pur-constant-trace-line-automorphism-unit). -/
abbrev constantTraceLine (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- Pull a locally constant unit-valued function back along a scheme morphism.

Source: the pullback clause of the constant trace-line statement, using the inverse-image
construction of `prop-weil-pbc-inverse-image-modules-exact` (blueprint:
lem-pur-constant-trace-line-automorphism-unit). -/
def pullbackConstantTraceUnit {X Y : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (f : Y ⟶ X) (u : LocallyConstant X Aˣ) : LocallyConstant Y Aˣ :=
  LocallyConstant.comap (ContinuousMap.mk f.base.hom f.base.hom.continuous) u

/-- Stalkwise meaning of multiplication by a locally constant unit.

The scalar is evaluated at every point of every geometric test scheme.  The stalk map is
therefore multiplication by the corresponding element of `A`; this also covers empty and
disconnected schemes without a connectedness assumption.

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), and the
constant rank-one calculation in the cited blueprint proof (blueprint:
lem-pur-constant-trace-line-automorphism-unit). -/
def constantTraceLineScalarCorresponds (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (u : LocallyConstant X Aˣ) (e : (End (constantTraceLine X A))ˣ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (x : Spec (.of Ω)),
    (Scheme.pointSmallEtale s).sheafFiber.map e.val =
      ((u (s.base.hom x) : A) • 𝟙
        ((Scheme.pointSmallEtale s).sheafFiber.obj (constantTraceLine X A)))

private def lcPresheaf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A where
  obj V := ModuleCat.of A (LocallyConstant V.unop.left A)
  map f := ModuleCat.ofHom (LocallyConstant.comapₗ A
    ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id _ := by ext s x; rfl
  map_comp _ _ := by ext s x; rfl

private theorem lcPresheaf_isSheaf (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsSheaf X.smallEtaleTopology (lcPresheaf X A) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  apply Presheaf.isSheaf_of_isSheaf_comp X.smallEtaleTopology (lcPresheaf X A)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let e : lcPresheaf X A ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ≅
      (Scheme.Etale.continuousMapSheaf X A).obj :=
    NatIso.ofComponents (fun V ↦ AddEquiv.toAddCommGrpIso
      { toFun := LocallyConstant.toContinuousMap
        invFun := fun t ↦
          let t₀ : C(V.unop.left, A) := t
          ⟨t₀, (IsLocallyConstant.iff_continuous _).2 t₀.continuous⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }) (by intros; rfl)
  exact (Presheaf.isSheaf_of_iso_iff e).2 (Scheme.Etale.continuousMapSheaf X A).property

private def lcConst (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A) ⟶ lcPresheaf X A where
  app V := ModuleCat.ofHom
    { toFun := LocallyConstant.const V.unop.left
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality _ _ _ := rfl

private instance lcConst_surjective (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (lcConst X A) where
  imageSieve_mem {V} s₀ := by
    let s : LocallyConstant V.left A := s₀
    let F (a : A) : V.left.Opens := ⟨{x | s x = a}, s.isLocallyConstant.isOpen_fiber a⟩
    let W (a : A) : X.Etale := Scheme.Etale.mk ((F a).ι ≫ V.hom)
    let ι (a : A) : W a ⟶ V := MorphismProperty.Over.homMk (F a).ι rfl
    refine X.smallEtaleTopology.superset_covering ?_
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨a⟩
      refine ⟨a, LocallyConstant.ext fun x ↦ ?_⟩
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

private instance lcConst_injective (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (lcConst X A) where
  equalizerSieve_mem {V} a b h := by
    by_cases hab : a = b
    · subst hab
      exact X.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (X.smallEtaleTopology.top_mem _)
    · have : IsEmpty V.unop.left := ⟨fun x ↦ hab (congrArg
        (fun f : LocallyConstant V.unop.left A ↦ f x) h)⟩
      refine X.smallEtaleTopology.superset_covering ?_
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := V.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

private def lcComparison (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    constantTraceLine X A ⟶ ⟨lcPresheaf X A, lcPresheaf_isSheaf X A⟩ :=
  ⟨sheafifyLift _ (lcConst X A) (lcPresheaf_isSheaf X A)⟩

private instance lcComparison_isIso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    IsIso (lcComparison X A) := by
  refine (Sheaf.isLocallyBijective_iff_isIso (lcComparison X A)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify X.smallEtaleTopology _)]
    change Presheaf.IsLocallyInjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify X.smallEtaleTopology _)]
    change Presheaf.IsLocallySurjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance

private def lcEval {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (x : Spec (.of Ω)) :
    (Scheme.pointSmallEtale s).presheafFiber.obj (lcPresheaf X A) ⟶ ModuleCat.of A A :=
  (Scheme.pointSmallEtale s).presheafFiberDesc
    (fun V t ↦ ModuleCat.ofHom
      { toFun := fun f ↦ f (t.left x)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }) (by intros; rfl)

private theorem lcEval_germ {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (x : Spec (.of Ω))
    (V : X.Etale) (t : (Scheme.pointSmallEtale s).fiber.obj V) :
    (Scheme.pointSmallEtale s).toPresheafFiber V t (lcPresheaf X A) ≫ lcEval s x =
      ModuleCat.ofHom
        { toFun := fun f ↦ f (t.left x)
          map_add' := by intros; rfl
          map_smul' := by intros; rfl } := by
  exact (Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberDesc _ _ V t

private theorem lcEval_comparison {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (x : Spec (.of Ω)) :
    (Scheme.pointSmallEtale s).sheafFiber.map (lcComparison X A) ≫ lcEval s x =
      ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)).hom := by
  let Φ := Scheme.pointSmallEtale s
  apply (cancel_epi (Φ.presheafFiber.map (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))))).1
  change Φ.presheafFiber.map _ ≫ Φ.presheafFiber.map
    (sheafifyLift _ (lcConst X A) (lcPresheaf_isSheaf X A)) ≫ _ = _
  rw [← Functor.map_comp_assoc, toSheafify_sheafifyLift]
  dsimp only [GrothendieckTopology.Point.sheafFiberConstantSheafIso,
    Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [IsIso.hom_inv_id_assoc]
  apply Φ.presheafFiber_hom_ext
  intro V t
  rw [Φ.toPresheafFiber_naturality_assoc, lcEval_germ,
    Φ.toPresheafFiber_presheafFiberConstIso_hom]
  rfl

private def scalarEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    End (constantTraceLine X A) ≃ LocallyConstant X A :=
  ((Iso.refl _).homCongr (asIso (lcComparison X A))).trans
    (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)).homEquiv _ _).trans
      (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf A A _).toEquiv))

private theorem scalarEquiv_stalk (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (g : End (constantTraceLine X A))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (x : Spec (.of Ω)) :
    (Scheme.pointSmallEtale s).sheafFiber.map g =
      scalarEquiv X A g (s x) • 𝟙 _ := by
  let Φ := Scheme.pointSmallEtale s
  let i := Φ.sheafFiberConstantSheafIso (ModuleCat.of A A)
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let t : Φ.fiber.obj T := Over.homMk s (Category.comp_id s)
  have hi := Φ.sheafFiberConstantSheafIso_inv_comp_sheafFiber_map hT t
    (ModuleCat.of A A) ⟨lcPresheaf X A, lcPresheaf_isSheaf X A⟩
    (g ≫ lcComparison X A)
  have hcmp := lcEval_comparison (A := A) s x
  have hi' : i.inv ≫ Φ.sheafFiber.map g ≫ i.hom =
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A) hT).homEquiv _ _
        (g ≫ lcComparison X A)) ≫ Φ.toPresheafFiber T t (lcPresheaf X A) ≫ lcEval s x := by
    rw [← hcmp, ← Functor.map_comp_assoc, reassoc_of% hi]
  apply (cancel_epi i.inv).1
  apply (cancel_mono i.hom).1
  rw [Category.assoc, hi', lcEval_germ]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [Functor.flip_obj_obj, ObjectProperty.ι_obj, Over.mk_left,
    Scheme.Etale.forget_obj_left, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
    LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    Linear.comp_smul, Linear.smul_comp, Category.assoc, ModuleCat.hom_smul,
    LinearMap.smul_apply, smul_eq_mul]
  change scalarEquiv X A g (s x) =
    scalarEquiv X A g (s x) * i.hom (i.inv (1 : A))
  rw [Iso.inv_hom_id_apply, mul_one]

private theorem scalarEquiv_mul (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (g h : End (constantTraceLine X A)) :
    scalarEquiv X A (g * h) = scalarEquiv X A g * scalarEquiv X A h := by
  apply LocallyConstant.ext
  intro x
  let s := X.algClosurePoint x
  have hg := scalarEquiv_stalk X A g _ s default
  have hh := scalarEquiv_stalk X A h _ s default
  have hgh := scalarEquiv_stalk X A (g * h) _ s default
  rw [End.mul_def, Functor.map_comp, hg, hh, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, smul_smul] at hgh
  have he := congrArg (fun g ↦
    ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)).inv ≫
      g ≫ ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso (ModuleCat.of A A)).hom) hgh
  have he' := congrArg (fun g ↦ g (1 : A)) he
  simpa [s, Linear.comp_smul, Linear.smul_comp, mul_comm] using he'.symm

private def scalarMulEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    End (constantTraceLine X A) ≃* LocallyConstant X A where
  __ := scalarEquiv X A
  map_mul' := scalarEquiv_mul X A

private def lcUnitEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (LocallyConstant X A)ˣ ≃ LocallyConstant X Aˣ where
  toFun a :=
    ⟨fun x ↦ ⟨a.val x, a.inv x, congrArg (fun f : LocallyConstant X A ↦ f x) a.val_inv,
        congrArg (fun f : LocallyConstant X A ↦ f x) a.inv_val⟩,
      IsLocallyConstant.desc _ Units.val a.val.isLocallyConstant Units.val_injective⟩
  invFun a :=
    { val := a.map Units.val
      inv := a.map (fun x ↦ (x⁻¹ : Aˣ).val)
      val_inv := by ext x; exact (a x).val_inv
      inv_val := by ext x; exact (a x).inv_val }
  left_inv a := by apply Units.ext; rfl
  right_inv a := by ext x; rfl

private def unitScalarEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (End (constantTraceLine X A))ˣ ≃ LocallyConstant X Aˣ :=
  (Units.mapEquiv (scalarMulEquiv X A)).toEquiv.trans (lcUnitEquiv X A)

private theorem unitScalarEquiv_val (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (e : (End (constantTraceLine X A))ˣ) (x : X) :
    (unitScalarEquiv X A e x : A) = scalarEquiv X A e.val x := rfl

/-- Existence and uniqueness of multiplication by a locally constant unit.

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), together with
`MonoidalCategory.unitsUnitEndMulEquivAut` for the constant rank-one line
(blueprint: lem-pur-constant-trace-line-automorphism-unit).
-/
theorem constantTraceLine_multiplication_exists (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (u : LocallyConstant X Aˣ) :
    ∃! e : (End (constantTraceLine X A))ˣ,
      constantTraceLineScalarCorresponds X A u e := by
  have hc (e : (End (constantTraceLine X A))ˣ) :
      constantTraceLineScalarCorresponds X A u e ↔ unitScalarEquiv X A e = u := by
    constructor
    · intro h
      apply LocallyConstant.ext
      intro x
      apply Units.val_injective
      have he := scalarEquiv_stalk X A e.val _ (X.algClosurePoint x) default
      have hu := h _ (X.algClosurePoint x) default
      have hh := he.symm.trans hu
      let i := (Scheme.pointSmallEtale (X.algClosurePoint x)).sheafFiberConstantSheafIso
        (ModuleCat.of A A)
      have h' := congrArg (fun g ↦ i.inv ≫ g ≫ i.hom) hh
      have h'' := congrArg (fun g ↦ g (1 : A)) h'
      simpa [i, Linear.comp_smul, Linear.smul_comp, unitScalarEquiv_val] using h''
    · intro h Ω _ _ s x
      have he := scalarEquiv_stalk X A e.val Ω s x
      rw [← unitScalarEquiv_val, h] at he
      exact he
  refine ⟨(unitScalarEquiv X A).symm u, (hc _).2 (Equiv.apply_symm_apply _ _), ?_⟩
  intro e he
  exact (unitScalarEquiv X A).injective ((hc e).1 he |>.trans
    (Equiv.apply_symm_apply _ _).symm)

end AlgebraicGeometry.Etale
