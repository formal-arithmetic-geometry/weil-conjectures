/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntersectionStructureSections
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.QcOpenFlatSectionDiagram

/-!
# Flat affine base change on intersections of compact opens

Source: Stacks Project, More on Groupoids, Tag 0APJ, equation
`equation-sections-of-intersection`, and Cohomology of Schemes, Tag 02KH.
(blueprint: lem-a1-intersection-sections-flat-base-change)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
namespace Scheme

/-- The continuous map of indicated intersections induced by a scheme map; different
presentations of the subsets are allowed. Source: Stacks, Tag 0APJ canonical maps
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionSubsetMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    TopCat.of {x : X // ∀ j, x ∈ V j} ⟶ TopCat.of {y : Y // ∀ i, y ∈ U i} :=
  TopCat.ofHom ⟨fun x ↦ ⟨g x.val, h x.val x.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The comorphism on inverse-image sheaves is the adjoint of the scheme comorphism
followed by the inclusion's inverse-image unit. Source: Stacks, Tags 008F and 0APJ
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionSheafMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionStructureSheaf Y U ⟶
      (TopCat.Sheaf.pushforward CommRingCat (intersectionSubsetMap g U V h)).obj
        (intersectionStructureSheaf X V) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion Y U)).homEquiv _ _).symm
      ⟨g.c ≫ Functor.whiskerLeft (Opens.map g.base).op
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (intersectionInclusion X V)).unit.app X.sheaf).hom⟩

/-- Pullback of sections on the actual inverse-image structure sheaves, evaluated at the
full subspace. Source: Stacks, Tag 0APJ canonical maps
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionSectionsMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionSections Y U ⟶ intersectionSections X V :=
  (intersectionSheafMap g U V h).hom.app (op ⊤) ≫
    (intersectionStructureSheaf X V).obj.map (homOfLE (fun _ _ ↦ trivial)).op

/-- The scalar map obtained from the structure morphism and restriction to the subset.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionScalars {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    {I : Type v} (U : I → X.Opens) : R ⟶ intersectionSections X U :=
  (ΓSpecIso R).inv ≫ f.appTop ≫ intersectionRestriction X U ⊤ (fun _ _ ↦ trivial)

/-- The sections endowed with the algebra structure from the structure morphism.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionAlgebraSections {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) {I : Type v} (U : I → X.Opens) : CommAlgCat.{u} R :=
  letI := (intersectionScalars f U).hom.toAlgebra
  CommAlgCat.of R (intersectionSections X U)

private theorem intersectionSheafMap_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) (W : Y.Opens) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (intersectionInclusion Y U)).unit.app Y.sheaf).hom.app (op W) ≫
        (intersectionSheafMap g U V h).hom.app
          (op ((Opens.map (intersectionInclusion Y U)).obj W)) =
      g.app W ≫ ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (intersectionInclusion X V)).unit.app X.sheaf).hom.app (op (g ⁻¹ᵁ W)) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion Y U)
  have he := (adj.homEquiv _ _).apply_symm_apply
    (show Y.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat (intersectionInclusion Y U)).obj
        ((TopCat.Sheaf.pushforward CommRingCat (intersectionSubsetMap g U V h)).obj
          (intersectionStructureSheaf X V)) from
      ⟨g.c ≫ Functor.whiskerLeft (Opens.map g.base).op
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (intersectionInclusion X V)).unit.app X.sheaf).hom⟩)
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun k ↦ k.hom.app (op W)) he

attribute [local irreducible] intersectionSheafMap

set_option backward.isDefEq.respectTransparency false in
private theorem intersectionRestriction_top_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionRestriction Y U ⊤ (fun _ _ ↦ trivial) ≫
        intersectionSectionsMap g U V h =
      g.appTop ≫ intersectionRestriction X V ⊤ (fun _ _ ↦ trivial) := by
  simp only [intersectionRestriction, intersectionSectionsMap, Opens.map_top,
    homOfLE_refl, op_id]
  erw [(intersectionStructureSheaf Y U).obj.map_id,
    (intersectionStructureSheaf X V).obj.map_id]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  exact intersectionSheafMap_unit g U V h ⊤

private theorem intersectionSectionsMap_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionSectionsMap g U V h = (intersectionSheafMap g U V h).hom.app (op ⊤) := by
  unfold intersectionSectionsMap
  change _ ≫ (intersectionStructureSheaf X V).obj.map (𝟙 (op ⊤)) = _
  erw [(intersectionStructureSheaf X V).obj.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem intersectionSectionsMap_comp {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) {I : Type v} {J : Type w} {K : Type*}
    (U : I → Z.Opens) (V : J → Y.Opens) (W : K → X.Opens)
    (hf : ∀ y : Y, (∀ j, y ∈ V j) → ∀ i, f y ∈ U i)
    (hg : ∀ x : X, (∀ k, x ∈ W k) → ∀ j, g x ∈ V j) :
    intersectionSectionsMap f U V hf ≫ intersectionSectionsMap g V W hg =
      intersectionSectionsMap (g ≫ f) U W (fun x hx ↦ hf (g x) (hg x hx)) := by
  have hs : intersectionSheafMap f U V hf ≫
      (TopCat.Sheaf.pushforward CommRingCat (intersectionSubsetMap f U V hf)).map
        (intersectionSheafMap g V W hg) =
      intersectionSheafMap (g ≫ f) U W (fun x hx ↦ hf (g x) (hg x hx)) := by
    apply (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
      (intersectionInclusion Z U)).homEquiv _ _ |>.injective
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    change
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (intersectionInclusion Z U)).unit.app Z.sheaf).hom.app O ≫
          ((intersectionSheafMap f U V hf).hom.app _ ≫
            (intersectionSheafMap g V W hg).hom.app _) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (intersectionInclusion Z U)).unit.app Z.sheaf).hom.app O ≫
            (intersectionSheafMap (g ≫ f) U W _).hom.app _
    erw [← Category.assoc, intersectionSheafMap_unit f U V hf O.unop,
      Category.assoc, intersectionSheafMap_unit g V W hg (f ⁻¹ᵁ O.unop),
      intersectionSheafMap_unit (g ≫ f) U W _ O.unop]
    exact (Category.assoc _ _ _).symm
  rw [intersectionSectionsMap_eq, intersectionSectionsMap_eq,
    intersectionSectionsMap_eq]
  exact congrArg (fun k ↦ k.hom.app (op ⊤)) hs

set_option backward.isDefEq.respectTransparency false in
private theorem intersectionRestriction_res (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) {V W : X.Opens} (hWV : W ≤ V)
    (hW : ∀ x : X, (∀ i, x ∈ U i) → x ∈ W) :
    X.presheaf.map (homOfLE hWV).op ≫ intersectionRestriction X U W hW =
      intersectionRestriction X U V (fun x hx ↦ hWV (hW x hx)) := by
  unfold intersectionRestriction
  rw [← Category.assoc]
  erw [((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion X U)).unit.app X.sheaf).hom.naturality]
  rw [Category.assoc]
  congr 1
  change (intersectionStructureSheaf X U).obj.map _ ≫
    (intersectionStructureSheaf X U).obj.map _ = _
  rw [← Functor.map_comp]
  congr 1

private theorem intersectionSectionsMap_id (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) :
    intersectionSectionsMap (𝟙 X) U U (fun _ hx ↦ hx) = 𝟙 _ := by
  have hs : intersectionSheafMap (𝟙 X) U U (fun _ hx ↦ hx) =
      (𝟙 (intersectionStructureSheaf X U)) := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
      (intersectionInclusion X U)).homEquiv _ _).injective
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext O
    change
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (intersectionInclusion X U)).unit.app X.sheaf).hom.app O ≫
          (intersectionSheafMap (𝟙 X) U U _).hom.app _ = _ ≫ 𝟙 _
    erw [intersectionSheafMap_unit]
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    rfl
  rw [intersectionSectionsMap_eq, hs]
  rfl

private theorem intersectionSectionsMap_reindex {X : Scheme.{u}}
    {I : Type v} {J : Type w} (U : I → X.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ i, x ∈ U i) ↔ ∀ j, x ∈ V j) :
    Function.Bijective
      (intersectionSectionsMap (𝟙 X) U V (fun x hx ↦ (h x).mpr hx)) := by
  let a := intersectionSectionsMap (𝟙 X) U V (fun x hx ↦ (h x).mpr hx)
  let b := intersectionSectionsMap (𝟙 X) V U (fun x hx ↦ (h x).mp hx)
  have hab : a ≫ b = 𝟙 _ := by
    dsimp [a, b]
    rw [intersectionSectionsMap_comp]
    change intersectionSectionsMap (𝟙 X) U U _ = _
    exact intersectionSectionsMap_id X U
  have hba : b ≫ a = 𝟙 _ := by
    dsimp [a, b]
    rw [intersectionSectionsMap_comp]
    change intersectionSectionsMap (𝟙 X) V V _ = _
    exact intersectionSectionsMap_id X V
  exact ⟨Function.HasLeftInverse.injective
    ⟨b, fun x ↦ congrArg (fun k : intersectionSections X U ⟶ _ ↦ k x) hab⟩,
    Function.HasRightInverse.surjective
    ⟨b, fun x ↦ congrArg (fun k : intersectionSections X V ⟶ _ ↦ k x) hba⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem intersectionRestriction_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i)
    (O : Y.Opens) (hO : ∀ y : Y, (∀ i, y ∈ U i) → y ∈ O) :
    intersectionRestriction Y U O hO ≫ intersectionSectionsMap g U V h =
      g.app O ≫ intersectionRestriction X V (g ⁻¹ᵁ O)
        (fun x hx ↦ hO (g x) (h x hx)) := by
  rw [intersectionSectionsMap_eq]
  unfold intersectionRestriction
  rw [Category.assoc]
  erw [(intersectionSheafMap g U V h).hom.naturality]
  erw [← Category.assoc, intersectionSheafMap_unit]
  simp only [Category.assoc]
  rfl

/-- Compatibility of pullback and scalar restriction in a commutative square.
Source: Stacks, Tag 0APJ canonical maps
(blueprint: lem-a1-intersection-sections-flat-base-change).
Proof: functoriality of the scheme comorphism identifies the two maps on global sections
using the commutative square and naturality of `ΓSpecIso`. Naturality of the inclusion's
inverse-image unit then gives the equality after restriction to the subspaces. -/
theorem intersectionScalars_map {R T : CommRingCat.{u}} (r : R ⟶ T)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec R) (q : X ⟶ Spec T) (g : X ⟶ Y)
    (comm : g ≫ f = q ≫ Spec.map r) {I : Type v} {J : Type w}
    (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionScalars f U ≫ intersectionSectionsMap g U V h =
      r ≫ intersectionScalars q V := by
  unfold intersectionScalars
  rw [Category.assoc, Category.assoc, intersectionRestriction_top_map]
  rw [← Category.assoc f.appTop, ← Hom.comp_appTop, comm, Hom.comp_appTop]
  simp only [Category.assoc]
  rw [← ΓSpecIso_inv_naturality_assoc]


private theorem intersectionScalars_map_apply {R T : CommRingCat.{u}} (r : R ⟶ T)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec R) (q : X ⟶ Spec T) (g : X ⟶ Y)
    (comm : g ≫ f = q ≫ Spec.map r) {I : Type v} {J : Type w}
    (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) (a : R) :
    intersectionSectionsMap g U V h (intersectionScalars f U a) =
      intersectionScalars q V (r a) :=
  congrArg (fun k : R ⟶ intersectionSections X V ↦ k a)
    (intersectionScalars_map r f q g comm U V h)

private def intersectionRestrictionAlgebra {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) {I : Type v} (U : I → X.Opens) (O : X.Opens)
    (hO : ∀ x : X, (∀ i, x ∈ U i) → x ∈ O) :
    qcOpenSectionAlgebra f O ⟶ intersectionAlgebraSections f U := by
  let : Algebra R (intersectionSections X U) := (intersectionScalars f U).hom.toAlgebra
  exact CommAlgCat.ofHom
    (X := qcOpenSectionAlgebra f O) (Y := intersectionAlgebraSections f U)
    { (intersectionRestriction X U O hO).hom with
      commutes' := fun a ↦ by
        change (X.presheaf.map (homOfLE le_top).op ≫
          intersectionRestriction X U O hO)
            (((ΓSpecIso R).inv ≫ f.appTop) a) =
          intersectionRestriction X U ⊤ (fun _ _ ↦ trivial)
            (((ΓSpecIso R).inv ≫ f.appTop) a)
        rw [intersectionRestriction_res] }

/-- Extension of the section algebra's scalars, using the right tensor factor.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionScalarTensor {R T : CommRingCat.{u}} (r : R ⟶ T)
    (C : CommAlgCat.{u} R) : CommAlgCat.{u} T :=
  letI := r.hom.toAlgebra
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := T)
  CommAlgCat.of T (C ⊗[R] T)

/-- The tensor source of the comparison, retaining the actual section ring.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionTensorSource {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    CommAlgCat.{u} T :=
  intersectionScalarTensor r (intersectionAlgebraSections f U)

/-- The canonical T-algebra map, constructed by `Algebra.TensorProduct.productMap` from
pullback of sections and the scalar map. It is defined for every commutative square, so
its naturality and iteration make sense without choices of inverse isomorphisms.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionTensorMap {R T : CommRingCat.{u}} (r : R ⟶ T)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec R) (q : X ⟶ Spec T) (g : X ⟶ Y)
    (comm : g ≫ f = q ≫ Spec.map r) {I : Type v} {J : Type w}
    (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    intersectionTensorSource r f U ⟶ intersectionAlgebraSections q V := by
  letI := r.hom.toAlgebra
  let C := intersectionAlgebraSections f U
  let D := intersectionAlgebraSections q V
  letI : Algebra R (intersectionSections Y U) := (intersectionScalars f U).hom.toAlgebra
  letI : Algebra T (intersectionSections X V) := (intersectionScalars q V).hom.toAlgebra
  letI : Algebra R D := (r ≫ intersectionScalars q V).hom.toAlgebra
  let a : C →ₐ[R] D :=
    { (intersectionSectionsMap g U V h).hom with
      commutes' := fun x ↦ congrArg (fun k : R ⟶ intersectionSections X V ↦ k x)
        (intersectionScalars_map r f q g comm U V h) }
  let b : T →ₐ[R] D :=
    { (intersectionScalars q V).hom with commutes' := fun _ ↦ rfl }
  let m := Algebra.TensorProduct.productMap a b
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := T)
  exact CommAlgCat.ofHom
    { m.toRingHom with
      commutes' := fun t ↦ Algebra.TensorProduct.productMap_right_apply a b t }

/-- Pure tensors in scalar-extended section algebras.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionScalarTensorPure {R T : CommRingCat.{u}} (r : R ⟶ T)
    (C : CommAlgCat.{u} R) (c : C) (t : T) : intersectionScalarTensor r C :=
  letI := r.hom.toAlgebra
  c ⊗ₜ[R] t

/-- Tensoring a map of section algebras with the identity of the new scalar ring.
Source: Stacks, Tag 0APJ naturality
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionScalarTensorMap {R T : CommRingCat.{u}} (r : R ⟶ T)
    {C D : CommAlgCat.{u} R} (a : C ⟶ D) :
    intersectionScalarTensor r C ⟶ intersectionScalarTensor r D := by
  letI := r.hom.toAlgebra
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := T)
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := D) (B := T)
  let m := Algebra.TensorProduct.map a.hom (AlgHom.id R T)
  exact CommAlgCat.ofHom
    { m.toRingHom with
      commutes' := by
        intro t
        change m (1 ⊗ₜ[R] t) = 1 ⊗ₜ[R] t
        simp [m] }

/-- Associativity and the tensor unit identify successive extension with direct extension.
This is the usual tensor associator and unitor, expressed using commutation and
`cancelBaseChange` to accommodate the right-factor algebra structures.
Source: Stacks, Tag 0APJ iterated compatibility
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionTensorAssociator {R T S : CommRingCat.{u}} (r : R ⟶ T) (s : T ⟶ S)
    (C : CommAlgCat.{u} R) :
    intersectionScalarTensor s (intersectionScalarTensor r C) ≃+*
      intersectionScalarTensor (r ≫ s) C := by
  letI := r.hom.toAlgebra
  letI := s.hom.toAlgebra
  letI : Algebra R S := (r ≫ s).hom.toAlgebra
  letI : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := T)
  exact (Algebra.TensorProduct.comm T (C ⊗[R] T) S).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S))
      (Algebra.TensorProduct.commRight R T C).symm).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange R T S S C).toRingEquiv.trans
        (Algebra.TensorProduct.comm R S C).toRingEquiv))

/-- The specified comparison for the chosen scheme pullback.
Source: Stacks, Tag 0APJ (blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionBaseChangeMap {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    intersectionTensorSource r f U ⟶
      intersectionAlgebraSections (pullback.snd f (Spec.map r))
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) :=
  intersectionTensorMap r f (pullback.snd f (Spec.map r))
    (pullback.fst f (Spec.map r)) pullback.condition U _ (fun _ hx ↦ hx)

/-- The canonical pasting map from the iterated scheme pullback to the direct pullback.
Source: Stacks, Tag 0APJ iterated compatibility
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionIteratedProjection {R T S : CommRingCat.{u}} (r : R ⟶ T) (s : T ⟶ S)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) :
    pullback (pullback.snd f (Spec.map r)) (Spec.map s) ⟶
      pullback f (Spec.map (r ≫ s)) :=
  pullback.lift
    (pullback.fst (pullback.snd f (Spec.map r)) (Spec.map s) ≫
      pullback.fst f (Spec.map r))
    (pullback.snd (pullback.snd f (Spec.map r)) (Spec.map s)) (by
      simp only [Category.assoc, pullback.condition, Spec.map_comp]
      rw [← Category.assoc, pullback.condition, Category.assoc])

/-- The induced canonical pullback on sections under iterated scheme base change.
Source: Stacks, Tag 0APJ iterated compatibility
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionIteratedSections {R T S : CommRingCat.{u}} (r : R ⟶ T) (s : T ⟶ S)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    intersectionSections (pullback f (Spec.map (r ≫ s)))
        (fun i ↦ pullback.fst f (Spec.map (r ≫ s)) ⁻¹ᵁ U i) ⟶
      intersectionSections (pullback (pullback.snd f (Spec.map r)) (Spec.map s))
        (fun i ↦ pullback.fst (pullback.snd f (Spec.map r)) (Spec.map s) ⁻¹ᵁ
          (pullback.fst f (Spec.map r) ⁻¹ᵁ U i)) :=
  intersectionSectionsMap (intersectionIteratedProjection r s f) _ _ (by
    intro x hx i
    change ((intersectionIteratedProjection r s f ≫
      pullback.fst f (Spec.map (r ≫ s))) x) ∈ U i
    simpa only [intersectionIteratedProjection, pullback.lift_fst, Hom.comp_apply,
      Hom.mem_preimage] using hx i)

/-- Compatibility of direct and successive flat affine base change on all tensor
positions, together with the explicit pure-triple-tensor formula for the associator.
Source: Stacks, Tag 0APJ canonical maps and tensor-pushout uniqueness
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionBaseChangeIteration {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) : Prop :=
  ∀ (S : CommRingCat.{u}) (s : T ⟶ S), Flat (Spec.map s) →
    (∀ (c : intersectionAlgebraSections f U) (t : T) (a : S),
      intersectionTensorAssociator r s (intersectionAlgebraSections f U)
        (intersectionScalarTensorPure s (intersectionTensorSource r f U)
          (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c t) a) =
        intersectionScalarTensorPure (r ≫ s) (intersectionAlgebraSections f U)
          c (s t * a)) ∧
    (∀ z : intersectionScalarTensor s (intersectionTensorSource r f U),
      intersectionIteratedSections r s f U
          (intersectionBaseChangeMap (r ≫ s) f U
            (intersectionTensorAssociator r s (intersectionAlgebraSections f U) z)) =
        intersectionBaseChangeMap s (pullback.snd f (Spec.map r))
          (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)
          (intersectionScalarTensorMap s (intersectionBaseChangeMap r f U) z))

private theorem intersectionTensorMap_pure {R T : CommRingCat.{u}} (r : R ⟶ T)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec R) (q : X ⟶ Spec T) (g : X ⟶ Y)
    (comm : g ≫ f = q ≫ Spec.map r) {I : Type v} {J : Type w}
    (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i)
    (c : intersectionAlgebraSections f U) (t : T) :
    intersectionTensorMap r f q g comm U V h
        (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c t) =
      intersectionSectionsMap g U V h c * intersectionScalars q V t := rfl

private theorem intersectionTensorAssociator_pure {R T S : CommRingCat.{u}}
    (r : R ⟶ T) (s : T ⟶ S) (C : CommAlgCat.{u} R) (c : C) (t : T) (a : S) :
    intersectionTensorAssociator r s C
        (intersectionScalarTensorPure s (intersectionScalarTensor r C)
          (intersectionScalarTensorPure r C c t) a) =
      intersectionScalarTensorPure (r ≫ s) C c (s t * a) := by
  let := r.hom.toAlgebra
  let := s.hom.toAlgebra
  let : Algebra R S := (r ≫ s).hom.toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := T)
  change (Algebra.TensorProduct.comm R S C)
    ((Algebra.TensorProduct.cancelBaseChange R T S S C)
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S))
        (Algebra.TensorProduct.commRight R T C).symm)
          ((Algebra.TensorProduct.comm T (C ⊗[R] T) S)
            ((c ⊗ₜ[R] t) ⊗ₜ[T] a)))) = c ⊗ₜ[R] (s t * a)
  rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  change (Algebra.TensorProduct.comm R S C)
    ((Algebra.TensorProduct.cancelBaseChange R T S S C)
      (a ⊗ₜ[T] (t ⊗ₜ[R] c))) = c ⊗ₜ[R] (s t * a)
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.comm_tmul]
  rfl

attribute [local irreducible] intersectionStructureSheaf intersectionInclusion

private theorem intersectionBaseChangeIteration_proof {R T : CommRingCat.{u}}
    (r : R ⟶ T) {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v}
    (U : I → Y.Opens) : intersectionBaseChangeIteration r f U := by
  intro S s _
  refine ⟨intersectionTensorAssociator_pure r s _, ?_⟩
  intro z
  let := r.hom.toAlgebra
  let := s.hom.toAlgebra
  let : Algebra R S := (r ≫ s).hom.toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let := Algebra.TensorProduct.rightAlgebra
    (R := R) (A := intersectionAlgebraSections f U) (B := T)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ct a =>
    induction ct using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | tmul c t =>
      change intersectionIteratedSections r s f U
          (intersectionBaseChangeMap (r ≫ s) f U
            (intersectionTensorAssociator r s (intersectionAlgebraSections f U)
              (intersectionScalarTensorPure s (intersectionTensorSource r f U)
                (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c t) a))) = _
      erw [intersectionTensorAssociator_pure]
      change intersectionIteratedSections r s f U
          (intersectionSectionsMap (pullback.fst f (Spec.map (r ≫ s))) U _ _ c *
            intersectionScalars (pullback.snd f (Spec.map (r ≫ s))) _ (s t * a)) =
        intersectionBaseChangeMap s (pullback.snd f (Spec.map r)) _
          (intersectionScalarTensorPure s _
            (intersectionBaseChangeMap r f U
              (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c t)) a)
      rw [intersectionBaseChangeMap, intersectionTensorMap_pure, map_mul,
        intersectionBaseChangeMap, intersectionTensorMap_pure, map_mul, map_mul]
      rw [map_mul]
      let UT := fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i
      have hc : intersectionIteratedSections r s f U
          (intersectionSectionsMap (pullback.fst f (Spec.map (r ≫ s))) U _ (fun _ hx ↦ hx) c) =
        intersectionSectionsMap
          (pullback.fst (pullback.snd f (Spec.map r)) (Spec.map s)) UT _ (fun _ hx ↦ hx)
          (intersectionSectionsMap (pullback.fst f (Spec.map r)) U UT
            (fun _ hx ↦ hx) c) := by
        change (intersectionSectionsMap (pullback.fst f (Spec.map (r ≫ s))) U _ _ ≫
          intersectionSectionsMap (intersectionIteratedProjection r s f) _ _ _) c =
            (intersectionSectionsMap (pullback.fst f (Spec.map r)) U _ _ ≫
              intersectionSectionsMap
                (pullback.fst (pullback.snd f (Spec.map r)) (Spec.map s)) _ _ _) c
        rw [intersectionSectionsMap_comp, intersectionSectionsMap_comp]
        congr 2
        simp [intersectionIteratedProjection]
      have hs (a : S) : intersectionIteratedSections r s f U
          (intersectionScalars (pullback.snd f (Spec.map (r ≫ s))) _ a) =
        intersectionScalars (pullback.snd (pullback.snd f (Spec.map r)) (Spec.map s))
          _ a := by
        exact congrArg (fun k : S ⟶ _ ↦ k a)
          (intersectionScalars_map (𝟙 S) (pullback.snd f (Spec.map (r ≫ s)))
            (pullback.snd (pullback.snd f (Spec.map r)) (Spec.map s))
            (intersectionIteratedProjection r s f) (by simp [intersectionIteratedProjection])
            _ _ _)
      have ht := intersectionScalars_map_apply s (pullback.snd f (Spec.map r))
        (pullback.snd (pullback.snd f (Spec.map r)) (Spec.map s))
        (pullback.fst (pullback.snd f (Spec.map r)) (Spec.map s))
        pullback.condition UT
        (fun i ↦ pullback.fst (pullback.snd f (Spec.map r)) (Spec.map s) ⁻¹ᵁ UT i)
        (fun _ hx ↦ hx) t
      rw [hc, hs, hs, ht, mul_assoc]
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem qcFiniteIntersection_mem {X : Scheme.{u}} {I : Type v}
    (U : I → X.Opens) (F : {F : Finset I // F.Nonempty}) (x : X) :
    x ∈ qcFiniteIntersection U F ↔ ∀ i ∈ F.val, x ∈ U i := by
  change x ∈ (qcFiniteIntersection U F : Set X) ↔ _
  rw [qcFiniteIntersection, TopologicalSpace.Opens.coe_iInf]
  simp

private theorem qcFiniteIntersection_all {X : Scheme.{u}} {I : Type v}
    (U : I → X.Opens) (x : X) :
    (∀ i, x ∈ U i) ↔ ∀ F : {F : Finset I // F.Nonempty}, x ∈ qcFiniteIntersection U F := by
  classical
  constructor
  · intro hx F
    exact (qcFiniteIntersection_mem U F x).mpr fun i _ ↦ hx i
  · intro hx i
    exact (qcFiniteIntersection_mem U ⟨{i}, by simp⟩ x).mp (hx ⟨{i}, by simp⟩) i
      (by simp)

private theorem intersectionSectionPresentation (X : Scheme.{u})
    [QuasiSeparatedSpace X] {I : Type v} {J : Type w} [Nonempty J]
    (U : I → X.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ i, x ∈ U i) ↔ ∀ j, x ∈ V j)
    (hqc : ∀ j, IsCompact (V j : Set X))
    (hdir : ∀ i j : J, ∃ k, V k ≤ V i ⊓ V j) :
    (∀ c : intersectionSections X U, ∃ (j : J) (x : Γ(X, V j)),
      intersectionRestriction X U (V j) (fun x hx ↦ (h x).mp hx j) x = c) ∧
    (∀ (j : J) (x y : Γ(X, V j)),
      intersectionRestriction X U (V j) (fun x hx ↦ (h x).mp hx j) x =
        intersectionRestriction X U (V j) (fun x hx ↦ (h x).mp hx j) y →
      ∃ (k : J) (hki : V k ≤ V j),
        X.presheaf.map (homOfLE hki).op x = X.presheaf.map (homOfLE hki).op y) := by
  let a := intersectionSectionsMap (𝟙 X) U V (fun x hx ↦ (h x).mpr hx)
  have ha := (intersectionSectionsMap_reindex U V h).1
  have comm (j : J) :
      intersectionRestriction X U (V j) (fun x hx ↦ (h x).mp hx j) ≫ a =
        intersectionRestriction X V (V j) (fun x hx ↦ hx j) := by
    exact (intersectionRestriction_map (𝟙 X) U V _ (V j) _).trans (by
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      rfl)
  obtain ⟨hsurj, heq, _⟩ := sections_intersection_structure_colimit X V hqc hdir
  constructor
  · intro c
    obtain ⟨j, x, hx⟩ := hsurj (a c)
    refine ⟨j, x, ha ?_⟩
    change a (intersectionRestriction X U (V j) _ x) = a c
    rw [← CommRingCat.comp_apply, comm, hx]
  · intro j x y hxy
    obtain ⟨k, hk, he⟩ := heq j x y (by
      rw [← comm]
      change a (intersectionRestriction X U (V j) _ x) =
        a (intersectionRestriction X U (V j) _ y)
      rw [hxy])
    exact ⟨k, hk, he⟩

private theorem directedTensor_bijective {R T : Type u} [CommRing R] [CommRing T]
    [Algebra R T] {J : Type v} [Preorder J] [Nonempty J]
    (hdir : ∀ i j : J, ∃ k, i ≤ k ∧ j ≤ k)
    (A : J → CommAlgCat.{u} R) (B : J → CommAlgCat.{u} T)
    (C : CommAlgCat.{u} R) (D : CommAlgCat.{u} T)
    (rho : ∀ i, A i →ₐ[R] C) (sigma : ∀ i, B i →ₐ[T] D)
    (ar : ∀ i j, i ≤ j → A i →ₐ[R] A j)
    (br : ∀ i j, i ≤ j → B i →ₐ[T] B j)
    (hrho : ∀ (i j : J) (h : i ≤ j) x, rho j (ar i j h x) = rho i x)
    (hrho_surj : ∀ c : C, ∃ i x, rho i x = c)
    (hsigma_surj : ∀ d : D, ∃ i x, sigma i x = d)
    (hsigma_eq : ∀ (i : J) (x : B i), sigma i x = 0 →
      ∃ (j : J) (h : i ≤ j), br i j h x = 0)
    (phi : ∀ i, (A i ⊗[R] T) →+* B i)
    (hphi : ∀ i, Function.Bijective (phi i))
    (hphi_nat : ∀ (i j : J) (h : i ≤ j) z,
      phi j (Algebra.TensorProduct.map (ar i j h) (AlgHom.id R T) z) =
        br i j h (phi i z))
    (m : (C ⊗[R] T) →+* D)
    (hm : ∀ i z, m (Algebra.TensorProduct.map (rho i) (AlgHom.id R T) z) =
      sigma i (phi i z)) : Function.Bijective m := by
  classical
  let leg (i : J) := Algebra.TensorProduct.map (rho i) (AlgHom.id R T)
  have leg_nat (i j : J) (h : i ≤ j) (z : A i ⊗[R] T) :
      leg j (Algebra.TensorProduct.map (ar i j h) (AlgHom.id R T) z) = leg i z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x t => simp only [leg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hrho]
    | add x y hx hy => simp only [map_add, hx, hy]
  have reps (z : C ⊗[R] T) : ∃ (i : J) (x : A i ⊗[R] T), leg i x = z := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨Classical.choice ‹Nonempty J›, 0, map_zero _⟩
    | tmul c t =>
      obtain ⟨i, x, rfl⟩ := hrho_surj c
      exact ⟨i, x ⊗ₜ[R] t, rfl⟩
    | add z w hz hw =>
      obtain ⟨i, x, rfl⟩ := hz
      obtain ⟨j, y, rfl⟩ := hw
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, Algebra.TensorProduct.map (ar i k hik) (AlgHom.id R T) x +
        Algebra.TensorProduct.map (ar j k hjk) (AlgHom.id R T) y, ?_⟩
      rw [map_add, leg_nat, leg_nat]
  refine ⟨?_, ?_⟩
  · intro z w hzw
    have hz : m (z - w) = 0 := by rw [map_sub, hzw, sub_self]
    obtain ⟨i, x, hx⟩ := reps (z - w)
    have hi : sigma i (phi i x) = 0 := by rw [← hx, hm] at hz; exact hz
    obtain ⟨j, hij, hj⟩ := hsigma_eq i (phi i x) hi
    have hj' : Algebra.TensorProduct.map (ar i j hij) (AlgHom.id R T) x = 0 := by
      apply (hphi j).1
      rw [hphi_nat, hj, map_zero]
    have : z - w = 0 := by rw [← hx, ← leg_nat i j hij x, hj', map_zero]
    exact sub_eq_zero.mp this
  · intro d
    obtain ⟨i, b, rfl⟩ := hsigma_surj d
    obtain ⟨x, hx⟩ := (hphi i).2 b
    exact ⟨leg i x, by rw [hm, hx]⟩

private theorem intersectionBaseChange_bijective {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) [QuasiSeparatedSpace Y] [Flat (Spec.map r)]
    {I : Type v} (U : I → Y.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set Y)) :
    Function.Bijective (intersectionBaseChangeMap r f U) := by
  classical
  let := hI
  let := r.hom.toAlgebra
  let J := {F : Finset I // F.Nonempty}
  let V := qcFiniteIntersection U
  let g := pullback.fst f (Spec.map r)
  let q := pullback.snd f (Spec.map r)
  let W := fun F : J ↦ g ⁻¹ᵁ V F
  let UT := fun i ↦ g ⁻¹ᵁ U i
  obtain ⟨hne, _hdir, hqs, hcomp, e, he, henat⟩ := qc_open_flat_section_diagram r f U hqc
  let : Nonempty J := hne
  let : QuasiSeparatedSpace (pullback f (Spec.map r) : Scheme) := hqs
  have hV (x : Y) : (∀ i, x ∈ U i) ↔ ∀ F : J, x ∈ V F :=
    qcFiniteIntersection_all U x
  have hW (x : (pullback f (Spec.map r) : Scheme)) :
      (∀ i, x ∈ UT i) ↔ ∀ F : J, x ∈ W F := hV (g x)
  have hJ (F G : J) : ∃ H : J, F ≤ H ∧ G ≤ H := by
    refine ⟨⟨F.val ∪ G.val, F.property.mono Finset.subset_union_left⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩
  have hVdir (F G : J) : ∃ H : J, V H ≤ V F ⊓ V G := by
    obtain ⟨H, hF, hG⟩ := hJ F G
    exact ⟨H, le_inf (leOfHom (qcFiniteIntersectionInclusion U hF))
      (leOfHom (qcFiniteIntersectionInclusion U hG))⟩
  have hWdir (F G : J) : ∃ H : J, W H ≤ W F ⊓ W G := by
    obtain ⟨H, hH⟩ := hVdir F G
    exact ⟨H, fun x hx ↦ hH hx⟩
  obtain ⟨hCsurj, _hCeq⟩ := intersectionSectionPresentation Y U V hV
    (fun F ↦ (hcomp F).1) hVdir
  obtain ⟨hDsurj, hDeq⟩ := intersectionSectionPresentation _ UT W hW
    (fun F ↦ (hcomp F).2.2.1) hWdir
  let rho (F : J) := intersectionRestrictionAlgebra f U (V F)
    (fun x hx ↦ (hV x).mp hx F)
  let sigma (F : J) := intersectionRestrictionAlgebra q UT (W F)
    (fun x hx ↦ (hW x).mp hx F)
  let ar (F G : J) (h : F ≤ G) :=
    qcOpenSectionRestriction f (qcFiniteIntersectionInclusion U h)
  let br (F G : J) (h : F ≤ G) :=
    qcOpenSectionRestriction q
      ((Opens.map g.base).map (qcFiniteIntersectionInclusion U h))
  apply directedTensor_bijective hJ
    (fun F ↦ qcOpenSectionAlgebra f (V F)) (fun F ↦ qcOpenSectionAlgebra q (W F))
    (intersectionAlgebraSections f U) (intersectionAlgebraSections q UT)
    (fun F ↦ (rho F).hom) (fun F ↦ (sigma F).hom)
    (fun F G h ↦ (ar F G h).hom) (fun F G h ↦ (br F G h).hom)
    (phi := fun F ↦ (e F).hom.hom.toRingHom)
    (m := (intersectionBaseChangeMap r f U).hom.toRingHom)
  · intro F G h x
    exact congrArg (fun k : Γ(Y, V F) ⟶ intersectionSections Y U ↦ k x)
      (intersectionRestriction_res Y U (leOfHom (qcFiniteIntersectionInclusion U h))
        (fun y hy ↦ (hV y).mp hy G))
  · exact hCsurj
  · exact hDsurj
  · intro F x hx
    have hx' : intersectionRestriction _ UT (W F) _ x = 0 := hx
    obtain ⟨K, hK, hk⟩ := hDeq F x 0 (by simpa only [map_zero] using hx')
    obtain ⟨G, hFG, hKG⟩ := hJ F K
    refine ⟨G, hFG, ?_⟩
    have hk' := congrArg
      (fun z ↦ (pullback f (Spec.map r)).presheaf.map
        ((Opens.map g.base).map (qcFiniteIntersectionInclusion U hKG)).op z) hk
    change (pullback f (Spec.map r)).presheaf.map _ x = 0
    rw [map_zero] at hk'
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at hk'
    rw [map_zero] at hk'
    convert hk' using 1
    congr 2
  · intro F
    exact ⟨fun x y h ↦ by
      change (e F).hom x = (e F).hom y at h
      have := congrArg (fun z ↦ (e F).inv z) h
      simpa only [CommAlgCat.inv_hom_apply] using this,
      fun y ↦ ⟨(e F).inv y, CommAlgCat.hom_inv_apply _ _⟩⟩
  · intro F G h z
    exact congrArg (fun k ↦ k.hom z) (henat F G h)
  · intro F z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x t =>
      change intersectionBaseChangeMap r f U
        (intersectionScalarTensorPure r (intersectionAlgebraSections f U)
          (rho F x) t) = sigma F ((e F).hom (qcOpenSectionPure r f (V F) x t))
      rw [intersectionBaseChangeMap, intersectionTensorMap_pure, he, map_mul]
      congr 1
      · exact congrArg (fun k : Γ(Y, V F) ⟶ intersectionSections _ UT ↦ k x)
          (intersectionRestriction_map g U UT (fun _ hx ↦ hx) (V F)
            (fun y hy ↦ (hV y).mp hy F))
      · exact (sigma F).hom.commutes t |>.symm
    | add x y hx hy => simp only [map_add, hx, hy]

end Scheme

/-- Flat affine base change for sections of the inverse-image structure sheaf on an
intersection of any nonempty family of quasi-compact opens. The actual T-algebra map is
bijective, has the canonical pure-tensor formula, is natural for isomorphisms carrying
the subsets, and commutes with iterated base change and the tensor associator.

Source: Stacks Project, More on Groupoids, Tag 0APJ and
`equation-sections-of-intersection`; Cohomology of Schemes, Tag 02KH.
(blueprint: lem-a1-intersection-sections-flat-base-change).

Proof, following the node's four steps:
1. Replace the family by all nonempty finite intersections. Quasi-separatedness makes
   these compact; the new family is directed by reverse inclusion and has the same
   intersection. Inverse image commutes with intersections. The pullback projection is
   affine, so inverse images of these compact opens are compact.
2. Apply `Scheme.sections_intersection_structure_colimit` to both schemes and their
   refined families. The second scheme is quasi-separated because it is affine over Y.
   Its surjectivity and eventual-equality clauses identify the two section rings with
   the corresponding filtered colimits, including empty intersections and zero rings.
3. Tensor induction and directedness show that every tensor comes from a finite stage.
   The stagewise comparisons of `qc_open_flat_section_diagram` commute with restriction.
   Target representatives and stagewise surjectivity give surjectivity. A tensor in the
   kernel is represented at one stage; eventual equality makes its image vanish at a
   later stage. Stagewise injectivity makes that restricted tensor zero, proving
   injectivity. This uses no module-colimit construction or colimit-preservation theorem.
4. Scheme isomorphisms commute with inclusion units, restriction and pullback; tensor
   functoriality gives the naturality square. For a second flat affine base change,
   both composites on a pure triple tensor give the pullback of c times the two scalars.
   The tensor associator sends (c tensor t) tensor a to c tensor (s(t) times a).
   Pure tensors generate each tensor product, so the equations hold for every element.
   Functoriality of pullback identifies the targets via the canonical pasting map. -/
theorem flat_affine_intersection_sections_base_change
    {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R)
    [QuasiSeparatedSpace Y] [Flat (Spec.map r)]
    {I : Type v} (U : I → Y.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set Y)) :
    Function.Bijective (Scheme.intersectionBaseChangeMap r f U) ∧
    (∀ (c : Scheme.intersectionAlgebraSections f U) (t : T),
      Scheme.intersectionBaseChangeMap r f U
          (Scheme.intersectionScalarTensorPure r (Scheme.intersectionAlgebraSections f U) c t) =
        Scheme.intersectionSectionsMap (pullback.fst f (Spec.map r)) U
            (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) (fun _ hx ↦ hx) c *
          Scheme.intersectionScalars (pullback.snd f (Spec.map r))
            (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) t) ∧
    Scheme.intersectionBaseChangeNaturality.{u, v, w} r f U ∧
    Scheme.intersectionBaseChangeIteration r f U := by
  exact ⟨Scheme.intersectionBaseChange_bijective r f U hI hqc,
    Scheme.intersectionTensorMap_pure r f _ _ pullback.condition U _ (fun _ hx ↦ hx),
    Scheme.intersectionBaseChangeNaturality_proof r f U,
    Scheme.intersectionBaseChangeIteration_proof r f U⟩

end AlgebraicGeometry
