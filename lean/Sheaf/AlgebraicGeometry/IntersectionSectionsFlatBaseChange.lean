/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.IntersectionStructureSections
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Adjunction.Limits

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
  sorry

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

/-- Pullback of section algebras along an isomorphism over the affine base.
Source: Stacks, Tag 0APJ naturality
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionOverIsoMap {R : CommRingCat.{u}} {Y Y' : Scheme.{u}}
    (f : Y ⟶ Spec R) (e : Y' ≅ Y) {I : Type v} {J : Type w}
    (U : I → Y.Opens) (V : J → Y'.Opens)
    (h : ∀ x : Y', (∀ j, x ∈ V j) ↔ ∀ i, e.hom x ∈ U i) :
    intersectionAlgebraSections f U ⟶ intersectionAlgebraSections (e.hom ≫ f) V := by
  letI : Algebra R (intersectionSections Y U) := (intersectionScalars f U).hom.toAlgebra
  letI : Algebra R (intersectionSections Y' V) :=
    (intersectionScalars (e.hom ≫ f) V).hom.toAlgebra
  exact CommAlgCat.ofHom
    { (intersectionSectionsMap e.hom U V (fun x hx ↦ (h x).mp hx)).hom with
      commutes' := fun a ↦ by
        change intersectionSectionsMap e.hom U V (fun x hx ↦ (h x).mp hx)
          (intersectionScalars f U a) = intersectionScalars (e.hom ≫ f) V a
        simpa using congrArg (fun k : R ⟶ intersectionSections Y' V ↦ k a)
          (intersectionScalars_map (𝟙 R) f (e.hom ≫ f) e.hom
            (by simp) U V (fun x hx ↦ (h x).mp hx)) }

/-- The canonical map of base-changed schemes induced by an isomorphism over the base.
Source: Stacks, Tag 0APJ naturality
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionBaseChangeIsoMap {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y Y' : Scheme.{u}} (f : Y ⟶ Spec R) (e : Y' ≅ Y) :
    pullback (e.hom ≫ f) (Spec.map r) ⟶ pullback f (Spec.map r) :=
  pullback.map (e.hom ≫ f) (Spec.map r) f (Spec.map r)
    e.hom (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- Pullback of sections under the canonical base-changed isomorphism, with arbitrary
presentations of the corresponding subsets. Source: Stacks, Tag 0APJ naturality
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionBaseChangeIsoSections {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y Y' : Scheme.{u}} (f : Y ⟶ Spec R) (e : Y' ≅ Y)
    {I : Type v} {J : Type w} (U : I → Y.Opens) (V : J → Y'.Opens)
    (h : ∀ x : Y', (∀ j, x ∈ V j) ↔ ∀ i, e.hom x ∈ U i) :
    intersectionSections (pullback f (Spec.map r))
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) ⟶
      intersectionSections (pullback (e.hom ≫ f) (Spec.map r))
        (fun j ↦ pullback.fst (e.hom ≫ f) (Spec.map r) ⁻¹ᵁ V j) :=
  intersectionSectionsMap (intersectionBaseChangeIsoMap r f e) _ _ (by
    intro x hx i
    have hi := (h (pullback.fst (e.hom ≫ f) (Spec.map r) x)).mp hx i
    change ((intersectionBaseChangeIsoMap r f e ≫ pullback.fst f (Spec.map r)) x) ∈ U i
    simpa only [intersectionBaseChangeIsoMap, pullback.lift_fst, Hom.comp_apply] using hi)

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

/-- The naturality square on all tensor elements, for isomorphisms carrying the indicated
subsets to one another. The families need not have the same indexing or the same opens.
Source: Stacks, Tag 0APJ canonical maps
(blueprint: lem-a1-intersection-sections-flat-base-change). -/
def intersectionBaseChangeNaturality {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) : Prop :=
  ∀ (Y' : Scheme.{u}) (e : Y' ≅ Y) (J : Type w) (V : J → Y'.Opens)
    (h : ∀ x : Y', (∀ j, x ∈ V j) ↔ ∀ i, e.hom x ∈ U i)
    (z : intersectionTensorSource r f U),
    intersectionBaseChangeIsoSections r f e U V h (intersectionBaseChangeMap r f U z) =
      intersectionBaseChangeMap r (e.hom ≫ f) V
        (intersectionScalarTensorMap r (intersectionOverIsoMap f e U V h) z)

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
3. These elementwise descriptions also prove the R-module colimit properties: compatible
   linear maps factor uniquely by representatives; eventual equality proves well-definedness.
   On each compact open apply `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
   (lem-weil-pbc-flat-base-change-global-sections-qcqs, Tag 02KH). Restriction commutes with
   pullback, so the stagewise isomorphisms form a diagram isomorphism. Tensor preserves
   colimits (lem-weil-pbc-tensor-commutes-with-colimits). Its colimit map is bijective and
   sends c tensor t to g-sharp(c) times t. Tensor-pushout uniqueness identifies it with
   `Algebra.TensorProduct.productMap`, hence with the defined T-algebra comparison.
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
  sorry

end AlgebraicGeometry
