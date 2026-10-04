/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# The étale fundamental group of a connected scheme

Let `Y` be a scheme and `s : Spec Ω ⟶ Y` a geometric point, `Ω` a separably closed field.
The finite étale `Y`-schemes form the category `AlgebraicGeometry.Scheme.FiniteEtale Y`, a full
subcategory of the small étale site `Y.Etale`, and taking the geometric fibre at `s`,
i.e. the `Y`-morphisms `Spec Ω ⟶ P`, is the fibre functor
`AlgebraicGeometry.Scheme.FiniteEtale.fiber s` to finite sets. For connected `Y` this is a
Galois category with fibre functor, and the étale fundamental group `π₁(Y, s)` is the
automorphism group of the fibre functor, a profinite group; Mathlib's Galois theory
(`CategoryTheory.PreGaloisCategory`) then shows that the fibre functor is an equivalence onto
finite sets with a continuous `π₁(Y, s)`-action.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale`: the category of finite étale `Y`-schemes.
- `AlgebraicGeometry.Scheme.FiniteEtale.fiber`: the fibre functor at a geometric point.
- `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction`: for any fundamental group `G`
  of the fibre functor, the equivalence between finite étale `Y`-schemes and finite discrete
  `G`-sets.

## Main statements

- `AlgebraicGeometry.Scheme.FiniteEtale.fiberFunctor`: for connected `Y` the finite étale
  `Y`-schemes form a Galois category with fibre functor the geometric fibre.
- `AlgebraicGeometry.Scheme.FiniteEtale.exists_isFundamentalGroup`: the fibre functor has a
  fundamental group in the universe of `Y`, a profinite group.

## Implementation notes

The fundamental group `Aut (fiber s)` itself lives one universe above `Y`, as the category of
finite étale `Y`-schemes does. The étale fundamental group used elsewhere is therefore any
profinite group `G : ProfiniteGrp.{u}` together with a fundamental group structure
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup (fiber s) G`; such a `G` exists, by
`AlgebraicGeometry.Scheme.FiniteEtale.exists_isFundamentalGroup`, since the category of finite
étale `Y`-schemes is essentially small, and it is unique up to a unique isomorphism compatible
with the actions (`CategoryTheory.PreGaloisCategory.toAutMulEquiv`).

The Galois category axioms for finite étale schemes (blueprint `lem-fet-galois-category`), the
finiteness of geometric fibres and the essential smallness are recorded as separate lemmas
without proof here.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u})

/-- Blueprint `def-galois-fibre-functor`: The fibre functor.

The category `FÉt(Y)` of finite étale `Y`-schemes, as a full subcategory of the small étale
site of `Y`. -/
protected abbrev FiniteEtale : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun P : Y.Etale ↦ IsFinite P.hom

namespace FiniteEtale

variable {Y} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The geometric fibre of a finite étale `Y`-scheme at a geometric point is finite. -/
lemma finite_fiber (P : Y.FiniteEtale) : Finite ((pointSmallEtale s).fiber.obj P.obj) := by
  sorry

/-- Blueprint `def-galois-fibre-functor`: The fibre functor.

The fibre functor `F_s : FÉt(Y) ⥤ FintypeCat` at a geometric point `s : Spec Ω ⟶ Y`, sending a
finite étale `P ⟶ Y` to the finite set of `Y`-morphisms `Spec Ω ⟶ P`. -/
noncomputable def fiber : Y.FiniteEtale ⥤ FintypeCat.{u} :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (pointSmallEtale s).fiber) (finite_fiber s)

@[simp]
lemma fiber_obj_obj (P : Y.FiniteEtale) :
    ((fiber s).obj P).obj = (pointSmallEtale s).fiber.obj P.obj := rfl

lemma fiber_map_apply {P Q : Y.FiniteEtale} (f : P ⟶ Q) (x : (fiber s).obj P) :
    (fiber s).map f x = (pointSmallEtale s).fiber.map f.hom x := rfl

variable (Y) in
/-- Blueprint `lem-fet-galois-category`: The finite etale category is a Galois category.

The finite étale `Y`-schemes form a pre-Galois category: they have a terminal object,
fibre products, finite coproducts and quotients by finite groups, and a monomorphism is the
inclusion of a direct summand. -/
theorem preGaloisCategory : PreGaloisCategory Y.FiniteEtale := by
  sorry

attribute [instance] preGaloisCategory

/-- Blueprint `lem-fet-galois-category`: The finite etale category is a Galois category.

For connected `Y` the geometric fibre at a geometric point is a fibre functor on the
finite étale `Y`-schemes. -/
theorem fiberFunctor [ConnectedSpace Y] : FiberFunctor (fiber s) := by
  sorry

attribute [instance] fiberFunctor

variable (Y) in
/-- Blueprint `lem-fet-galois-category`: The finite etale category is a Galois category.

For connected `Y` the finite étale `Y`-schemes form a Galois category: a geometric point
`Spec κ(y)^alg ⟶ Y` at any point `y` gives a fibre functor. -/
theorem galoisCategory [ConnectedSpace Y] : GaloisCategory Y.FiniteEtale := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  exact ⟨⟨_, ⟨fiberFunctor (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
    (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y)⟩⟩⟩

attribute [instance] galoisCategory

variable (Y) in
/-- The finite étale `Y`-schemes form an essentially small category: finite morphisms are
affine, so a finite étale `Y`-scheme is determined by a quasi-coherent `𝒪_Y`-algebra. -/
theorem essentiallySmall : EssentiallySmall.{u} Y.FiniteEtale := by
  sorry

/-- The automorphism group of the fibre functor is small: an automorphism is determined by
its components on a small model of `FÉt(Y)`. -/
lemma small_aut : Small.{u} (Aut (fiber s)) := by
  have := essentiallySmall Y
  let e := equivSmallModel.{u} Y.FiniteEtale
  let φ : Aut (fiber s) → ∀ X : SmallModel.{u} Y.FiniteEtale,
      Aut ((fiber s).obj (e.inverse.obj X)) := fun σ X ↦ σ.app _
  refine small_of_injective (f := φ) fun σ τ h ↦ ?_
  refine Iso.ext (NatTrans.ext (funext fun P ↦ ?_))
  have hP := congr_arg (fun ρ ↦ (ρ (e.functor.obj P)).hom) h
  rw [← cancel_mono ((fiber s).map (e.unitIso.hom.app P)), ← NatTrans.naturality,
    ← NatTrans.naturality]
  exact congrArg ((fiber s).map (e.unitIso.hom.app P) ≫ ·) hP

section FundamentalGroup

variable [ConnectedSpace Y]

open scoped FintypeCatDiscrete

/-- Blueprint `lem-galois-aut-profinite`: Aut of fibre functor is profinite.

The fibre functor at a geometric point of a connected scheme has a fundamental group in the
universe of the scheme: a profinite group `G` acting naturally and continuously on the
geometric fibres, transitively on those of Galois objects, and faithfully. This `G` is the
étale fundamental group `π₁(Y, s)`, unique up to unique isomorphism. -/
theorem exists_isFundamentalGroup :
    ∃ (G : ProfiniteGrp.{u}) (_ : ∀ P, MulAction G ((fiber s).obj P)),
      IsFundamentalGroup (fiber s) G := by
  have := small_aut s
  let A := Aut (fiber s)
  let e : Shrink.{u} A ≃* A := Shrink.mulEquiv
  let _ : TopologicalSpace (Shrink.{u} A) := .induced e inferInstance
  let h : Shrink.{u} A ≃ₜ A := e.toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩
  let f : Shrink.{u} A ≃ₜ* A :=
    { toMulEquiv := e, continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }
  have : IsTopologicalGroup (Shrink.{u} A) :=
    { continuous_mul := by
        rw [h.isInducing.continuous_iff]
        have : (fun p : Shrink.{u} A × Shrink.{u} A ↦ e (p.1 * p.2)) =
            fun p ↦ e p.1 * e p.2 := funext fun p ↦ map_mul e _ _
        change Continuous fun p : Shrink.{u} A × Shrink.{u} A ↦ e (p.1 * p.2)
        rw [this]
        exact (h.continuous.comp continuous_fst).mul (h.continuous.comp continuous_snd)
      continuous_inv := by
        rw [h.isInducing.continuous_iff]
        have : (fun p : Shrink.{u} A ↦ e p⁻¹) = fun p ↦ (e p)⁻¹ := funext fun p ↦ map_inv e _
        change Continuous fun p : Shrink.{u} A ↦ e p⁻¹
        rw [this]
        exact h.continuous.inv }
  let G := ProfiniteGrp.ofContinuousMulEquiv (G := ProfiniteGrp.of A) f.symm
  let _ (P : Y.FiniteEtale) : MulAction G ((fiber s).obj P) :=
    MulAction.compHom _ (e : Shrink.{u} A →* A)
  refine ⟨G, inferInstance, ?_⟩
  have hsmul (g : G) (P : Y.FiniteEtale) (x : (fiber s).obj P) : g • x = e g • x := rfl
  exact
    { naturality g _ _ f x := by
        simp only [hsmul]
        exact IsNaturalSMul.naturality (e g) f x
      transitive_of_isGalois P _ := by
        refine ⟨fun x y ↦ ?_⟩
        obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq A x y
        refine ⟨e.symm σ, ?_⟩
        change e (e.symm σ) • x = y
        rwa [MulEquiv.apply_symm_apply]
      continuous_smul P := by
        refine ⟨?_⟩
        change Continuous fun p : G × (fiber s).obj P ↦ e p.1 • p.2
        have : Continuous fun p : G × (fiber s).obj P ↦ (e p.1, p.2) :=
          (h.continuous.comp continuous_fst).prodMk continuous_snd
        exact (continuousSMul_aut_fiber (fiber s) P).continuous_smul.comp this
      non_trivial' g hg := by
        have := IsFundamentalGroup.non_trivial (F := fiber s) (e g) fun P x ↦ hg P x
        exact e.injective (this.trans (map_one e).symm) }

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- The isomorphism of topological groups between a fundamental group `G` of the fibre
functor and the automorphism group of the fibre functor. -/
noncomputable def toAutContinuousMulEquiv : G ≃ₜ* Aut (fiber s) :=
  { toAutMulEquiv (fiber s) G with
    continuous_toFun := (toAutMulEquiv_isHomeomorph (fiber s) G).continuous
    continuous_invFun := (toAutMulEquiv_isHomeomorph (fiber s) G).homeomorph.symm.continuous }

/-- Blueprint `thm-galois-fundamental`: The fibre functor is an equivalence.

For a connected scheme `Y` with geometric point `s` and a fundamental group `G` of the fibre
functor, the fibre functor induces an equivalence between finite étale `Y`-schemes and finite
sets with a continuous `G`-action. -/
noncomputable def equivalenceContAction : Y.FiniteEtale ≌ ContAction FintypeCat.{u} G :=
  (functorToContAction (fiber s)).asEquivalence.trans
    (ContAction.resEquiv _ (toAutContinuousMulEquiv s G))

/-- Blueprint `thm-galois-fundamental`: The fibre functor is an equivalence.

The underlying finite set of the `G`-set attached to a finite étale `Y`-scheme `P` is its
geometric fibre. -/
@[simp]
lemma equivalenceContAction_functor_obj_obj_V (P : Y.FiniteEtale) :
    ((equivalenceContAction s G).functor.obj P).obj.V = (fiber s).obj P := rfl

/-- Blueprint `thm-galois-fundamental`: The fibre functor is an equivalence.

The action of `G` on the `G`-set attached to a finite étale `Y`-scheme `P` is the given action
of `G` on the geometric fibre of `P`. -/
lemma equivalenceContAction_functor_obj_obj_ρ_apply (P : Y.FiniteEtale) (g : G)
    (x : (fiber s).obj P) :
    (((equivalenceContAction s G).functor.obj P).obj.ρ g).hom x = g • x := rfl

/-- Blueprint `thm-galois-fundamental`: The fibre functor is an equivalence.

The map of `G`-sets attached to a morphism of finite étale `Y`-schemes is the induced map on
geometric fibres. -/
lemma equivalenceContAction_functor_map_hom_hom {P Q : Y.FiniteEtale} (f : P ⟶ Q) :
    ((equivalenceContAction s G).functor.map f).hom.hom = (fiber s).map f := rfl

end FundamentalGroup

end FiniteEtale

end AlgebraicGeometry.Scheme
