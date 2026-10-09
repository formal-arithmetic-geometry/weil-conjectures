/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Galois.Equivalence
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.CategoryTheory.Galois.IsFundamentalgroup

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCategory
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
étale `Y`-schemes is essentially small
(`CategoryTheory.PreGaloisCategory.exists_isFundamentalGroup`), and it is unique up to a unique
isomorphism compatible with the actions
(`CategoryTheory.PreGaloisCategory.toAutContinuousMulEquiv`).

The Galois category axioms for finite étale schemes (blueprint `lem-fet-galois-category`) are
recorded without proof here.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

namespace FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

variable (Y) in
/-- Blueprint `lem-fet-galois-category`: The finite etale category is a Galois category.

The finite étale `Y`-schemes form a pre-Galois category: they have a terminal object,
fibre products, finite coproducts and quotients by finite groups, and a monomorphism is the
inclusion of a direct summand. -/
theorem preGaloisCategory : PreGaloisCategory Y.FiniteEtale where
  hasQuotientsByFiniteGroups G _ _ := hasColimitsOfShape_singleObj Y G
  monoInducesIsoOnDirectSummand i _ := monoInducesIsoOnDirectSummand i

attribute [instance] preGaloisCategory

/-- Blueprint `lem-fet-galois-category`: The finite etale category is a Galois category.

For connected `Y` the geometric fibre at a geometric point is a fibre functor on the
finite étale `Y`-schemes. -/
theorem fiberFunctor [ConnectedSpace Y] : FiberFunctor (fiber s) where
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f _ ↦ isIso_of_isIso_fiber_map s f⟩

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
affine and of finite type, and the `Y`-schemes affine and locally of finite type over `Y` form an
essentially small family
(`AlgebraicGeometry.Scheme.Over.small_skeleton_isAffineHomLocallyOfFiniteType`). -/
theorem essentiallySmall : EssentiallySmall.{u} Y.FiniteEtale := by
  let Q := Scheme.Over.isAffineHomLocallyOfFiniteType (Y := Y)
  have hQ (P : Y.FiniteEtale) : Q ((MorphismProperty.Over.forget _ _ _).obj P.obj) := by
    have : IsFinite P.obj.hom := P.property
    exact ⟨inferInstanceAs (IsAffineHom P.obj.hom), inferInstanceAs (LocallyOfFiniteType P.obj.hom)⟩
  let g : Skeleton Y.FiniteEtale → Skeleton Q.FullSubcategory := fun x ↦
    toSkeleton ⟨(MorphismProperty.Over.forget _ _ _).obj (Quotient.out x).obj, hQ _⟩
  have hg : Function.Injective g := fun x y hxy ↦ by
    obtain ⟨e⟩ := Quotient.exact hxy
    rw [← Quotient.out_eq x, ← Quotient.out_eq y]
    exact Quotient.sound ⟨ObjectProperty.isoMk _
      (MorphismProperty.Over.isoMk ((CategoryTheory.Over.forget Y).mapIso
        ((ObjectProperty.ι _).mapIso e)) (Over.w e.hom.hom))⟩
  have := Scheme.Over.small_skeleton_isAffineHomLocallyOfFiniteType (Y := Y)
  exact (essentiallySmall_iff _).2 ⟨small_of_injective hg, ⟨fun _ _ ↦ inferInstance⟩⟩

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
  have := essentiallySmall Y
  exact PreGaloisCategory.exists_isFundamentalGroup (fiber s)

/-- A finite étale `Y`-scheme `P` over a connected scheme with an action of `M` by
`Y`-automorphisms which is simply transitive on the geometric fibre at `s` is an `M`-torsor:
the morphism `∐_{m ∈ M} P ⟶ P ×_Y P` is a morphism of finite étale `Y`-schemes inducing a
bijection on geometric fibres, hence an isomorphism, as the fibre functor is conservative. -/
lemma isIso_sigmaDesc_of_existsUnique {M : Type (u + 1)} [Finite M]
    (P : Y.FiniteEtale) (v : M → (P ⟶ P))
    (hv : ∀ x y : (fiber s).obj P, ∃! m, (fiber s).map (v m) x = y) :
    IsIso (Sigma.desc fun m : M ↦ pullback.lift (f := P.obj.hom) (g := P.obj.hom)
      (v m).hom.left (𝟙 P.obj.left) (by rw [Category.id_comp]; exact hom_left_comp (v m))) := by
  sorry

/-- Blueprint `rem-ptr-galois-object-2`: Pointer to the properties of [def-galois-object].

The Galois covers of `Y` — the connected finite étale `P ⟶ Y` on whose geometric fibre `P_s`
the automorphism group `Aut_Y(P)` acts simply transitively — are exactly the Galois objects of
the Galois category of finite étale `Y`-schemes. -/
theorem isGalois_iff (P : Y.FiniteEtale) :
    IsGalois P ↔ IsConnected P ∧
      ∀ x : (fiber s).obj P, Function.Bijective fun σ : Aut P ↦ (fiber s).map σ.hom x := by
  refine ⟨fun _ ↦ ⟨inferInstance, evaluation_aut_bijective_of_isGalois (fiber s) P⟩,
    fun ⟨_, h⟩ ↦ (isGalois_iff_pretransitive (fiber s) P).mpr ⟨fun x y ↦ (h x).2 y⟩⟩

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- Blueprint `thm-galois-fundamental`: The fibre functor is an equivalence.

For a connected scheme `Y` with geometric point `s` and a fundamental group `G` of the fibre
functor, the fibre functor induces an equivalence between finite étale `Y`-schemes and finite
sets with a continuous `G`-action. -/
noncomputable def equivalenceContAction : Y.FiniteEtale ≌ ContAction FintypeCat.{u} G :=
  (functorToContAction (fiber s)).asEquivalence.trans
    (ContAction.resEquiv _ (toAutContinuousMulEquiv (fiber s) G))

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
