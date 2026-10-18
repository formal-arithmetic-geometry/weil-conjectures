/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q61
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.RepresentationTheory.DiscreteIntegerInvariantsInfrastructure
import Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable
import Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.Algebra.Category.Grp.AB

/-!
# Continuous cochains compute Galois cohomology

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-base-field-cd,
sk-lem-base-field-cd-cochains, clauses (1)--(3), and its proof; Stacks Project,
Tags 04JP, 04JR, 010T and 00DB (blueprint: det-base-field-cd-cochains).

Locally constant functions are exactly continuous functions into the discrete coefficient
group. An equivalent abelian category `A` permits any presentation of the category of
discrete integer representations. Coordinate equations specify all maps uniquely.
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- The invariants functor in an equivalent presentation of discrete integer modules.
This is the restriction of `Rep.invariantsFunctor`, followed by the underlying additive
group functor, with no choice of an invariant subgroup.
Source: Stacks Project, Tag 04JR (blueprint: det-base-field-cd-cochains). -/
noncomputable abbrev baseFieldIntegerInvariants
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G) :=
  E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
    forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat

/-- Right derived invariants, using Mathlib's injective-resolution definition.
Source: Stacks Project, Tag 04JR (blueprint: det-base-field-cd-cochains). -/
noncomputable abbrev baseFieldDerivedInvariants
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A] [Abelian A] [EnoughInjectives A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(baseFieldIntegerInvariants G A E).Additive] (n : ℕ) :
    A ⥤ AddCommGrpCat.{max u s} :=
  (baseFieldIntegerInvariants G A E).rightDerived n

/-- The natural coordinates and the inhomogeneous differential of continuous cochains.
`Fin.contractNth` multiplies adjacent entries, with its final face deleting the last entry.
For `n = 0` the formula is exactly `g • m - m`.
Source: blueprint cochains statement, displayed differential
(blueprint: det-base-field-cd-cochains). -/
def HasBaseFieldCochainCoordinates
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V) : Prop :=
  (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
    e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g)) ∧
  (∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
    e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
      (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
        ∑ k : Fin (n + 1),
          (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g))

/-- Continuous cochain cohomology is a universal delta-functor, naturally identified with
derived invariants by mutually inverse morphisms of delta-functors.

Source: blueprint cochains statement (1), and Stacks Project, Tag 010T
(blueprint: det-base-field-cd-cochains).

Proof: The category is the category of discrete integer representations via `E`.
The integer-invariants infrastructure gives enough injectives and left exact invariants;
invariants are additive since coefficient maps restrict additively. The locally constant
cochain effaceability theorem supplies `C`, its coordinates, and its cohomological
delta-functor with degree zero naturally equal to invariants. The coordinate formula is
the displayed differential, including degree zero. Positive cohomology is effaced by the
orbit embedding into the discrete coinduced module: evaluation at one proves monicity,
and insertion of one contracts the homogeneous complex in positive degrees. By Tag 010T
this delta-functor is universal. The right derived functors of the left exact invariant
functor are universal too. Extend the degree-zero identification in both directions.
Uniqueness in universality makes the composites the identity in every degree, so the
comparison is natural and commutes with connecting maps. -/
theorem exists_baseFieldContinuousCochains_universal
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    ∃ (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
      (e : ∀ (M : A) (n : ℕ),
        (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V),
      HasBaseFieldCochainCoordinates G A E C e ∧
      ∃ (hI : EnoughInjectives A) (hV : (baseFieldIntegerInvariants G A E).Additive)
        (T R : CohomologicalDeltaFunctor A AddCommGrpCat.{max u s}),
        T.F = (fun n ↦ C ⋙ HomologicalComplex.homologyFunctor
          AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n) ∧
        T.IsUniversal ∧ Nonempty (T.F 0 ≅ baseFieldIntegerInvariants G A E) ∧
        R.F = (fun n ↦ @baseFieldDerivedInvariants G _ _ _ A _ _ hI E hV n) ∧
        ∃ (α : CohomologicalDeltaFunctor.Hom T R) (β : CohomologicalDeltaFunctor.Hom R T),
          (∀ n : ℕ, α.app n ≫ β.app n = 𝟙 (T.F n)) ∧
          (∀ n : ℕ, β.app n ≫ α.app n = 𝟙 (R.F n)) := by
  sorry

/-- Directed unions of discrete coefficient modules are preserved by continuous cochain
cohomology. The injective cocone legs identify each stage with a stable subgroup; their
joint surjectivity says exactly that the union is the vertex. `IsColimit` states the
canonical comparison is an isomorphism, without choosing a colimit object.

Source: blueprint cochains statement (2), proof (2), and Stacks Project, Tag 00DB
(blueprint: det-base-field-cd-cochains).

Proof: A locally constant cochain on compact `G^n` has finite image. Nonemptiness and
directedness put this finite set in one coefficient stage, so the cochain complex at the
union is the degreewise colimit of the stage complexes. The differential preserves every
stable subgroup. Filtered colimits of abelian groups are exact (Tag 00DB). Apply exactness
to the sequences from cycles to terms to boundaries, and from boundaries to cycles to
cohomology. The resulting cycle and boundary identifications show that the canonical
cohomology cocone is a colimit. Transport through the natural derived-invariant comparison
of clause (1) to obtain the assertion for Galois cohomology, including degree zero. -/
theorem baseFieldContinuousCochains_directedUnion
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hC : HasBaseFieldCochainCoordinates G A E C e)
    (I : Type t) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ A) (c : Cocone D)
    (hinj : ∀ i : I, Function.Injective (E.functor.map (c.ι.app i)).hom.hom)
    (hunion : ∀ m : (E.functor.obj c.pt).obj.V,
      ∃ (i : I) (x : (E.functor.obj (D.obj i)).obj.V),
        (E.functor.map (c.ι.app i)).hom.hom x = m)
    (n : ℕ) :
    Nonempty (IsColimit ((C ⋙ HomologicalComplex.homologyFunctor
      AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n).mapCocone c)) := by
  sorry

/-- Open normal subgroups acting trivially on the entire coefficient module.
The subtype order is inclusion; its order dual is the inflation index category.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
abbrev baseFieldTrivialOpenNormals
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :=
  {N : OpenNormalSubgroup G // ∀ (g : G), g ∈ N → ∀ m : M.obj.V, M.obj.ρ g m = m}

/-- The finite-quotient diagram for the inverse-limit hypothesis, with its actual quotient
projections. Its index order is inclusion, so an arrow `N ≤ N'` induces `G/N → G/N'`.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
def baseFieldQuotientDiagram
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    baseFieldTrivialOpenNormals G M ⥤ Type u where
  obj N := G ⧸ N.val.toSubgroup
  map {N N'} f := TypeCat.ofHom (fun x ↦
    QuotientGroup.map N.val.toSubgroup N'.val.toSubgroup
      (MonoidHom.id G) (fun _ hx ↦ (leOfHom f) hx) x)
  map_id N := by
    ext x
    refine Quotient.inductionOn x ?_
    intro g
    rfl
  map_comp f g := by
    ext x
    refine Quotient.inductionOn x ?_
    intro h
    rfl

/-- The canonical quotient cone with vertex `G`, without any chosen limit comparison.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
def baseFieldQuotientCone
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    Cone (baseFieldQuotientDiagram G M) where
  pt := G
  π :=
    { app := fun N ↦ TypeCat.ofHom (QuotientGroup.mk' N.val.toSubgroup)
      naturality := by intros; ext x; rfl }

/-- The inverse-limit hypothesis is Mathlib's universal property for the canonical quotient
cone. For compact Hausdorff `G` and its finite discrete quotients, its underlying limit
bijection is also a topological group isomorphism, by the compact-to-Hausdorff criterion.
Source: blueprint cochains statement (3) (blueprint: det-base-field-cd-cochains). -/
def IsBaseFieldQuotientLimit
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteContinuousRep.{0, u, max u s} ℤ G) : Prop :=
  Nonempty (IsLimit (baseFieldQuotientCone G M))

/-- Finite-quotient inflation realizes both the continuous complex and its cohomology as
colimits. The coordinate equations specify quotient differentials, all transition maps,
and the cocone legs by their pullbacks to tuples in `G`; quotient surjectivity makes these
specifications unique. In particular these are canonical inflation maps.

Source: blueprint cochains statement (3), opening compactness paragraph and proof (3);
Stacks Project, Tag 00DB (blueprint: det-base-field-cd-cochains).

Proof: The inverse-limit hypothesis implies that the subgroup family is nonempty: an
empty inverse limit is trivial, and the whole group then acts trivially. Fix a member N0.
Compactness and the open-normal neighborhood basis show that every cochain factors through
some finite quotient G/K: cover by finitely many constant boxes and intersect their open
normal subgroups. Replace K by K intersect N0. This subgroup acts trivially on M, so the
displayed quotient differential pulls back to the differential on G. Intersections make
the index nonempty directed under reverse inclusion. Inflation is injective since quotient
maps are surjective. Representatives agreeing on G agree at their common intersection.
Thus the specified inflation cocone is a colimit of complexes, degree by degree. Exactness
of filtered colimits identifies its cycles and boundaries, hence gives the cohomology
colimit cocone. Clause (1) identifies these cohomology groups with derived invariants for
G and each finite quotient, with inflation as their canonical comparison. Degree zero
uses the singleton G^0 and zero incoming boundaries. -/
theorem baseFieldContinuousCochains_finiteQuotients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hC : HasBaseFieldCochainCoordinates G A E C e)
    (M : A) (hlim : IsBaseFieldQuotientLimit G (E.functor.obj M)) :
    ∃ (D : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ ⥤
        CochainComplex AddCommGrpCat.{max u s} ℕ)
      (eN : ∀ (N : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ) (n : ℕ),
        (D.obj N).X n ≃+
          LocallyConstant (Fin n → G ⧸ N.val.toSubgroup) (E.functor.obj M).obj.V)
      (ι : D ⟶ (Functor.const _).obj (C.obj M)),
      (∀ (N : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ)
        (n : ℕ) (x : (D.obj N).X n) (g : Fin (n + 1) → G),
        eN N (n + 1) (((D.obj N).d n (n + 1)) x)
            (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k)) =
          (E.functor.obj M).obj.ρ (g 0)
              (eN N n x (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k.succ))) +
            ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
              eN N n x (fun j ↦ QuotientGroup.mk' N.val.toSubgroup
                (Fin.contractNth k (· * ·) g j))) ∧
      (∀ (N N' : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ)
        (f : N ⟶ N') (n : ℕ) (x : (D.obj N).X n) (g : Fin n → G),
        eN N' n (((D.map f).f n) x) (fun k ↦ QuotientGroup.mk' N'.val.toSubgroup (g k)) =
          eN N n x (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k))) ∧
      (∀ (N : (baseFieldTrivialOpenNormals G (E.functor.obj M))ᵒᵈ)
        (n : ℕ) (x : (D.obj N).X n) (g : Fin n → G),
        e M n (((ι.app N).f n) x) g =
          eN N n x (fun k ↦ QuotientGroup.mk' N.val.toSubgroup (g k))) ∧
      Nonempty (IsColimit (Cocone.mk (C.obj M) ι)) ∧
      (∀ n : ℕ, Nonempty (IsColimit
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u s}
          (ComplexShape.up ℕ) n).mapCocone (Cocone.mk (C.obj M) ι)))) := by
  sorry

end Rep
