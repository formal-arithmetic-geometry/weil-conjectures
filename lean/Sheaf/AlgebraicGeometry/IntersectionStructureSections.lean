/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Topology.Spectral.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.Topology.SetsInverseImageComposition
import Sheaf.Topology.SpectralLimitPullbackSections

/-!
# Structure-sheaf sections on intersections of quasi-compact opens

Source: Stacks Project, More on Groupoids in Spaces, equation
`equation-sections-of-intersection` preceding Tag 0APJ
(blueprint: lem-a1-sections-intersection-structure-colimit).

The auxiliary definitions construct the subspace, its inverse-image structure sheaf,
the unit restriction maps, and the diagram indexed by the distinct indicated opens.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The subspace inclusion of the intersection. Source: Stacks, equation
`equation-sections-of-intersection` (blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionInclusion (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual inverse-image structure sheaf on the subspace intersection. Source: Stacks,
equation `equation-sections-of-intersection`, Tags 008F/008I
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionStructureSheaf (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    (TopCat.of {x : X // ∀ i : I, x ∈ U i}).Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat (intersectionInclusion X U)).obj X.sheaf

/-- Global sections of the inverse-image structure sheaf, without any scheme structure on
the intersection. Source: Stacks, equation `equation-sections-of-intersection`
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionSections (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) : CommRingCat.{u} :=
  (intersectionStructureSheaf X U).obj.obj (op ⊤)

/-- Restriction from a neighbourhood of the intersection: the inverse-image unit followed
by restriction to the full subspace. Source: Stacks, equation
`equation-sections-of-intersection`, Tag 008F
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionRestriction (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (V : X.Opens) (hV : ∀ x : X, (∀ i : I, x ∈ U i) → x ∈ V) :
    X.presheaf.obj (op V) ⟶ intersectionSections X U :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion X U)).unit.app X.sheaf).hom.app (op V) ≫
      (intersectionStructureSheaf X U).obj.map
        (homOfLE (fun (x : {x : X // ∀ i : I, x ∈ U i}) _ ↦
          hV x.val x.property)).op

/-- The restriction diagram, with repeated opens identified, indexed by reverse inclusion.
Source: Stacks, equation `equation-sections-of-intersection`
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionOpenDiagram (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    {V : X.Opens // V ∈ Set.range U}ᵒᵖ ⥤ CommRingCat.{u} where
  obj V := X.presheaf.obj (op V.unop.val)
  map f := X.presheaf.map (homOfLE (leOfHom f.unop)).op
  map_id V := X.presheaf.map_id (op V.unop.val)
  map_comp _f _g := X.presheaf.map_comp _ _

/-- The continuous map between intersections induced by a scheme morphism carrying each
indicated open into the corresponding open. Source: Stacks, naturality of equation
`equation-sections-of-intersection`
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionMap {X Y : Scheme.{u}} (g : X ⟶ Y) {I : Type v}
    (U : I → X.Opens) (V : I → Y.Opens) (h : ∀ i : I, U i ≤ g ⁻¹ᵁ V i) :
    TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶
      TopCat.of {y : Y // ∀ i : I, y ∈ V i} :=
  TopCat.ofHom ⟨fun x ↦ ⟨g x.val, fun i ↦ h i (x.property i)⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Structure-sheaf sections on a directed intersection are the filtered colimit, in sets,
abelian groups and commutative rings, naturally under scheme isomorphisms. The final clause
specifies the canonical sheaf transport by its adjunction-unit equation on every open,
then states its square with the section restrictions. Thus no unspecified comparison map
is assumed. Distinct opens index the colimit; the elementwise clauses retain the original
indexing, including repetitions.

Source: Stacks, equation `equation-sections-of-intersection` preceding Tag 0APJ
(blueprint: lem-a1-sections-intersection-structure-colimit).

Proof, following the node's eight steps:
1. Quasi-separatedness makes intersections of compact opens compact. Nonempty finite
   intersections refine the family without changing its intersection. Fix a member Y;
   the distinct members contained in Y are cofinal and are spectral qcqs schemes
   (quasi-separated-affine-cover criterion and qcqs-scheme-spectral).
2. Their inclusion maps are spectral. Compatible tuples have a common underlying point,
   giving the intersection as their topological limit with its subspace topology; this
   also applies to the empty intersection (def-weil-spectral-space).
3. Filtered ring colimits have exactly the set-colimit representatives and eventual
   equality relation (lem-pc-filtered-colimit-commrings-elementwise and
   lem-weil-pbc-filtered-colimit-sets-elementwise). Ring sheafification commutes with
   underlying sets and its unit (ring-sheafification-space-underlying-abelian).
4. Inverse image along an open embedding is ordinary restriction: the open itself is
   terminal among its neighbourhoods. The unit equation of sets-inverse-image-composition
   identifies the transitions and the displayed maps with the actual restriction units.
5. Apply spectralLimit_pullback_sections (b) to the full compact open Y for surjectivity.
6. For two representatives on U_i use Y = U_i and clause (c) of the same theorem to get
   equality on a further original member. Passing to distinct opens loses no indices.
7. Surjectivity and eventual equality give the set colimit. A compatible cocone of group
   or ring maps factors by choosing a representative; eventual equality proves this
   independent of choice. Move finitely many representatives to a common stage to check
   addition, multiplication, zero, negatives and one. Surjectivity gives uniqueness.
8. The structure-sheaf map of an isomorphism and the inverse-image units give the unique
   transport of sheaves by the inverse-image adjunction (Tag 008F). Naturality on each
   neighbourhood gives the displayed square. Colimit uniqueness then gives naturality
   in all three categories. Empty spaces have their unique section, also in the zero ring. -/
theorem sections_intersection_structure_colimit
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hqc : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) :
    (∀ s : intersectionSections X U, ∃ (i : I) (a : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a = s) ∧
    (∀ (i : I) (a a' : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a =
        intersectionRestriction X U (U i) (fun x hx ↦ hx i) a' →
      ∃ (k : I) (hki : U k ≤ U i),
        X.presheaf.map (homOfLE hki).op a = X.presheaf.map (homOfLE hki).op a') ∧
    (∃ ι : intersectionOpenDiagram X U ⟶
        (Functor.const _).obj (intersectionSections X U),
      (∀ V, ι.app V = intersectionRestriction X U V.unop.val
        (fun x hx ↦ V.unop.property.elim (fun i hi ↦ hi ▸ hx i))) ∧
      Nonempty (IsColimit (Cocone.mk (intersectionSections X U) ι)) ∧
      Nonempty (IsColimit ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι))) ∧
      Nonempty (IsColimit ((CategoryTheory.forget CommRingCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι)))) ∧
    (∀ (Y : Scheme.{u}) (g : X ≅ Y) (V : I → Y.Opens)
        (hUV : ∀ i : I, U i = g.hom ⁻¹ᵁ V i),
      ∃! t : intersectionStructureSheaf Y V ⟶
          (TopCat.Sheaf.pushforward CommRingCat
            (intersectionMap g.hom U V (fun i ↦ (hUV i).le))).obj
              (intersectionStructureSheaf X U),
        (∀ W : Y.Opens,
          HEq
            (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion Y V)).unit.app Y.sheaf).hom.app (op W) ≫
              t.hom.app (op ((Opens.map (intersectionInclusion Y V)).obj W)))
            (g.hom.app W ≫
              ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion X U)).unit.app X.sheaf).hom.app
                  (op (g.hom ⁻¹ᵁ W)))) ∧
        (∀ i : I,
          intersectionRestriction Y V (V i) (fun y hy ↦ hy i) ≫
              t.hom.app (op ⊤) ≫
                (intersectionStructureSheaf X U).obj.map
                  (homOfLE (fun _ _ ↦ trivial)).op =
            g.hom.appLE (V i) (U i) (hUV i).le ≫
              intersectionRestriction X U (U i) (fun x hx ↦ hx i))) := by
  sorry

end AlgebraicGeometry.Scheme
