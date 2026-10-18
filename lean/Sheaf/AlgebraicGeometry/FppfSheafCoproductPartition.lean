/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Clopen partitions from coproducts of fppf sheaves

Source: Stacks Project, Spaces, Tags 0F15 and 02WO, and Sites, Tag 00WI
(blueprint: lem-trf-fppf-sheaf-coproduct-partition).

The auxiliary data record encodes the opens and their component sections. Coproduct
existence is asserted without assuming a sheafification instance on the big site.
The coefficient and index universe `max u v` includes the scheme universe `u`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The open subscheme as an object over the base. Source: Stacks, Spaces, Tag 0F15
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
def fppfPartitionOpen {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) : Over S :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of a partition piece over the base. Source: Stacks, Spaces, Tag 0F15
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
def fppfPartitionInclusion {S : Scheme.{u}} (T : Over S) (U : T.left.Opens) :
    fppfPartitionOpen T U ⟶ T :=
  Over.homMk U.ι

/-- Restriction of a test morphism to the inverse image of an open piece.
Source: Stacks, Spaces, Tags 0F15 and 02WO
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
noncomputable def fppfPartitionRestriction {S : Scheme.{u}} {Z T : Over S} (b : Z ⟶ T)
    (U : T.left.Opens) :
    fppfPartitionOpen Z (b.left ⁻¹ᵁ U) ⟶ fppfPartitionOpen T U :=
  Over.homMk (b.left ∣_ U)
    (by
      change (b.left ∣_ U) ≫ U.ι ≫ T.hom = (b.left ⁻¹ᵁ U).ι ≫ Z.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])

/-- A clopen partition of a test scheme with a section in each summand sheaf.
Empty opens and empty index types are permitted. Source: Stacks, Spaces, Tags 0F15
and 02WO (blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
structure FppfCoproductPartition {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v))) (T : Over S) where
  /-- The open subschemes of the partition. -/
  opens : I → T.left.Opens
  /-- Each piece is also closed. -/
  isClosed : ∀ i, IsClosed (opens i : Set T.left)
  /-- Distinct pieces are disjoint. -/
  disjoint : Pairwise (fun i j ↦ Disjoint (opens i) (opens j))
  /-- The pieces cover the test scheme. -/
  covers : iSup opens = ⊤
  /-- The component section on each piece. -/
  sections : ∀ i, (G i).obj.obj (op (fppfPartitionOpen T (opens i)))

/-- The component sections have the prescribed image in the coproduct sheaf.
Source: Stacks, Spaces, Tag 0F15
(blueprint: lem-trf-fppf-sheaf-coproduct-partition). -/
def FppfCoproductPartition.MapsTo {S : Scheme.{u}} {I : Type (max u v)}
    {G : I → Sheaf (fppfTopology.over S) (Type (max u v))}
    {C : Sheaf (fppfTopology.over S) (Type (max u v))} (c : ∀ i, G i ⟶ C)
    {T : Over S} (d : FppfCoproductPartition G T) (a : C.obj.obj (op T)) : Prop :=
  ∀ i, (c i).hom.app (op (fppfPartitionOpen T (d.opens i))) (d.sections i) =
    C.obj.map (fppfPartitionInclusion T (d.opens i)).op a

/-- Coproducts of fppf sheaves exist, with monic coprojections, and their sections
correspond uniquely to clopen partitions with component sections. The summand squares
are cartesian, the correspondence commutes with arbitrary test morphisms, and an empty
coproduct has one section precisely on empty schemes.
Source: Stacks, Spaces, Tags 0F15 and 02WO; Sites, Tags 00WI and 00WK
(blueprint: lem-trf-fppf-sheaf-coproduct-partition).

Proof:
1. Form the labelled coproduct presheaf and sheafify it, using
   lem-trf-sieve-set-sheafification-exists. The adjunction identifies maps from its
   sheafification with families of maps from the summands, proving the colimit property.
2. By lem-weil-pbc-site-sheafification-sections-local every section locally has a label.
   Local equality of two images forces equal labels unless the test scheme is empty;
   for equal labels the sheaf condition gives equal sections. This proves monicity,
   injectivity on sections, and emptiness of mixed intersections. Every sheaf has one
   section on the empty scheme, by its empty covering.
3. The images of the labelled covering members are open by lem-weil-pbc-flat-lfp-open.
   Members with distinct labels have empty fibre product. Surjective base change
   (lem-weil-pbc-surjective-base-change) then shows that their images are disjoint.
4. Unite the images of each label. They cover the test scheme and are pairwise disjoint.
   Each complement is the union of the other opens, so each piece is closed. Scheme
   morphism gluing (lem-weil-pbc-scheme-morphism-gluing) gives the scheme coproduct.
5. On each piece glue its local labelled sections, using injectivity on sections for
   agreement. The sheaf condition gives the required equality with the original section.
6. Compare with another partition on all intersections. Mixed intersections are empty,
   forcing the opens to coincide; injectivity then identifies their component sections.
7. A pair consisting of a test map and a summand section with equal images factors
   uniquely through the corresponding open: all other inverse image pieces are empty.
   This factorization is natural in the test object and proves the cartesian square.
8. Inverse images of the opens and restrictions of the sections give the partition
   after any test morphism, by uniqueness. Conversely the images of any component
   sections glue uniquely, since their mixed overlaps are empty.
9. For an empty index type the coproduct presheaf has no sections. Local representatives
   force an empty covering, hence an empty test scheme. On the empty scheme the empty
   covering gives exactly one section. -/
theorem fppfSheaf_coproduct_partition {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v))) :
    (∃ (C : Sheaf (fppfTopology.over S) (Type (max u v))) (c : ∀ i, G i ⟶ C),
      Nonempty (IsColimit (Cofan.mk C c))) ∧
    (∀ (C : Sheaf (fppfTopology.over S) (Type (max u v))) (c : ∀ i, G i ⟶ C),
      IsColimit (Cofan.mk C c) →
      (∀ i, Mono (c i) ∧ ∀ T : Over S, Function.Injective ((c i).hom.app (op T))) ∧
      (∀ (T : Over S) (a : C.obj.obj (op T)),
        ∃! d : FppfCoproductPartition G T, d.MapsTo c a) ∧
      (∀ (T : Over S) (a : C.obj.obj (op T)) (d : FppfCoproductPartition G T),
        d.MapsTo c a →
        (Nonempty (IsColimit (Cofan.mk T.left (fun i ↦ (d.opens i).ι)))) ∧
        (∀ i, IsPullback
          (uliftYoneda.{v}.map (fppfPartitionInclusion T (d.opens i)))
          (uliftYonedaEquiv.{v}.symm (d.sections i))
          (uliftYonedaEquiv.{v}.symm a) (c i).hom) ∧
        (∀ (Z : Over S) (b : Z ⟶ T),
          ∃ e : FppfCoproductPartition G Z,
            e.MapsTo c (C.obj.map b.op a) ∧
            ∀ i, e.opens i = b.left ⁻¹ᵁ d.opens i ∧
              HEq (e.sections i)
                ((G i).obj.map (fppfPartitionRestriction b (d.opens i)).op (d.sections i)))) ∧
      (∀ (T : Over S) (d : FppfCoproductPartition G T),
        ∃! a : C.obj.obj (op T), d.MapsTo c a) ∧
      (IsEmpty I → ∀ T : Over S,
        (IsEmpty T.left → Nonempty (Unique (C.obj.obj (op T)))) ∧
        (Nonempty T.left → IsEmpty (C.obj.obj (op T))))) := by
  sorry

end AlgebraicGeometry.Scheme
