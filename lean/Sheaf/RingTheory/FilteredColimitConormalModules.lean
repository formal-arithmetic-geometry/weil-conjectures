module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected

/-! # Filtered colimits of conormal modules

Source: Stacks Project, Algebra, Tag 07BQ (lemma-colimits-NL), the implicit
ideal-square quotient argument (blueprint: lem-sfb-filtered-colimit-conormal-modules).

The diagram and cocone below use Mathlib's `Ideal.Cotangent` and `Ideal.mapCotangent`.
The last theorem states the universal property for the prescribed quotient maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Ideal

variable {R : Type u} [CommRing R] {J : Type v} [SmallCategory J]
variable (P : J ⥤ CommAlgCat.{v} R) (L : ∀ j : J, Ideal (P.obj j))
variable (hL : ∀ ⦃j k : J⦄ (a : j ⟶ k), L j ≤ (L k).comap (P.map a).hom)

/-- Identity and composition laws for the induced quotient maps.
Source: Stacks Project, Algebra, Tag 07BQ, ideal-square quotient argument
(blueprint: lem-sfb-filtered-colimit-conormal-modules).
Proof: an algebra map preserves finite sums of products in the ideal, hence induces
`Ideal.mapCotangent`. On a representative `[x]`, identity and composition are exactly
those of `P`. Surjectivity of `Ideal.toCotangent` extends the equalities to all classes. -/
theorem conormalDiagram_laws :
    (∀ j : J, ModuleCat.ofHom (mapCotangent (L j) (L j) (P.map (𝟙 j)).hom (hL (𝟙 j))) =
      𝟙 (ModuleCat.of R (L j).Cotangent)) ∧
    (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l),
      ModuleCat.ofHom (mapCotangent (L j) (L l) (P.map (a ≫ b)).hom (hL (a ≫ b))) =
        ModuleCat.ofHom (mapCotangent (L j) (L k) (P.map a).hom (hL a)) ≫
          ModuleCat.ofHom (mapCotangent (L k) (L l) (P.map b).hom (hL b))) := by
  sorry

/-- The diagram `j ↦ L j / (L j)²`, with the prescribed maps on representatives.
Source: Stacks Project, Algebra, Tag 07BQ, ideal-square quotient argument
(blueprint: lem-sfb-filtered-colimit-conormal-modules). -/
def conormalDiagram : J ⥤ ModuleCat.{v} R where
  obj j := ModuleCat.of R (L j).Cotangent
  map a := ModuleCat.ofHom (mapCotangent _ _ (P.map a).hom (hL a))
  map_id j := (conormalDiagram_laws P L hL).1 j
  map_comp a b := (conormalDiagram_laws P L hL).2 _ _ _ a b

variable (c : Cocone P) (I : Ideal c.pt)
variable (hι : ∀ j : J, L j ≤ I.comap (c.ι.app j).hom)

/-- The quotient maps induced by the cocone legs are compatible with the diagram.
Source: Stacks Project, Algebra, Tag 07BQ, ideal-square quotient argument
(blueprint: lem-sfb-filtered-colimit-conormal-modules).
Proof: on `[x]` both composites are the class of the image of `x` under the
corresponding composite algebra map. The cocone identity for `c` identifies these
images, and quotient surjectivity gives equality of the linear maps. -/
theorem conormalCocone_naturality {j k : J} (a : j ⟶ k) :
    (conormalDiagram P L hL).map a ≫
        ModuleCat.ofHom (mapCotangent (L k) I (c.ι.app k).hom (hι k)) =
      ModuleCat.ofHom (mapCotangent (L j) I (c.ι.app j).hom (hι j)) := by
  sorry

/-- The cocone with vertex `I/I²` and legs `[x] ↦ [c.ι.app j x]`.
Source: Stacks Project, Algebra, Tag 07BQ, ideal-square quotient argument
(blueprint: lem-sfb-filtered-colimit-conormal-modules). -/
def conormalCocone : Cocone (conormalDiagram P L hL) where
  pt := ModuleCat.of R I.Cotangent
  ι :=
    { app := fun j ↦ ModuleCat.ofHom (mapCotangent (L j) I (c.ι.app j).hom (hι j))
      naturality := fun _ _ a ↦ by
        simpa using conormalCocone_naturality P L hL c I hι a }

/-- Compatible conormal modules commute with filtered colimits.
Source: Stacks Project, Algebra, Tag 07BQ (lemma-colimits-NL), the ideal-square
quotient argument (blueprint: lem-sfb-filtered-colimit-conormal-modules).
Proof:
1. Algebra maps preserve ideal squares; the preceding constructions therefore give
   the quotient diagram and its cocone with the prescribed maps on representatives.
2. By lem-weil-pbc-filtered-colimit-algebras-elementwise, the algebra colimit is
   also a ring colimit. By lem-pc-filtered-colimit-commrings-elementwise, equal
   images of ring elements become equal after arrows to a common object.
3. A class in `I/I²` has an ideal representative; `hlift` lifts this representative
   from some `L j`. Thus the cocone legs are jointly surjective.
4. If `[x]` from `L j` maps to zero, its image is a finite sum of products of
   elements of `I`. Lift all the finitely many factors by `hlift` and use
   filteredness to move them and `x` to one common stage `t`. The image `X` of `x`
   and the resulting sum `Y` have equal images in the colimit; `Y` belongs to
   `(L t)²`. For an empty sum take `t = j` and `Y = 0`.
5. The elementwise ring criterion supplies two arrows identifying `X` and `Y`.
   Equalize these parallel arrows using filteredness. Their single resulting
   composite sends `[x]` to zero, since ideal squares are preserved.
6. Apply lem-weil-pbc-filtered-colimit-modules-criterion: joint surjectivity from
   step 3 and eventual vanishing of kernels from steps 4--5 prove that this
   very cocone is a colimit. No injectivity, flatness, or finite generation is used. -/
theorem isColimit_conormalCocone [IsFiltered J] (hc : IsColimit c)
    (hlift : ∀ x : c.pt, x ∈ I →
      ∃ (j : J) (y : P.obj j), y ∈ L j ∧ c.ι.app j y = x) :
    Nonempty (IsColimit (conormalCocone P L hL c I hι)) := by
  sorry

end Ideal
