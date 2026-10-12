module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
import Sheaf.Topology.ConstantSheafLocallyConstantComparison
public import Sheaf.Topology.AbelianOpenExtensionByZero

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- A finite disjoint partition of each original domain, with zero pieces and signed
positive component sections. The equations `hs`, `hzero`, and `hsigned` retain the
connection to the original map; positive values alone would not suffice.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-constant-subsheaf-positive-refinement-data) -/
structure PositiveRefinementData
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C)
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (m : ℕ) (U : Fin m → Opens X)
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) where
  n : ℕ
  A : Fin n → Opens X
  hA : ∀ i, IsCompact (A i : Set X)
  c : Fin n → ℕ
  hc : ∀ i, 0 < c i
  f : ∀ i, (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K
  hv : ∀ i,
    (ι ≫ isoC.hom).hom.app (op (A i))
      ((f i).hom.app (op (A i)) (abelianOpenExtensionSection (A i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (A i)) (ULift.up (c i : ℤ))

  parent : Fin n → Fin m
  hAU : ∀ j, A j ≤ U (parent j)
  Z : Fin m → Opens X
  hZU : ∀ i, Z i ≤ U i
  hdisjoint : ∀ j k, parent j = parent k → j ≠ k → Disjoint (A j) (A k)
  hdisjointZ : ∀ j, Disjoint (A j) (Z (parent j))
  hcover : ∀ i, U i = Z i ⊔ ⨆ j : {j // parent j = i}, A j.1
  sign : Fin n → ℤ
  s : ∀ i, K.obj.obj (op (U i))
  hs : ∀ i, s i = (Sigma.ι _ i ≫ g).hom.app (op (U i))
      (abelianOpenExtensionSection (U i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (U i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (U i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (U i).inclusion').obj (U i))) (ULift.up 1)))
  hzero : ∀ i, K.obj.map (homOfLE (hZU i)).op (s i) = 0
  hsigned : ∀ j, K.obj.map (homOfLE (hAU j)).op (s (parent j)) =
    sign j • (f j).hom.app (op (A j))
      (abelianOpenExtensionSection (A j)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A j) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A j)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A j)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A j).inclusion').obj (A j))) (ULift.up 1)))

/-- Construct a finite signed partition and positive component maps, without yet
constructing a morphism between the coproducts.
Source: Stacks Project, Cohomology, Lemma 0A38, first proof paragraph.
https://stacks.math.columbia.edu/tag/0A38
(blueprint: lem-sc-constant-subsheaf-positive-refinement-data)

Proof: Let s i be the image under the i-th component of g of its canonical integer-one
section; this gives hs. Compose with the monomorphism into C and isoC. The locally
constant comparison identifies the resulting section with an integer-valued locally
constant function on U i. Here use the canonical description by local integer
representatives of the sheafification unit, so unit images have their prescribed values:
representatives exist locally by sheafification; equality on overlaps is detected by
evaluation at a point (factor the constant presheaf into the integer skyscraper there).
Their values therefore glue into a locally constant function, whose inverse glues
constant unit sections on its fibres. This gives compatibility with the unit, in addition
to the restriction compatibility of the comparison theorem. Compactness of U i makes
its range finite. Each fibre is
clopen in U i, hence open in X and compact in X (a closed subset of a compact space,
followed by the continuous inclusion). Let Z i be the zero fibre. Index all nonzero
fibres of all original domains by Fin n, retaining the original-domain index parent.
Take A j to be the corresponding fibre. These fibres are disjoint for each parent,
are disjoint from Z, and cover U together with Z, proving hAU, hZU, hdisjoint,
hdisjointZ and hcover. This also handles empty domains or an empty original family.

On a fibre of value a different from zero, set c j to the positive absolute value of a
and sign j to 1 or -1 according to its sign. Restrict s (parent j) to A j and multiply
by sign j, obtaining a section t j of K with image the constant c j. To construct f j,
on every open of A j send an integer to that multiple of the restriction of t j.
This is a map from the constant presheaf to the restriction of K. Sheafify, apply the
extension-by-zero functor, and compose with its restriction counit. The sheafification
unit and the explicit counit send the canonical unit to t j; this proves hv and
hsigned because sign j squared is one. On Z i the image of the restriction of s i
is zero. Monicity of the sheaf morphism makes the maps on sections injective, so the
restriction itself is zero, proving hzero. The resulting record has actual finite
partition data and component maps; no choice of a factorization is made here. -/
theorem positive_refinement_data
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C) [Mono ι]
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (m : ℕ) (U : Fin m → Opens X)
    (hU : ∀ i, IsCompact (U i : Set X))
    (g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K) :
    ∃ d : PositiveRefinementData X K C ι isoC m U g, True := by sorry

end TopCat.Sheaf
