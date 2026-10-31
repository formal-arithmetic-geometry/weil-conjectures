/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsMittagLeffler
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.RingTheory.MittagLefflerHomSystems

/-!
# Countable extraction from a finitely presented Mittag-Leffler presentation

Source: Stacks Project, Algebra, Tag 059W (blueprint: lem-trf-ml-countable-colimit).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- The restriction of a module diagram to a subset of its partially ordered index.

Source: Stacks Project, Algebra, Tag 059W (blueprint: lem-trf-ml-countable-colimit).
-/
def restrictedDiagram {R : Type u} [CommRing R]
    {I : Type v} [PartialOrder I]
    (F : I ⥤ ModuleCat.{max u v w} R) (J : Set I) : J ⥤ ModuleCat.{max u v w} R where
  obj j := F.obj j.1
  map f := F.map f
  map_id _ := F.map_id _
  map_comp _ _ := F.map_comp _ _

/-- The cocone on a restricted diagram induced by a cocone on the original diagram.

Source: Stacks Project, Algebra, Tag 059W (blueprint: lem-trf-ml-countable-colimit).
-/
def restrictedCocone {R : Type u} [CommRing R]
    {I : Type v} [PartialOrder I] {F : I ⥤ ModuleCat.{max u v w} R}
    (c : Cocone F) (J : Set I) : Cocone (restrictedDiagram F J) where
  pt := c.pt
  ι :=
    { app := fun j => c.ι.app j.1
      naturality := by
        intro j k f
        exact c.ι.naturality f }


/-- The canonical map from the restricted colimit to the original cocone target.

Source: Stacks Project, Algebra, Tag 059W (blueprint: lem-trf-ml-countable-colimit).
-/
noncomputable def restrictedColimitMap {R : Type u} [CommRing R]
    {I : Type v} [PartialOrder I] {F : I ⥤ ModuleCat.{max u v w} R}
    (c : Cocone F) (J : Set I) (_hJ : J.Nonempty) (_dJ : IsDirected J (· ≤ ·)) :
    colimit (restrictedDiagram F J) ⟶ c.pt := by
  letI : Nonempty J := ⟨⟨_hJ.choose, _hJ.choose_spec⟩⟩
  letI : IsDirectedOrder J := _dJ
  exact colimit.desc (restrictedDiagram F J) (restrictedCocone c J)

/--
A countably generated Mittag-Leffler module presented as a directed colimit of finitely
presented modules is already the colimit of a countable directed subdiagram.

Source: Stacks Project, Algebra, Tag 059W (lemma-ML-countable-colimit); the module
notion is the tensor condition of Tag 059M (proposition-ML-tensor).
(blueprint: lem-trf-ml-countable-colimit)

Proof:
1. Choose a finite or countable generating sequence and representatives for its elements
   in the given filtered colimit, together with one initial index.
2. The tensor-product Mittag-Leffler condition and the Hom-system stabilization theorem
   give, for every index, a later index through which all subsequent transition maps
   factor.
3. Repeatedly close the chosen countable set under these stabilizing indices and under
   directed upper bounds; the union is countable, nonempty, directed, and retains the
   factorization property.
4. The restricted colimit map is surjective because the chosen generators occur in the
   restricted system and finite sums have a common upper bound.
5. If an element from a restricted stage maps to zero, eventual vanishing in the original
   colimit followed by the factorization property gives vanishing at a restricted stage;
   hence the canonical map is injective and therefore an isomorphism.
-/
theorem exists_countable_directed_colimit_of_isMittagLeffler
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{max u v w} R)
    [∀ i : I, Module.FinitePresentation R (F.obj i)]
    (c : Cocone F) (hc : IsColimit c)
    (hM : Module.IsMittagLeffler.{u, max u v w, max u v w, 0} R c.pt)
    (hcountable : ∃ E : Set c.pt, E.Countable ∧ Submodule.span R E = ⊤) :
    ∃ J : Set I, J.Countable ∧
      ∃ (hJ : J.Nonempty) (dJ : IsDirected J (· ≤ ·)),
        IsIso (restrictedColimitMap c J hJ dJ) := by
  sorry

end Module
