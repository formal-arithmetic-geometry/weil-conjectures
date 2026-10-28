/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt

/-!
# Morphisms out of an object of `D(C)` commuting with filtered colimits

Let `C` be an abelian category and `s` an object of its derived category. We say that
`Hom(s, -[n])` *commutes with filtered colimits* of objects of `C`
(`DerivedCategory.HomCommutesWithFilteredColimits`) if for every filtered colimit
`B = colim Bᵢ` in `C` and every `n`, the canonical map `colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is
bijective. This is blueprint `sk-lem-constructible-ext-continuity` for targets in degree `0`.

* The class of such `s` contains zero, is closed under isomorphisms, shifts and extensions
  (blueprint `det-lem-constructible-ext-continuity-devissage`, five lemma).
* For `s` bounded above, the comparison is then bijective for every filtered diagram `Yᵢ` in
  `D(C)` of uniformly bounded below objects with a cocone `Y` inducing colimits on cohomology
  (`DerivedCategory.HomCommutesWithFilteredColimits.diagram`), by induction on the amplitude
  along the truncation triangles.
* The class is transported along adjunctions `F ⊣ G` whose right adjoint `G` is left
  `t`-exact up to a shift and commutes with filtered colimits on cohomology
  (`DerivedCategory.HomCommutesWithFilteredColimits.of_adjunction`), and along adjunctions of
  exact functors whose right adjoint preserves filtered colimits
  (`DerivedCategory.HomCommutesWithFilteredColimits.mapDerivedCategory`).
-/

@[expose] public section

universe w

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Blueprint `sk-lem-constructible-ext-continuity` for targets in degree `0`: for every filtered
colimit `B = colim Bᵢ` of objects of `C` (indexed by a category in `Type w`) and every `n`, the
map `colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is surjective (every morphism factors through some
`Bᵢ[n]`) and injective (a morphism to `Bᵢ[n]` which vanishes in `B[n]` vanishes in some
`Bⱼ[n]`). -/
def HomCommutesWithFilteredColimits (s : DerivedCategory C) : Prop :=
  ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (F : I ⥤ C) (c : Cocone F)
    (_ : IsColimit c) (n : ℤ),
    (∀ f : s ⟶ (singleFunctor C n).obj c.pt, ∃ (i : I) (g : s ⟶ (singleFunctor C n).obj (F.obj i)),
      f = g ≫ (singleFunctor C n).map (c.ι.app i)) ∧
    (∀ (i : I) (g : s ⟶ (singleFunctor C n).obj (F.obj i)),
      g ≫ (singleFunctor C n).map (c.ι.app i) = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (singleFunctor C n).map (F.map t) = 0)

namespace HomCommutesWithFilteredColimits

/-- Surjectivity is the factorization property `HomFactorsThroughFilteredColimits`. -/
lemma homFactorsThroughFilteredColimits {s : DerivedCategory C}
    (hs : HomCommutesWithFilteredColimits.{w} s) : HomFactorsThroughFilteredColimits.{w} s :=
  fun I _ _ F c hc n f ↦ (hs I F c hc n).1 f

lemma of_isZero {s : DerivedCategory C} (hs : IsZero s) :
    HomCommutesWithFilteredColimits.{w} s :=
  sorry

lemma of_iso {s s' : DerivedCategory C} (e : s ≅ s')
    (hs : HomCommutesWithFilteredColimits.{w} s) : HomCommutesWithFilteredColimits.{w} s' :=
  sorry

lemma shift {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) (a : ℤ) :
    HomCommutesWithFilteredColimits.{w} ((shiftFunctor (DerivedCategory C) a).obj s) :=
  sorry

/-- Blueprint `det-lem-constructible-ext-continuity-devissage`: the class is closed under
extensions (five lemma on the long exact `Hom` sequences, filtered colimits of abelian groups
being exact). -/
lemma ext₂ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : HomCommutesWithFilteredColimits.{w} T.obj₁)
    (h₃ : HomCommutesWithFilteredColimits.{w} T.obj₃) :
    HomCommutesWithFilteredColimits.{w} T.obj₂ :=
  sorry

lemma ext₃ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : HomCommutesWithFilteredColimits.{w} T.obj₁)
    (h₂ : HomCommutesWithFilteredColimits.{w} T.obj₂) :
    HomCommutesWithFilteredColimits.{w} T.obj₃ :=
  sorry

lemma ext₁ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₂ : HomCommutesWithFilteredColimits.{w} T.obj₂)
    (h₃ : HomCommutesWithFilteredColimits.{w} T.obj₃) :
    HomCommutesWithFilteredColimits.{w} T.obj₁ :=
  sorry

/-- For `s` bounded above, the continuity of `Hom(s, -[q])` extends from filtered colimits of
objects of `C` to filtered diagrams `Yᵢ` of uniformly bounded below objects of `D(C)` with a
cocone `Y` which induces colimits on all cohomology objects: by induction on the amplitude along
the truncation triangles, `Hom(s, -[q])` only seeing a bounded window of degrees. -/
lemma diagram {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) (b : ℤ)
    [s.IsLE b] (I : Type w) [SmallCategory I] [IsFiltered I] (Y : I ⥤ DerivedCategory C)
    (c : Cocone Y) (a : ℤ) (hY : ∀ i, (Y.obj i).IsGE a) (hc : c.pt.IsGE a)
    (hH : ∀ n : ℤ, Nonempty (IsColimit ((homologyFunctor C n).mapCocone c))) (q : ℤ) :
    (∀ f : s ⟶ (shiftFunctor _ q).obj c.pt, ∃ (i : I) (g : s ⟶ (shiftFunctor _ q).obj (Y.obj i)),
      f = g ≫ (shiftFunctor _ q).map (c.ι.app i)) ∧
    (∀ (i : I) (g : s ⟶ (shiftFunctor _ q).obj (Y.obj i)),
      g ≫ (shiftFunctor _ q).map (c.ι.app i) = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (shiftFunctor _ q).map (Y.map t) = 0) :=
  sorry

variable {C' : Type*} [Category* C'] [Abelian C'] [HasDerivedCategory C']

/-- Transport along an adjunction `F ⊣ G` of triangulated functors: if `G` sends objects of `C'`
placed in degree `0` to objects of `D(C)` concentrated in degrees `≥ a`, and commutes on
cohomology with filtered colimits of objects of `C'`, then `F` preserves bounded above objects
whose morphisms commute with filtered colimits. -/
lemma of_adjunction {F : DerivedCategory C ⥤ DerivedCategory C'}
    {G : DerivedCategory C' ⥤ DerivedCategory C} (adj : F ⊣ G) [G.CommShift ℤ] (a : ℤ)
    (hG : ∀ B : C', (G.obj ((singleFunctor C' 0).obj B)).IsGE a)
    (hGc : ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (B : I ⥤ C') (c : Cocone B)
      (_ : IsColimit c) (n : ℤ),
      Nonempty (IsColimit ((homologyFunctor C n).mapCocone
        ((singleFunctor C' 0 ⋙ G).mapCocone c))))
    {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) (b : ℤ) [s.IsLE b] :
    HomCommutesWithFilteredColimits.{w} (F.obj s) :=
  sorry

/-- Transport along an adjunction `f ⊣ g` of exact functors of abelian categories, the right
adjoint `g` preserving filtered colimits: the levelwise functor `D(f)` preserves objects whose
morphisms commute with filtered colimits. -/
lemma mapDerivedCategory {f : C ⥤ C'} {g : C' ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (hg : ∀ (I : Type w) [SmallCategory I] [IsFiltered I], PreservesColimitsOfShape I g)
    {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) :
    HomCommutesWithFilteredColimits.{w} (f.mapDerivedCategory.obj s) :=
  sorry

end HomCommutesWithFilteredColimits

end DerivedCategory
