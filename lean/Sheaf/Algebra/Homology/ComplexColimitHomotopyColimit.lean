/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sequential colimits of complexes represent homotopy colimits

Source: blueprint sec-smooth-purity, sk-prop-sf-kunneth-ordinary, order 1719;
Stacks Project, Derived Categories, Tags 093W, 0949, 0A5L and 090Z
(blueprint: lem-kun-complex-colimit-hocolim).

The two statements cover abelian sheaves and sheaves of modules over a commutative
ring sheaf. Arbitrary coproduct and colimit cocones are used, so the statements apply
to the degreewise chosen colimits as well. The equations for `u` and `q` specify
exactly the canonical telescope and colimit maps. The cone comparison is specified
by both its summand restrictions, without choosing a triangulated cone.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory

/-- The canonical telescope cone comparison for abelian sheaves.
Source: blueprint node order 1719; Stacks Tags 093W, 0949, 0A5L, 090Z
(blueprint: lem-kun-complex-colimit-hocolim).

Proof: (1) Sequential colimits of abelian sheaves are exact; for module sheaves use
`lem-weil-pbc-module-sheaves-colimits-forgetful`, whose faithful exact forgetful functor
preserves colimits and reflects exactness. (2) The finite initial telescope sequences
are split exact: the last summand sections the transition-sum map, and recursive
coordinates identify its kernel with the previous initial sum. This includes the
zero initial sum. (3) Their sequential colimit is degreewise the exact sequence
`0 → B.pt → B.pt → L.pt → 0` with maps `u,q`. (4) Its relation `u ≫ q = 0`
constructs the cone map with unshifted part `q` and shifted part zero. (5) Apply
`lem-pc-cone-short-exact-quasi-iso` to obtain its quasi-isomorphism.
(6) Countable sums are exact as sequential colimits of finite sums; apply
`lem-kun-derived-countable-sums-exact` to identify the actual mapped coprojections.
(7) The localized cone triangle is distinguished and its first map is `1-shift`.
Thus its cone is a homotopy colimit. Localization inverts the comparison; transport
the third vertex along this isomorphism to obtain the displayed distinguished
triangle with second arrow `Q.map q`. This also exhibits `Q.obj L.pt` as a homotopy
colimit. The argument is unbounded and requires no monic transition maps. -/
theorem abelianSheaf_complex_colimit_homotopyColimit
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    (E : ℕ ⥤ CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}) ℤ)
    (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (hL : IsColimit L)
    (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n) :
    ∃ p : mappingCone u ⟶ L.pt,
      mappingCone.inr u ≫ p = q ∧
      (mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0 ∧
      QuasiIso p ∧
      Nonempty (IsColimit
        (Cofan.mk (DerivedCategory.Q.obj B.pt)
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.inj n)))) ∧
      ∃ e : DerivedCategory.Q.obj (mappingCone u) ≅ DerivedCategory.Q.obj L.pt,
        e.hom = DerivedCategory.Q.map p ∧
        DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u) ∈
          distTriang (DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})) ∧
        Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
          (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃) ∈
          distTriang (DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})) ∧
        ∃ h : HasCountableCoproducts (DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})),
          @IsSequentialHomotopyColimit
            (DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj (mappingCone u)) ∧
          @IsSequentialHomotopyColimit
            (DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj L.pt) := by
  sorry

/-- The canonical telescope cone comparison for sheaves of modules.
Source: blueprint node order 1719; Stacks Tags 093W, 0949, 0A5L, 090Z
(blueprint: lem-kun-complex-colimit-hocolim).

Proof: (1) Sequential colimits of abelian sheaves are exact; for module sheaves use
`lem-weil-pbc-module-sheaves-colimits-forgetful`, whose faithful exact forgetful functor
preserves colimits and reflects exactness. (2) The finite initial telescope sequences
are split exact: the last summand sections the transition-sum map, and recursive
coordinates identify its kernel with the previous initial sum. This includes the
zero initial sum. (3) Their sequential colimit is degreewise the exact sequence
`0 → B.pt → B.pt → L.pt → 0` with maps `u,q`. (4) Its relation `u ≫ q = 0`
constructs the cone map with unshifted part `q` and shifted part zero. (5) Apply
`lem-pc-cone-short-exact-quasi-iso` to obtain its quasi-isomorphism.
(6) Countable sums are exact as sequential colimits of finite sums; apply
`lem-kun-derived-countable-sums-exact` to identify the actual mapped coprojections.
(7) The localized cone triangle is distinguished and its first map is `1-shift`.
Thus its cone is a homotopy colimit. Localization inverts the comparison; transport
the third vertex along this isomorphism to obtain the displayed distinguished
triangle with second arrow `Q.map q`. This also exhibits `Q.obj L.pt` as a homotopy
colimit. The argument is unbounded and requires no monic transition maps. -/
theorem moduleSheaf_complex_colimit_homotopyColimit
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (R : Sheaf J.toGrothendieck CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (E : ℕ ⥤ CochainComplex (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (hL : IsColimit L)
    (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n) :
    ∃ p : mappingCone u ⟶ L.pt,
      mappingCone.inr u ≫ p = q ∧
      (mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0 ∧
      QuasiIso p ∧
      Nonempty (IsColimit
        (Cofan.mk (DerivedCategory.Q.obj B.pt)
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.inj n)))) ∧
      ∃ e : DerivedCategory.Q.obj (mappingCone u) ≅ DerivedCategory.Q.obj L.pt,
        e.hom = DerivedCategory.Q.map p ∧
        DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u) ∈
          distTriang (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ∧
        Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
          (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃) ∈
          distTriang (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ∧
        ∃ h : HasCountableCoproducts
            (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R))),
          @IsSequentialHomotopyColimit
            (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj (mappingCone u)) ∧
          @IsSequentialHomotopyColimit
            (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj L.pt) := by
  sorry

end CategoryTheory
