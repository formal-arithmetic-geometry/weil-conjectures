/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion
import Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue
import WeilConjectures.AlgebraicGeometry.DerivedOpenGluingObjects

/-! # Extending derived descent solutions across two open unions

Source: Stacks Project, Cohomology, Tags 0D67, 0D69, 0D6A and 0D6C
(blueprint: lem-trf-derived-basis-binary-extension).

The structures below package the system and solution explicitly defined in the node.
The localized open-site module categories are the same as in the shared basis-descent
statements, canonically equivalent to module sheaves on the open subschemes.
All nested restrictions use the shared canonical comparison isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry
namespace DerivedBasisBinary

variable (X : Scheme.{u})
  [∀ U : X.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

/-- The system of local objects, normalized transitions and their cocycle.
Source: Stacks Project, Cohomology, Situation 0D67
(blueprint: lem-trf-derived-basis-binary-extension).
The identity normalization is the sectionwise identity, localized to the derived category.
It is written explicitly to avoid importing the downstream BBD descent theorem. -/
structure System (B : Set X.Opens) where
  K : ∀ U : {U : X.Opens // U ∈ B},
    DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U.val))
  rho : ∀ (U V : {U : X.Opens // U ∈ B}) (h : V.val ≤ U.val),
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE h)).mapDerivedCategory.obj (K U) ≅ K V
  rho_id : ∀ U : {U : X.Opens // U ∈ B},
    (rho U U le_rfl).hom =
      (Functor.mapDerivedCategoryNatIso
        (NatIso.ofComponents
          (F := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (le_refl U.val)))
          (G := 𝟭 (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U.val)))
          (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
            (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)))) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (K U)
  rho_comp : ∀ (U V T : {U : X.Opens // U ∈ B})
      (hVU : V.val ≤ U.val) (hTV : T.val ≤ V.val),
    (derivedModuleOpenMapCompIso X (homOfLE hTV) (homOfLE hVU)).inv.app (K U) ≫
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hTV)).mapDerivedCategory.map (rho U V hVU).hom ≫
      (rho V T hTV).hom = (rho U T (hTV.trans hVU)).hom

/-- A solution on an open: its object, every original-family identification, and every
inclusion equation. The indexing includes members crossing both pieces of a binary union.
Source: Stacks Project, Cohomology, Tags 0D67, 0D6A and 0D6C
(blueprint: lem-trf-derived-basis-binary-extension). -/
structure Solution {B : Set X.Opens} (D : System X B) (O : X.Opens) where
  F : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))
  s : ∀ (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ O),
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE hU)).mapDerivedCategory.obj F ≅ D.K U
  compatible : ∀ (U V : {U : X.Opens // U ∈ B})
      (hU : U.val ≤ O) (hVU : V.val ≤ U.val),
    (derivedModuleOpenMapCompIso X (homOfLE hVU) (homOfLE hU)).inv.app F ≫
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU)).mapDerivedCategory.map (s U hU).hom ≫
      (D.rho U V hVU).hom = (s V (hVU.trans hU)).hom

/-- Restrict a map on a common open and normalize both iterated restrictions.
Source: Stacks Project, Cohomology, Remark 0D69, nested restriction convention
(blueprint: lem-trf-derived-basis-binary-extension).
This is the actual functorial restriction conjugated by the canonical comparisons. -/
def restrictHom {O₁ O₂ W V : X.Opens} (h₁ : W ≤ O₁) (h₂ : W ≤ O₂) (hV : V ≤ W)
    (A : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O₁)))
    (B : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O₂)))
    (f : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE h₁)).mapDerivedCategory.obj A ⟶
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE h₂)).mapDerivedCategory.obj B) :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hV.trans h₁))).mapDerivedCategory.obj A ⟶
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hV.trans h₂))).mapDerivedCategory.obj B :=
  (derivedModuleOpenMapCompIso X (homOfLE hV) (homOfLE h₁)).inv.app A ≫
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE hV)).mapDerivedCategory.map f ≫
    (derivedModuleOpenMapCompIso X (homOfLE hV) (homOfLE h₂)).hom.app B

/-- The basiswise characterization of an overlap comparison between two solutions.
Source: Stacks Project, Cohomology, Remark 0D69
(blueprint: lem-trf-derived-basis-binary-extension). -/
def IsComparison {B : Set X.Opens} {D : System X B} {O₁ O₂ : X.Opens}
    (S₁ : Solution X D O₁) (S₂ : Solution X D O₂)
    (c : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_left : O₁ ⊓ O₂ ≤ O₁))).mapDerivedCategory.obj S₁.F ≅
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (inf_le_right : O₁ ⊓ O₂ ≤ O₂))).mapDerivedCategory.obj S₂.F) : Prop :=
  ∀ (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ O₁ ⊓ O₂),
    restrictHom X inf_le_left inf_le_right hU S₁.F S₂.F c.hom ≫
      (S₂.s U (hU.trans inf_le_right)).hom = (S₁.s U (hU.trans inf_le_left)).hom

end DerivedBasisBinary

open DerivedBasisBinary

/-- Two supplied derived descent solutions extend across their union, with a unique
basis-compatible overlap comparison, its triple cocycle, and every crossing structure map.
Source: Stacks Project, Cohomology, Tags 0D69, 0D6A and 0D6C
(blueprint: lem-trf-derived-basis-binary-extension).

Proof:
1. The intersection-refinement hypothesis implies that every intersection of unions
   of B is again a union of B. Thus the subfamilies on the overlap and on the triple
   overlap cover and refine intersections, including the empty case.
2. On a basis member V of the overlap, compare the supplied solutions by
   s2,V inverse composed with s1,V. Their inclusion equations make these maps
   compatible. Both local objects identify with K_V, so all four cross negative
   Hom groups vanish. Apply lem-trf-derived-basis-local-hom-glue to these maps and
   their inverses. Its injectivity proves the composites are identities and gives
   uniqueness of the resulting isomorphism c12.
3. On a triple overlap the local formulas for c23 composed with c12 cancel the
   middle identification and agree with c13. The same Hom injectivity proves the
   cocycle, with the canonical iterated-restriction comparisons.
4. Apply lem-sc-derived-open-gluing-objects on O1 union O2 to c12. This produces
   an object F and isomorphisms f1,f2 with the prescribed overlap equation.
5. For any U in B inside the union, cover U by members V of B contained in U
   and in one of the two pieces. This family covers U and refines intersections.
   Set tau_V = sj,V composed with fj restricted to V. Steps 2 and 4 show independence
   of the piece; the original solution equations show inclusion compatibility.
   The maps b_V = rho_V^U inverse composed with tau_V are compatible isomorphisms
   between F restricted to V and K_U restricted to V, by the rho cocycle.
6. Apply lem-trf-derived-basis-local-hom-glue on U to the b_V and their inverses.
   Locally both objects identify with K_V, giving negative cross Hom vanishing.
   Hom injectivity makes the glued maps inverse, producing s_U for every U,
   including those contained in neither piece.
7. If U is contained in a piece, the original formula sj,U composed with fj has
   the same restrictions, so injectivity gives the extension equation. For T inside U,
   the covering family for T lies in that for U. After restricting to a member V,
   the rho cocycle identifies rho_T^U composed with s_U with s_T. Cancel rho_V^T
   and apply Hom injectivity on T to prove every solution inclusion equation.
   Empty opens use the empty-cover Hom clause and unrestricted object gluing;
   no quasi-compactness or boundedness is used. -/
theorem derived_basis_binary_extension
    (X : Scheme.{u})
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (B : Set X.Opens) (hcover : sSup B = ⊤)
    (hrefine : ∀ U ∈ B, ∀ V ∈ B,
      sSup {T : X.Opens | T ∈ B ∧ T ≤ U ⊓ V} = U ⊓ V)
    (D : System X B)
    (hnegative : ∀ (U : {U : X.Opens // U ∈ B}) (i : ℤ), i < 0 →
      Subsingleton (D.K U ⟶ (D.K U)⟦i⟧))
    (O₁ O₂ : X.Opens)
    (hO₁ : sSup {U : X.Opens | U ∈ B ∧ U ≤ O₁} = O₁)
    (hO₂ : sSup {U : X.Opens | U ∈ B ∧ U ≤ O₂} = O₂)
    (S₁ : Solution X D O₁) (S₂ : Solution X D O₂) :
    ∃ c₁₂ : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE (inf_le_left : O₁ ⊓ O₂ ≤ O₁))).mapDerivedCategory.obj S₁.F ≅
        (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE (inf_le_right : O₁ ⊓ O₂ ≤ O₂))).mapDerivedCategory.obj S₂.F,
      IsComparison X S₁ S₂ c₁₂ ∧
      (∀ c, IsComparison X S₁ S₂ c → c = c₁₂) ∧
      (∀ (O₃ : X.Opens), sSup {U : X.Opens | U ∈ B ∧ U ≤ O₃} = O₃ →
        ∀ (S₃ : Solution X D O₃)
          (c₁₃ : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE (inf_le_left : O₁ ⊓ O₃ ≤ O₁))).mapDerivedCategory.obj S₁.F ≅
            (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE (inf_le_right : O₁ ⊓ O₃ ≤ O₃))).mapDerivedCategory.obj S₃.F)
          (c₂₃ : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE (inf_le_left : O₂ ⊓ O₃ ≤ O₂))).mapDerivedCategory.obj S₂.F ≅
            (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE (inf_le_right : O₂ ⊓ O₃ ≤ O₃))).mapDerivedCategory.obj S₃.F),
          IsComparison X S₁ S₃ c₁₃ → IsComparison X S₂ S₃ c₂₃ →
          restrictHom X inf_le_left inf_le_right
              (le_inf (inf_le_left.trans inf_le_left) inf_le_right : O₁ ⊓ O₂ ⊓ O₃ ≤ O₁ ⊓ O₃)
              S₁.F S₃.F c₁₃.hom =
            restrictHom X inf_le_left inf_le_right
                (inf_le_left : O₁ ⊓ O₂ ⊓ O₃ ≤ O₁ ⊓ O₂) S₁.F S₂.F c₁₂.hom ≫
              restrictHom X inf_le_left inf_le_right
                (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
                  O₁ ⊓ O₂ ⊓ O₃ ≤ O₂ ⊓ O₃) S₂.F S₃.F c₂₃.hom) ∧
      ∃ (S : Solution X D (O₁ ⊔ O₂))
        (f₁ : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂))).mapDerivedCategory.obj S.F ≅ S₁.F)
        (f₂ : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂))).mapDerivedCategory.obj S.F ≅ S₂.F),
        ((derivedModuleOpenMapCompIso X (homOfLE inf_le_left)
            (homOfLE le_sup_left)).inv.app S.F ≫
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE inf_le_left)).mapDerivedCategory.map f₁.hom ≫ c₁₂.hom =
          (derivedModuleOpenMapCompIso X (homOfLE inf_le_right)
            (homOfLE le_sup_right)).inv.app S.F ≫
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE inf_le_right)).mapDerivedCategory.map f₂.hom) ∧
        (∀ (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ O₁),
          (S.s U (hU.trans le_sup_left)).hom =
            (derivedModuleOpenMapCompIso X (homOfLE hU)
              (homOfLE le_sup_left)).inv.app S.F ≫
            (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE hU)).mapDerivedCategory.map f₁.hom ≫ (S₁.s U hU).hom) ∧
        (∀ (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ O₂),
          (S.s U (hU.trans le_sup_right)).hom =
            (derivedModuleOpenMapCompIso X (homOfLE hU)
              (homOfLE le_sup_right)).inv.app S.F ≫
            (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE hU)).mapDerivedCategory.map f₂.hom ≫ (S₂.s U hU).hom) := by
  sorry

end AlgebraicGeometry
