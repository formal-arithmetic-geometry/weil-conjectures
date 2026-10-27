/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.SectionsScalarOrdinaryTower
public import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import all Sheaf.CategoryTheory.ExactDerivedTransformationPasting

/-! # Transport of an ordinary scalar tower through exact derived functors

Source: Stacks 04VG and 06YY; functoriality of localization
(blueprint: lem-weil-exact-scalar-tower-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe z x y v w dS dM
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ScalarTower

variable {I : Type z} [Preorder I]
  (S : I → Type x) (M : I → Type x)
  [∀ i, Category.{v} (S i)] [∀ i, Category.{v} (M i)]
  [∀ i, Abelian (S i)] [∀ i, Abelian (M i)]
  [∀ i, HasDerivedCategory.{dS} (S i)] [∀ i, HasDerivedCategory.{dS} (M i)]
  (T : ∀ i j, i ≤ j → S i ⥤ S j) (t : ∀ i j, i ≤ j → M i ⥤ M j)
  (G : ∀ i, S i ⥤ M i)
  [∀ i j h, (T i j h).Additive]
  [∀ i j h, PreservesFiniteLimits (T i j h)]
  [∀ i j h, PreservesFiniteColimits (T i j h)]
  [∀ i j h, (t i j h).Additive]
  [∀ i j h, PreservesFiniteLimits (t i j h)]
  [∀ i j h, PreservesFiniteColimits (t i j h)]
  [gAdd : ∀ i, (G i).Additive]
  [gLim : ∀ i, PreservesFiniteLimits (G i)]
  [gColim : ∀ i, PreservesFiniteColimits (G i)]
  (TD : ∀ i j, i ≤ j → DerivedCategory (S i) ⥤ DerivedCategory (S j))
  (c : ∀ i j h, (T i j h).mapDerivedCategory ≅ TD i j h)

/-- The exact derived module scalar functors.
Source: Stacks 06YY (blueprint: lem-weil-exact-scalar-tower-transport). -/
abbrev td (i j : I) (h : i ≤ j) := (t i j h).mapDerivedCategory
/-- The exact derived section functors.
Source: Stacks 06YY (blueprint: lem-weil-exact-scalar-tower-transport). -/
abbrev gd (i : I) := (G i).mapDerivedCategory
/-- The counit fixed by the comparison with exact localization.
Source: Stacks 04VG (blueprint: lem-weil-exact-scalar-tower-transport). -/
def sigma (i j : I) (h : i ≤ j) :
    DerivedCategory.Q ⋙ TD i j h ≅
      (T i j h).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q (c i j h).symm ≪≫
    (T i j h).mapDerivedCategoryFactors

/-- The four kinds of descended scalar coherence isomorphisms.
Source: Stacks 04VG (blueprint: lem-weil-exact-scalar-tower-transport). -/
abbrev DerivedMaps := OrdinaryMaps (fun i ↦ DerivedCategory (S i))
  (fun i ↦ DerivedCategory (M i)) TD (td M t)

variable {S M T t G TD c}
  (θ : ∀ i j h, G i ⋙ t i j h ≅ T i j h ⋙ G j)

/-- The exact-derived section comparison transported to the prescribed scalar functor.
Source: Stacks 04VG (blueprint: lem-weil-exact-scalar-tower-transport). -/
def thetaDerived (i j : I) (h : i ≤ j) :
    gd S M G i ⋙ td M t i j h ≅ TD i j h ⋙ gd S M G j :=
  (Functor.mapDerivedCategoryCompIso (G i) (t i j h)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (θ i j h) ≪≫
    Functor.mapDerivedCategoryCompIso (T i j h) (G j) ≪≫
    Functor.isoWhiskerRight (c i j h) (gd S M G j)

variable (O : OrdinaryMaps S M T t)

/-- The four normalizations that determine derived scalar maps.
Source: Stacks 04VG (blueprint: lem-weil-exact-scalar-tower-transport). -/
structure RepresentativeLaws (D : DerivedMaps S M t TD) : Prop where
  representative : ∀ i j k h g (P : CochainComplex (S i) ℤ),
    (TD j k g).map ((sigma S T TD c i j h).hom.app P) ≫
      (sigma S T TD c j k g).hom.app (((T i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (O.sheafComp i j k h g) (.up ℤ)).hom.app P) =
    (D.sheafComp i j k h g).hom.app (DerivedCategory.Q.obj P) ≫
      (sigma S T TD c i k (h.trans g)).hom.app P
  module_representative : ∀ i j k h g (P : CochainComplex (M i) ℤ),
    (D.moduleComp i j k h g).hom.app (DerivedCategory.Q.obj P) ≫
      (t i k (h.trans g)).mapDerivedCategoryFactors.hom.app P =
    (td M t j k g).map ((t i j h).mapDerivedCategoryFactors.hom.app P) ≫
      (t j k g).mapDerivedCategoryFactors.hom.app
        (((t i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (O.moduleComp i j k h g) (.up ℤ)).hom.app P)
  unit_representative : ∀ i (P : CochainComplex (S i) ℤ),
    (D.sheafUnit i).hom.app (DerivedCategory.Q.obj P) =
      (sigma S T TD c i i le_rfl).hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (O.sheafUnit i) (.up ℤ)).hom.app P)
  module_unit_representative : ∀ i (P : CochainComplex (M i) ℤ),
    (D.moduleUnit i).hom.app (DerivedCategory.Q.obj P) =
      (t i i le_rfl).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (O.moduleUnit i) (.up ℤ)).hom.app P)

/-- Normalizations on every cochain representative together with the descended equations.
Source: Stacks 04VG and 06YY (blueprint: lem-weil-exact-scalar-tower-transport). -/
structure DerivedLaws (D : DerivedMaps S M t TD) : Prop where
  representative : ∀ i j k h g (P : CochainComplex (S i) ℤ),
    (TD j k g).map ((sigma S T TD c i j h).hom.app P) ≫
      (sigma S T TD c j k g).hom.app (((T i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (O.sheafComp i j k h g) (.up ℤ)).hom.app P) =
    (D.sheafComp i j k h g).hom.app (DerivedCategory.Q.obj P) ≫
      (sigma S T TD c i k (h.trans g)).hom.app P
  module_representative : ∀ i j k h g (P : CochainComplex (M i) ℤ),
    (D.moduleComp i j k h g).hom.app (DerivedCategory.Q.obj P) ≫
      (t i k (h.trans g)).mapDerivedCategoryFactors.hom.app P =
    (td M t j k g).map ((t i j h).mapDerivedCategoryFactors.hom.app P) ≫
      (t j k g).mapDerivedCategoryFactors.hom.app
        (((t i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (O.moduleComp i j k h g) (.up ℤ)).hom.app P)
  unit_representative : ∀ i (P : CochainComplex (S i) ℤ),
    (D.sheafUnit i).hom.app (DerivedCategory.Q.obj P) =
      (sigma S T TD c i i le_rfl).hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (O.sheafUnit i) (.up ℤ)).hom.app P)
  module_unit_representative : ∀ i (P : CochainComplex (M i) ℤ),
    (D.moduleUnit i).hom.app (DerivedCategory.Q.obj P) =
      (t i i le_rfl).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (O.moduleUnit i) (.up ℤ)).hom.app P)
  coherent : Coherent (gd S M G) (thetaDerived (S := S) (M := M) (T := T) (t := t) (G := G)
    (TD := TD) (c := c) θ) D


/-- Equal ordinary coherence maps give the same normalized derived laws.
Source: substitution of equals (blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem laws_of_ordinary_eq (O' : OrdinaryMaps S M T t) (hO : O' = O)
    (D : DerivedMaps S M t TD)
    (hD : DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O' D) :
    DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O D := by
  subst O'
  exact hD

/-- Substitution of a prescribed counit in the binary representative equation.
Source: substitution of equal morphisms
(blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem representative_counit_iff (D : DerivedMaps S M t TD)
    (ε : ∀ i j (h : i ≤ j) (P : CochainComplex (S i) ℤ),
      (TD i j h).obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj (((T i j h).mapHomologicalComplex (.up ℤ)).obj P))
    (hε : ∀ i j h P, (sigma S T TD c i j h).hom.app P = ε i j h P) :
    (∀ i j k h g (P : CochainComplex (S i) ℤ),
      (TD j k g).map ((sigma S T TD c i j h).hom.app P) ≫
        (sigma S T TD c j k g).hom.app (((T i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (O.sheafComp i j k h g) (.up ℤ)).hom.app P) =
      (D.sheafComp i j k h g).hom.app (DerivedCategory.Q.obj P) ≫
        (sigma S T TD c i k (h.trans g)).hom.app P) ↔
    (∀ i j k h g (P : CochainComplex (S i) ℤ),
      (TD j k g).map (ε i j h P) ≫
        ε j k g (((T i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (O.sheafComp i j k h g) (.up ℤ)).hom.app P) =
      (D.sheafComp i j k h g).hom.app (DerivedCategory.Q.obj P) ≫ ε i k (h.trans g) P) := by
  simp only [hε]

/-- Substitution of a prescribed counit in the identity representative equation.
Source: substitution of equal morphisms
(blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem unit_counit_iff (D : DerivedMaps S M t TD)
    (ε : ∀ i j (h : i ≤ j) (P : CochainComplex (S i) ℤ),
      (TD i j h).obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj (((T i j h).mapHomologicalComplex (.up ℤ)).obj P))
    (hε : ∀ i j h P, (sigma S T TD c i j h).hom.app P = ε i j h P) :
    (∀ i (P : CochainComplex (S i) ℤ),
      (D.sheafUnit i).hom.app (DerivedCategory.Q.obj P) =
        (sigma S T TD c i i le_rfl).hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (O.sheafUnit i) (.up ℤ)).hom.app P)) ↔
    (∀ i (P : CochainComplex (S i) ℤ),
      (D.sheafUnit i).hom.app (DerivedCategory.Q.obj P) = ε i i le_rfl P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (O.sheafUnit i) (.up ℤ)).hom.app P)) := by
  simp only [hε]

section Normalization
variable {C₁ : Type x} {C₂ : Type x} {N₁ : Type y} {N₂ : Type y}
  [Category.{v} C₁] [Category.{v} C₂] [Category.{w} N₁] [Category.{w} N₂]
  [Abelian C₁] [Abelian C₂] [Abelian N₁] [Abelian N₂]
  [HasDerivedCategory.{dS} C₁] [HasDerivedCategory.{dS} C₂]
  [HasDerivedCategory.{dM} N₁] [HasDerivedCategory.{dM} N₂]
  (F F' : C₁ ⥤ N₁) (H H' : C₂ ⥤ N₂)
  (U : C₁ ⥤ C₂) (V : N₁ ⥤ N₂)
  [F.Additive] [F'.Additive] [H.Additive] [H'.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (UD : DerivedCategory C₁ ⥤ DerivedCategory C₂) (cU : U.mapDerivedCategory ≅ UD)

/-- Equality of coefficient identifications preserves the normalized derived comparison.
Source: functoriality of exact localization
(blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem normalizedComparison_heq (hF : F' = F) (hH : H' = H)
    (η : F ⋙ V ≅ U ⋙ H) (η' : F' ⋙ V ≅ U ⋙ H') (hη : HEq η' η) :
    HEq
      ((Functor.mapDerivedCategoryCompIso F' V).symm ≪≫
        Functor.mapDerivedCategoryNatIso η' ≪≫
        Functor.mapDerivedCategoryCompIso U H' ≪≫
        Functor.isoWhiskerRight cU H'.mapDerivedCategory)
      ((Functor.mapDerivedCategoryCompIso F V).symm ≪≫
        Functor.mapDerivedCategoryNatIso η ≪≫
        Functor.mapDerivedCategoryCompIso U H ≪≫
        Functor.isoWhiskerRight cU H.mapDerivedCategory) := by
  subst F'
  subst H'
  cases hη
  rfl
/-- The normalized comparison agrees with any specified localized representative.
Source: functoriality of exact localization
(blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem normalizedComparison_localized_heq (hF : F' = F) (hH : H' = H)
    (η : F ⋙ V ≅ U ⋙ H) (η' : F' ⋙ V ≅ U ⋙ H') (hη : HEq η' η)
    (etaLoc : (F ⋙ V).mapDerivedCategory ≅ (U ⋙ H).mapDerivedCategory)
    (τ : F.mapDerivedCategory ⋙ V.mapDerivedCategory ≅ UD ⋙ H.mapDerivedCategory)
    (hetaLoc : Functor.mapDerivedCategoryNatIso η = etaLoc)
    (hτ : τ = (Functor.mapDerivedCategoryCompIso F V).symm ≪≫ etaLoc ≪≫
      Functor.mapDerivedCategoryCompIso U H ≪≫
      Functor.isoWhiskerRight cU H.mapDerivedCategory) :
    HEq
      ((Functor.mapDerivedCategoryCompIso F' V).symm ≪≫
        Functor.mapDerivedCategoryNatIso η' ≪≫
        Functor.mapDerivedCategoryCompIso U H' ≪≫
        Functor.isoWhiskerRight cU H'.mapDerivedCategory) τ := by
  apply (normalizedComparison_heq F F' H H' U V UD cU hF hH η η' hη).trans
  apply heq_of_eq
  rw [hτ, ← hetaLoc]

end Normalization

section LocalizedComparison
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F H : A ⥤ B) [F.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- A localized comparison is determined by its termwise representative normalization.
Source: Stacks 04VG (blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem localizedComparison_eq (η : F ≅ H)
    (κ : F.mapHomologicalComplex (.up ℤ) ≅ H.mapHomologicalComplex (.up ℤ))
    (hκ : ∀ (P : CochainComplex A ℤ) i, (κ.hom.app P).f i = η.hom.app (P.X i))
    (τ : F.mapDerivedCategory ≅ H.mapDerivedCategory)
    (hτ : ∀ (P : CochainComplex A ℤ),
      τ.hom.app (DerivedCategory.Q.obj P) ≫ H.mapDerivedCategoryFactors.hom.app P =
        F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (κ.hom.app P)) :
    Functor.mapDerivedCategoryNatIso η = τ := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro P
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app P)).mp
  rw [Functor.mapDerivedCategoryNatIso_fac, hτ]
  congr 2
  apply HomologicalComplex.Hom.ext
  funext i
  exact (hκ P i).symm
end LocalizedComparison

private theorem derived_pasting {J : Type*} (C : J → Type x)
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory.{dS} (C i)]
    {i j : J} {P R : ExactDerivedPasting.Word C i j}
    (e f : ExactDerivedPasting.Expression C P R) (h : e.ordinary = f.ordinary) :
    e.derived = f.derived := by
  have cell (a : ExactDerivedPasting.Expression C P R) :
      a.derived = ExactDerivedPasting.Word.cell C a.ordinary := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (C i) (.up ℤ))
    intro K
    apply (cancel_mono ((ExactDerivedPasting.wordFactors C R).hom.app K)).mp
    exact (ExactDerivedPasting.expression_factors C a K).trans
      (ExactDerivedPasting.cell_factors C a.ordinary K).symm
  rw [cell e, cell f, h]

private abbrev towerCategory (p : I ⊕ I) : Type x :=
  match p with
  | .inl i => S i
  | .inr i => M i

@[reducible] private instance towerCategory_category (p : I ⊕ I) :
    Category.{v} (towerCategory (S := S) (M := M) p) :=
  match p with
  | .inl i => inferInstanceAs (Category.{v} (S i))
  | .inr i => inferInstanceAs (Category.{v} (M i))

@[reducible] private instance towerCategory_abelian (p : I ⊕ I) :
    Abelian (towerCategory (S := S) (M := M) p) :=
  match p with
  | .inl i => inferInstanceAs (Abelian (S i))
  | .inr i => inferInstanceAs (Abelian (M i))

@[reducible] private instance towerCategory_derived (p : I ⊕ I) :
    HasDerivedCategory.{dS} (towerCategory (S := S) (M := M) p) :=
  match p with
  | .inl i => inferInstanceAs (HasDerivedCategory.{dS} (S i))
  | .inr i => inferInstanceAs (HasDerivedCategory.{dS} (M i))

private def sheafWord (i j : I) (h : i ≤ j) :
    ExactDerivedPasting.Word (towerCategory (S := S) (M := M)) (Sum.inl i) (Sum.inl j) :=
  .edge (ExactFunctor.of (T i j h))

private def moduleWord (i j : I) (h : i ≤ j) :
    ExactDerivedPasting.Word (towerCategory (S := S) (M := M)) (Sum.inr i) (Sum.inr j) :=
  .edge (ExactFunctor.of (t i j h))

private def sectionsWord (i : I) :
    ExactDerivedPasting.Word (towerCategory (S := S) (M := M)) (Sum.inl i) (Sum.inr i) :=
  .edge (ExactFunctor.of (G i))

private def exactMaps : DerivedMaps S M t (fun i j h ↦ (T i j h).mapDerivedCategory) where
  sheafComp := fun i j k h g ↦ Functor.exactDerivedRestrictionComposition
    (T i j h) (T j k g) (T i k (h.trans g)) (O.sheafComp i j k h g)
  moduleComp := fun i j k h g ↦ Functor.exactDerivedRestrictionComposition
    (t i j h) (t j k g) (t i k (h.trans g)) (O.moduleComp i j k h g)
  sheafUnit := fun i ↦ Functor.exactDerivedRestrictionUnit (T i i le_rfl) (O.sheafUnit i)
  moduleUnit := fun i ↦ Functor.exactDerivedRestrictionUnit (t i i le_rfl) (O.moduleUnit i)

private instance exact_additive {A B : Type x} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] (F : A ⥤ₑ B) : F.obj.Additive :=
  exactFunctor_le_additiveFunctor A B F.obj F.property

private theorem edge_pair_cell {J : Type z} (C : J → Type x)
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory.{dS} (C i)] {i j k n : J}
    (F : C i ⥤ₑ C j) (H : C j ⥤ₑ C n)
    (U : C i ⥤ₑ C k) (V : C k ⥤ₑ C n)
    [F.obj.Additive] [H.obj.Additive] [U.obj.Additive] [V.obj.Additive]
    (η : F.obj ⋙ H.obj ≅ U.obj ⋙ V.obj) :
    ExactDerivedPasting.Word.cell C
      (P := .comp (.edge F) (.edge H)) (R := .comp (.edge U) (.edge V)) η.hom =
      (Functor.mapDerivedCategoryCompIso F.obj H.obj).inv ≫
        (Functor.mapDerivedCategoryNatIso η).hom ≫
        (Functor.mapDerivedCategoryCompIso U.obj V.obj).hom := by
  simp only [ExactDerivedPasting.Word.cell, ExactDerivedPasting.Word.comparison,
    ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl]
  rfl

private theorem pair_edge_cell {J : Type z} (C : J → Type x)
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory.{dS} (C i)] {i j k : J}
    (F : C i ⥤ₑ C j) (H : C j ⥤ₑ C k) (U : C i ⥤ₑ C k)
    [F.obj.Additive] [H.obj.Additive] [U.obj.Additive]
    (η : F.obj ⋙ H.obj ≅ U.obj) :
    ExactDerivedPasting.Word.cell C
      (P := .comp (.edge F) (.edge H)) (R := .edge U) η.hom =
      (Functor.exactDerivedRestrictionComposition F.obj H.obj U.obj η).hom := by
  simp only [ExactDerivedPasting.Word.cell, ExactDerivedPasting.Word.comparison,
    ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl,
    Iso.refl_hom, Category.comp_id]
  rfl

private theorem exact_square (hO : Coherent G θ O) (i j k : I)
    (h : i ≤ j) (g : j ≤ k) :
    ∀ X, ((t j k g).mapDerivedCategory).map
      ((thetaDerived (S := S) (M := M) (T := T) (t := t) (G := G)
        (TD := fun i j h ↦ (T i j h).mapDerivedCategory)
        (c := fun _ _ _ ↦ Iso.refl _) θ i j h).hom.app X) ≫
      (thetaDerived (S := S) (M := M) (T := T) (t := t) (G := G)
        (TD := fun i j h ↦ (T i j h).mapDerivedCategory)
        (c := fun _ _ _ ↦ Iso.refl _) θ j k g).hom.app ((T i j h).mapDerivedCategory.obj X) ≫
      (gd S M G k).map (((exactMaps (T := T) (t := t) O).sheafComp i j k h g).hom.app X) =
      ((exactMaps (T := T) (t := t) O).moduleComp i j k h g).hom.app ((gd S M G i).obj X) ≫
      (thetaDerived (S := S) (M := M) (T := T) (t := t) (G := G)
        (TD := fun i j h ↦ (T i j h).mapDerivedCategory)
        (c := fun _ _ _ ↦ Iso.refl _) θ i k (h.trans g)).hom.app X := by
  let C := towerCategory (S := S) (M := M)
  let U := sheafWord (S := S) (M := M) (T := T)
  let V := moduleWord (S := S) (M := M) (t := t)
  let W := sectionsWord (S := S) (M := M) (G := G)
  let th (i j : I) (h : i ≤ j) : ExactDerivedPasting.Expression C
      (.comp (W i) (V i j h)) (.comp (U i j h) (W j)) := .cell (θ i j h).hom
  let sh (i j k : I) (h : i ≤ j) (g : j ≤ k) : ExactDerivedPasting.Expression C
      (.comp (U i j h) (U j k g)) (U i k (h.trans g)) := .cell (O.sheafComp i j k h g).hom
  let md (i j k : I) (h : i ≤ j) (g : j ≤ k) : ExactDerivedPasting.Expression C
      (.comp (V i j h) (V j k g)) (V i k (h.trans g)) := .cell (O.moduleComp i j k h g).hom
  let e := ExactDerivedPasting.Expression.vcomp
    (.vcomp (.vcomp (.vcomp (.output (th i j h) (V j k g))
      (.assoc (U i j h) (W j) (V j k g))) (.input (U i j h) (th j k g)))
      (.assocInv (U i j h) (U j k g) (W k))) (.output (sh i j k h g) (W k))
  let f := ExactDerivedPasting.Expression.vcomp
    (.vcomp (.assoc (W i) (V i j h) (V j k g)) (.input (W i) (md i j k h g)))
      (th i k (h.trans g))
  have he : e.ordinary = f.ordinary := by
    apply NatTrans.ext
    funext X
    simpa [e, f, th, sh, md, U, V, W, sheafWord, moduleWord, sectionsWord,
      ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Expression.ordinary,
      Category.assoc] using
      hO.square i j k h g X
  have hd := derived_pasting C e f he
  intro X
  have hx := congrArg (fun α ↦ α.app X) hd
  dsimp only [e, f, ExactDerivedPasting.Expression.derived] at hx
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.assoc] at hx
  dsimp only [th, sh, md, ExactDerivedPasting.Expression.derived] at hx
  simp only [U, V, W, sheafWord, moduleWord, sectionsWord] at hx
  erw [edge_pair_cell, edge_pair_cell, pair_edge_cell, pair_edge_cell,
    edge_pair_cell] at hx
  dsimp only [ExactDerivedPasting.Word.derived, ExactDerivedPasting.Word.ordinary] at hx
  simp only [ExactFunctor.of] at hx
  dsimp only [ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    Functor.comp_obj] at hx
  try simp only [Category.comp_id] at hx
  simpa only [thetaDerived, exactMaps, gd, td, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_refl, Iso.refl_hom, NatTrans.comp_app,
    Category.comp_id, Category.id_comp, Category.assoc] using hx

private theorem exact_tower {J : Type z} (C : J → Type x) [Preorder J]
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory.{dS} (C i)]
    (U : ∀ i j, i ≤ j → C i ⥤ₑ C j)
    [∀ i j h, (U i j h).obj.Additive]
    (α : ∀ i j k (h : i ≤ j) (g : j ≤ k),
      (U i j h).obj ⋙ (U j k g).obj ≅ (U i k (h.trans g)).obj)
    (hn : ∀ i j k n h g q (X : C i),
      (U k n q).obj.map ((α i j k h g).hom.app X) ≫
        (α i k n (h.trans g) q).hom.app X =
      (α j k n g q).hom.app ((U i j h).obj.obj X) ≫
        (α i j n h (g.trans q)).hom.app X)
    (i j k n : J) (h : i ≤ j) (g : j ≤ k) (q : k ≤ n)
    (X : DerivedCategory (C i)) :
    (U k n q).obj.mapDerivedCategory.map
        ((Functor.exactDerivedRestrictionComposition _ _ _ (α i j k h g)).hom.app X) ≫
      (Functor.exactDerivedRestrictionComposition _ _ _ (α i k n (h.trans g) q)).hom.app X =
    (Functor.exactDerivedRestrictionComposition _ _ _ (α j k n g q)).hom.app
        ((U i j h).obj.mapDerivedCategory.obj X) ≫
      (Functor.exactDerivedRestrictionComposition _ _ _ (α i j n h (g.trans q))).hom.app X := by
  let W (i j : J) (h : i ≤ j) : ExactDerivedPasting.Word C i j := .edge (U i j h)
  let a (i j k : J) (h : i ≤ j) (g : j ≤ k) : ExactDerivedPasting.Expression C
      (.comp (W i j h) (W j k g)) (W i k (h.trans g)) := .cell (α i j k h g).hom
  let e := ExactDerivedPasting.Expression.vcomp
    (.output (a i j k h g) (W k n q)) (a i k n (h.trans g) q)
  let f := ExactDerivedPasting.Expression.vcomp
    (.vcomp (.assoc (W i j h) (W j k g) (W k n q))
      (.input (W i j h) (a j k n g q))) (a i j n h (g.trans q))
  have he : e.ordinary = f.ordinary := by
    apply NatTrans.ext
    funext Y
    simpa [e, f, a, W, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Expression.ordinary] using hn i j k n h g q Y
  have hx := congrArg (fun η ↦ η.app X) (derived_pasting C e f he)
  dsimp only [e, f, ExactDerivedPasting.Expression.derived] at hx
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at hx
  dsimp only [a, ExactDerivedPasting.Expression.derived, W] at hx
  erw [pair_edge_cell, pair_edge_cell, pair_edge_cell, pair_edge_cell] at hx
  simpa only [ExactDerivedPasting.Word.derived, ExactDerivedPasting.Word.ordinary,
    Category.id_comp, Category.assoc] using hx

private theorem edge_nil_cell {J : Type z} (C : J → Type x)
    [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory.{dS} (C i)] (i : J)
    (F : C i ⥤ₑ C i) [F.obj.Additive] (η : F.obj ≅ 𝟭 (C i)) :
    ExactDerivedPasting.Word.cell C (P := .edge F) (R := .nil i) η.hom =
      (Functor.exactDerivedRestrictionUnit F.obj η).hom := by
  simp only [ExactDerivedPasting.Word.cell, ExactDerivedPasting.Word.comparison,
    ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    Iso.refl_inv, Category.id_comp]
  rfl

private theorem exact_unit_square (hO : Coherent G θ O) (i : I)
    (X : DerivedCategory (S i)) :
    (thetaDerived (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := fun i j h ↦ (T i j h).mapDerivedCategory)
      (c := fun _ _ _ ↦ Iso.refl _) θ i i le_rfl).hom.app X ≫
      (gd S M G i).map (((exactMaps (T := T) (t := t) O).sheafUnit i).hom.app X) =
    ((exactMaps (T := T) (t := t) O).moduleUnit i).hom.app ((gd S M G i).obj X) := by
  let C := towerCategory (S := S) (M := M)
  let U := sheafWord (S := S) (M := M) (T := T)
  let V := moduleWord (S := S) (M := M) (t := t)
  let W := sectionsWord (S := S) (M := M) (G := G)
  let th : ExactDerivedPasting.Expression C (.comp (W i) (V i i le_rfl))
      (.comp (U i i le_rfl) (W i)) := .cell (θ i i le_rfl).hom
  let sh : ExactDerivedPasting.Expression C (U i i le_rfl) (.nil (Sum.inl i)) :=
    .cell (O.sheafUnit i).hom
  let md : ExactDerivedPasting.Expression C (V i i le_rfl) (.nil (Sum.inr i)) :=
    .cell (O.moduleUnit i).hom
  let e := ExactDerivedPasting.Expression.vcomp
    (.vcomp th (.output sh (W i))) (.leftUnit (W i))
  let f := ExactDerivedPasting.Expression.vcomp (.input (W i) md) (.rightUnit (W i))
  have he : e.ordinary = f.ordinary := by
    apply NatTrans.ext
    funext Y
    simpa [e, f, th, sh, md, U, V, W, sheafWord, moduleWord, sectionsWord,
      ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Expression.ordinary] using hO.unit i Y
  have hx := congrArg (fun η ↦ η.app X) (derived_pasting C e f he)
  dsimp only [e, f, ExactDerivedPasting.Expression.derived] at hx
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at hx
  dsimp only [th, sh, md, ExactDerivedPasting.Expression.derived, U, V, W,
    sheafWord, moduleWord, sectionsWord] at hx
  erw [edge_pair_cell, edge_nil_cell, edge_nil_cell] at hx
  simp only [ExactFunctor.of] at hx
  dsimp only [ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    Functor.comp_obj] at hx
  try simp only [Category.comp_id] at hx
  let aa := ((Functor.mapDerivedCategoryCompIso (G i) (t i i le_rfl)).inv.app X ≫
    (Functor.mapDerivedCategoryNatIso (θ i i le_rfl)).hom.app X ≫
    (Functor.mapDerivedCategoryCompIso (T i i le_rfl) (G i)).hom.app X ≫
    (G i).mapDerivedCategory.map
      ((Functor.exactDerivedRestrictionUnit (T i i le_rfl) (O.sheafUnit i)).hom.app X))
  let bb := (Functor.exactDerivedRestrictionUnit (t i i le_rfl)
    (O.moduleUnit i)).hom.app ((G i).mapDerivedCategory.obj X)
  simp only [NatTrans.comp_app, Category.assoc] at hx
  have hab : aa = bb := by
    apply (cancel_mono (𝟙 ((G i).mapDerivedCategory.obj X))).mp
    simpa only [aa, bb, Category.assoc] using hx
  simpa only [aa, bb, thetaDerived, exactMaps, gd, td, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_refl, Iso.refl_hom, NatTrans.comp_app, Category.comp_id,
    Category.assoc] using hab


private def transportedComp (i j k : I) (h : i ≤ j) (g : j ≤ k) :
    TD i j h ⋙ TD j k g ≅ TD i k (h.trans g) :=
  Functor.isoWhiskerRight (c i j h).symm (TD j k g) ≪≫
    Functor.isoWhiskerLeft (T i j h).mapDerivedCategory (c j k g).symm ≪≫
    Functor.exactDerivedRestrictionComposition (T i j h) (T j k g)
      (T i k (h.trans g)) (O.sheafComp i j k h g) ≪≫ c i k (h.trans g)

private def transportedUnit (i : I) : TD i i le_rfl ≅ 𝟭 (DerivedCategory (S i)) :=
  (c i i le_rfl).symm ≪≫
    Functor.exactDerivedRestrictionUnit (T i i le_rfl) (O.sheafUnit i)

private def transportedMaps : DerivedMaps S M t TD where
  sheafComp := fun i j k h g ↦ transportedComp (T := T) (TD := TD) (c := c) O i j k h g
  moduleComp := fun i j k h g ↦ Functor.exactDerivedRestrictionComposition
    (t i j h) (t j k g) (t i k (h.trans g)) (O.moduleComp i j k h g)
  sheafUnit := fun i ↦ transportedUnit (T := T) (TD := TD) (c := c) O i
  moduleUnit := fun i ↦ Functor.exactDerivedRestrictionUnit (t i i le_rfl) (O.moduleUnit i)

private theorem transported_sheaf_rep (i j k : I) (h : i ≤ j) (g : j ≤ k)
    (P : CochainComplex (S i) ℤ) :
    ((transportedMaps (T := T) (t := t) (TD := TD) (c := c) O).sheafComp i j k h g).hom.app
        (DerivedCategory.Q.obj P) ≫ (sigma S T TD c i k (h.trans g)).hom.app P =
      (TD j k g).map ((sigma S T TD c i j h).hom.app P) ≫
        (sigma S T TD c j k g).hom.app
          (((T i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (O.sheafComp i j k h g) (.up ℤ)).hom.app P) := by
  dsimp only [transportedMaps, transportedComp, sigma, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [Functor.exactDerivedRestrictionComposition_hom_factors]
  rw [← (c j k g).inv.naturality_assoc]
  rfl

private theorem transported_module_rep (i j k : I) (h : i ≤ j) (g : j ≤ k)
    (P : CochainComplex (M i) ℤ) :
    ((transportedMaps (T := T) (t := t) (TD := TD) (c := c) O).moduleComp i j k h g).hom.app
        (DerivedCategory.Q.obj P) ≫ (t i k (h.trans g)).mapDerivedCategoryFactors.hom.app P =
      (td M t j k g).map ((t i j h).mapDerivedCategoryFactors.hom.app P) ≫
        (t j k g).mapDerivedCategoryFactors.hom.app
          (((t i j h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (O.moduleComp i j k h g) (.up ℤ)).hom.app P) :=
  Functor.exactDerivedRestrictionComposition_hom_factors _ _ _ _ P

private theorem exact_unit_rep {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (R : A ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (η : R ≅ 𝟭 A) (P : CochainComplex A ℤ) :
    (Functor.exactDerivedRestrictionUnit R η).hom.app (DerivedCategory.Q.obj P) =
      R.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app P) := by
  dsimp only [Functor.exactDerivedRestrictionUnit, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, Functor.mapDerivedCategoryNatIso_fac]
  rfl

private theorem representatives_unique (D E : DerivedMaps S M t TD)
    (hD : RepresentativeLaws (S := S) (M := M) (T := T) (t := t) (TD := TD) (c := c) O D)
    (hE : RepresentativeLaws (S := S) (M := M) (T := T) (t := t)
      (TD := TD) (c := c) O E) : D = E := by
  have hs : D.sheafComp = E.sheafComp := by
    funext i j k h g
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (S i) (.up ℤ))
    intro P
    apply (cancel_mono ((sigma S T TD c i k (h.trans g)).hom.app P)).mp
    exact (hD.representative i j k h g P).symm.trans (hE.representative i j k h g P)
  have hm : D.moduleComp = E.moduleComp := by
    funext i j k h g
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (M i) (.up ℤ))
    intro P
    apply (cancel_mono ((t i k (h.trans g)).mapDerivedCategoryFactors.hom.app P)).mp
    exact (hD.module_representative i j k h g P).trans
      (hE.module_representative i j k h g P).symm
  have hu : D.sheafUnit = E.sheafUnit := by
    funext i
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (S i) (.up ℤ))
    intro P
    exact (hD.unit_representative i P).trans (hE.unit_representative i P).symm
  have hv : D.moduleUnit = E.moduleUnit := by
    funext i
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (M i) (.up ℤ))
    intro P
    exact (hD.module_unit_representative i P).trans
      (hE.module_unit_representative i P).symm
  cases D
  cases E
  congr


private theorem derived_unique (D E : DerivedMaps S M t TD)
    (hD : DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O D)
    (hE : DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O E) : D = E := by
  have hs : D.sheafComp = E.sheafComp := by
    funext i j k h g
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (S i) (.up ℤ))
    intro P
    apply (cancel_mono ((sigma S T TD c i k (h.trans g)).hom.app P)).mp
    exact (hD.representative i j k h g P).symm.trans (hE.representative i j k h g P)
  have hm : D.moduleComp = E.moduleComp := by
    funext i j k h g
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (M i) (.up ℤ))
    intro P
    apply (cancel_mono ((t i k (h.trans g)).mapDerivedCategoryFactors.hom.app P)).mp
    exact (hD.module_representative i j k h g P).trans
      (hE.module_representative i j k h g P).symm
  have hu : D.sheafUnit = E.sheafUnit := by
    funext i
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (S i) (.up ℤ))
    intro P
    exact (hD.unit_representative i P).trans (hE.unit_representative i P).symm
  have hv : D.moduleUnit = E.moduleUnit := by
    funext i
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (M i) (.up ℤ))
    intro P
    exact (hD.module_unit_representative i P).trans
      (hE.module_unit_representative i P).symm
  cases D
  cases E
  congr

/-- Equal ordinary maps and normalized representatives determine equal derived maps.
Source: equality substitution and full faithfulness of localization
(blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem derived_unique_of_ordinary_eq (O' : OrdinaryMaps S M T t) (hO : O' = O)
    (D E : DerivedMaps S M t TD)
    (hD : DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O' D)
    (hE : DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O E) : D = E := by
  subst O'
  exact derived_unique θ O D E hD hE

private theorem transported_sheaf_unit_rep (i : I) (P : CochainComplex (S i) ℤ) :
    ((transportedMaps (T := T) (t := t) (TD := TD) (c := c) O).sheafUnit i).hom.app
        (DerivedCategory.Q.obj P) = (sigma S T TD c i i le_rfl).hom.app P ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (O.sheafUnit i) (.up ℤ)).hom.app P) := by
  dsimp only [transportedMaps, transportedUnit, sigma, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rw [exact_unit_rep]
  exact (Category.assoc _ _ _).symm

private theorem transported_coherent (hO : Coherent G θ O) :
    Coherent (gd S M G) (thetaDerived (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ)
      (transportedMaps (T := T) (t := t) (TD := TD) (c := c) O) := by
  constructor
  · intro i j k h g X
    have hx := exact_square θ O hO i j k h g X
    dsimp only [thetaDerived, transportedMaps, transportedComp, gd, td,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    let β := (Functor.mapDerivedCategoryCompIso (G j) (t j k g)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (θ j k g) ≪≫
      Functor.mapDerivedCategoryCompIso (T j k g) (G k)
    have hc := (c j k g).hom.naturality ((c i j h).inv.app X)
    try dsimp only [Functor.comp_map] at hc
    rw [← (G k).mapDerivedCategory.map_comp_assoc, ← hc]
    simp only [Functor.map_comp, Category.assoc]
    have hnat := β.hom.naturality ((c i j h).inv.app X)
    dsimp only [Functor.comp_map, β, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app] at hnat
    simp only [Category.assoc] at hnat
    rw [← reassoc_of% hnat]
    simp only [← Functor.map_comp_assoc]
    have hjcancel : (G j).mapDerivedCategory.map ((c i j h).hom.app X) ≫
        (G j).mapDerivedCategory.map ((c i j h).inv.app X) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [hjcancel]
    simp only [Iso.hom_inv_id_app_assoc]
    simp only [Functor.map_comp, Category.assoc]
    erw [(t j k g).mapDerivedCategory.map_id]
    simp only [Category.id_comp]
    simpa only [thetaDerived, exactMaps, gd, td, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_refl, Iso.refl_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.map_id, Category.id_comp,
      Category.comp_id, Category.assoc] using
      congrArg (fun v ↦ v ≫ (G k).mapDerivedCategory.map
        ((c i k (h.trans g)).hom.app X)) hx
  · intro i X
    have hx := exact_unit_square θ O hO i X
    dsimp only [thetaDerived, transportedMaps, transportedUnit, gd, td,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    simpa only [thetaDerived, exactMaps, gd, td, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_refl, Iso.refl_hom, NatTrans.id_app,
      NatTrans.comp_app, Category.comp_id, Category.assoc] using hx
  · intro i j k n h g q X
    have hx := exact_tower S (fun i j h ↦ ExactFunctor.of (T i j h))
      O.sheafComp hO.sheaf_tower i j k n h g q X
    dsimp only [transportedMaps, transportedComp, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    have hc := (c j n (g.trans q)).hom.naturality ((c i j h).inv.app X)
    try dsimp only [Functor.comp_map] at hc
    rw [← reassoc_of% hc]
    simp only [Iso.hom_inv_id_app_assoc]
    have ha := (Functor.exactDerivedRestrictionComposition
      (T j k g) (T k n q) (T j n (g.trans q))
      (O.sheafComp j k n g q)).hom.naturality ((c i j h).inv.app X)
    try dsimp only [Functor.comp_map] at ha
    rw [← reassoc_of% ha]
    have hj := (c k n q).inv.naturality
      ((T j k g).mapDerivedCategory.map ((c i j h).inv.app X))
    try dsimp only [Functor.comp_map] at hj
    rw [← reassoc_of% hj]
    rw [← (TD k n q).map_comp_assoc]
    rw [(c j k g).inv.naturality]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (c k n q).inv.naturality
      ((Functor.exactDerivedRestrictionComposition
        (T i j h) (T j k g) (T i k (h.trans g))
        (O.sheafComp i j k h g)).hom.app X)
    try dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    simp only [← Functor.map_comp_assoc]
    dsimp only [ExactFunctor.of] at hx
    simpa only [Category.assoc] using congrArg (fun v ↦
      (TD k n q).map ((c j k g).inv.app ((TD i j h).obj X) ≫
        (T j k g).mapDerivedCategory.map ((c i j h).inv.app X)) ≫
      (c k n q).inv.app ((T j k g).mapDerivedCategory.obj
        ((T i j h).mapDerivedCategory.obj X)) ≫ v ≫
      (c i n (h.trans (g.trans q))).hom.app X) hx
  · intro i j k n h g q X
    exact exact_tower M (fun i j h ↦ ExactFunctor.of (t i j h))
      O.moduleComp hO.module_tower i j k n h g q X

/-- Exact localization transports all scalar-tower equations, with unique normalized maps.
Source: Stacks 04VG and 06YY; the localization part of
lem-weil-sections-scalar-derived-transport, proof steps 5--8.
(blueprint: lem-weil-exact-scalar-tower-transport).

Proof: localize each ordinary natural isomorphism termwise. For two-edge words use
inverse source compositor, localized isomorphism, then target compositor. Conjugate
by c at each sheaf edge. For units use the exact-derived identity comparison. The
factorization equations of these compositors give all four displayed representative
equations; naturality moves the intervening factors through the edge maps and the
inverse comparisons cancel. Apply exact-derived-transformation-pasting to the ordinary
square, unit, and both four-stage equations. Conjugation preserves these equations,
and thetaDerived is precisely the conjugated localized theta. To prove uniqueness,
precompose each transformation with Q, use its representative equation and cancel
the invertible sigma or exact module factor. Full faithfulness of precomposition
with localization gives equality of hom transformations; an isomorphism is determined
by its hom. This proves uniqueness simultaneously for the four families. -/
theorem exact_transport (_hO : Coherent G θ O) :
    ∃! D : DerivedMaps S M t TD, DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O D := by
  let D := transportedMaps (T := T) (t := t) (TD := TD) (c := c) O
  have hD : DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
      (TD := TD) (c := c) θ O D := by
    refine ⟨?_, ?_, ?_, ?_, transported_coherent θ O _hO⟩
    · intro i j k h g P
      exact (transported_sheaf_rep O i j k h g P).symm
    · exact transported_module_rep O
    · exact transported_sheaf_unit_rep O
    · intro i P
      exact exact_unit_rep _ _ P
  exact ⟨D, hD, fun E hE ↦ derived_unique θ O E D hE hD⟩

/-- Exact transport with uniqueness from the four representative equations.
Source: full faithfulness of localization
(blueprint: lem-weil-exact-scalar-tower-transport). -/
theorem exact_transport_unique (hO : Coherent G θ O) :
    ∃ D : DerivedMaps S M t TD,
      DerivedLaws (S := S) (M := M) (T := T) (t := t) (G := G)
        (TD := TD) (c := c) θ O D ∧
      ∀ (O' : OrdinaryMaps S M T t), O' = O →
        ∀ (E : DerivedMaps S M t TD),
          RepresentativeLaws (S := S) (M := M) (T := T) (t := t)
            (TD := TD) (c := c) O' E → E = D := by
  obtain ⟨D, hD, _⟩ := exact_transport θ O hO
  refine ⟨D, hD, ?_⟩
  intro O' he E hE
  subst O'
  exact representatives_unique O E D hE
    ⟨hD.representative, hD.module_representative,
      hD.unit_representative, hD.module_unit_representative⟩

end CategoryTheory.ScalarTower
