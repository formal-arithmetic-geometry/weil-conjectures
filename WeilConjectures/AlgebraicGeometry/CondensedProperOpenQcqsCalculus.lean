/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.CondensedIsomorphismSquareExchange
import WeilConjectures.AlgebraicGeometry.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso

/-! # Shift compatibility and image triangles of normalized condensed comparisons

Source: Stacks Project, more-etale.tex Tags 0F7B, 0F7F and 0F7J, and derived.tex
Tags 015F, 05SU and 0A8D
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

/-- The components of the specified transformation give a morphism of the two image
triangles, and both image triangles are distinguished. This packages the last clause,
including the connecting arrow, without choosing a different transformation.
Source: Stacks Tags 0145 and 014Y
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus). -/
def ImageTriangleCompatibility
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ] (τ : F ⟶ H) : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    F.mapTriangle.obj T ∈ distTriang E ∧ H.mapTriangle.obj T ∈ distTriang E ∧
      ∃ φ : F.mapTriangle.obj T ⟶ H.mapTriangle.obj T,
        φ.hom₁ = τ.app T.obj₁ ∧ φ.hom₂ = τ.app T.obj₂ ∧ φ.hom₃ = τ.app T.obj₃

/-- Compatibility with every canonical integer shift and with image distinguished
triangles, also for the unique inverse whenever the specified transformation is invertible.
The inverse is quantified as an isomorphism with this exact forward transformation.
Source: Stacks Tags 05SU, 0145 and 0A8D
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus). -/
def ShiftTriangleCompatibility
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ] (τ : F ⟶ H) : Prop :=
  NatTrans.CommShift τ ℤ ∧ ImageTriangleCompatibility τ ∧
    ∀ e : F ≅ H, e.hom = τ →
      NatTrans.CommShift e.inv ℤ ∧ ImageTriangleCompatibility e.inv

private theorem imageTriangle_of_commShift
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ]
    [F.IsTriangulated] [H.IsTriangulated]
    (τ : F ⟶ H) [NatTrans.CommShift τ ℤ] : ImageTriangleCompatibility τ := by
  intro T hT
  refine ⟨F.map_distinguished T hT, H.map_distinguished T hT, ?_⟩
  let φ : F.mapTriangle.obj T ⟶ H.mapTriangle.obj T :=
    { hom₁ := τ.app T.obj₁
      hom₂ := τ.app T.obj₂
      hom₃ := τ.app T.obj₃
      comm₁ := τ.naturality T.mor₁
      comm₂ := τ.naturality T.mor₂
      comm₃ := by
        change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
            (shiftFunctor E (1 : ℤ)).map (τ.app T.obj₁) =
          τ.app T.obj₃ ≫ H.map T.mor₃ ≫ (H.commShiftIso (1 : ℤ)).hom.app T.obj₁
        rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc,
          τ.naturality T.mor₃, Category.assoc] }
  exact ⟨φ, rfl, rfl, rfl⟩

private theorem shiftTriangleCompatibility_of_commShift
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ]
    [F.IsTriangulated] [H.IsTriangulated]
    (τ : F ⟶ H) [NatTrans.CommShift τ ℤ] : ShiftTriangleCompatibility τ := by
  refine ⟨inferInstance, imageTriangle_of_commShift τ, ?_⟩
  intro e he
  have hhom : NatTrans.CommShift e.hom ℤ := by
    rw [he]
    infer_instance
  have : NatTrans.CommShift e.hom ℤ := hhom
  have hinv : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  have : NatTrans.CommShift e.inv ℤ := hinv
  exact ⟨hinv, imageTriangle_of_commShift e.inv⟩

private theorem inverseMate_commShift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]
    (β : TwoSquare R₁ H G R₂) [β.natTrans.CommShift ℤ] :
    ((mateEquiv adj₁ adj₂).symm β).natTrans.CommShift ℤ := by
  change ((Functor.leftUnitor (G ⋙ L₂)).inv ≫
    Functor.whiskerRight adj₁.unit (G ⋙ L₂) ≫
    (Functor.associator (L₁ ⋙ R₁) G L₂).inv ≫
    Functor.whiskerRight (Functor.associator L₁ R₁ G).hom L₂ ≫
    Functor.whiskerRight (Functor.whiskerLeft L₁ β.natTrans) L₂ ≫
    Functor.whiskerRight (Functor.associator L₁ H R₂).inv L₂ ≫
    (Functor.associator (L₁ ⋙ H) R₂ L₂).hom ≫
    Functor.whiskerLeft (L₁ ⋙ H) adj₂.counit ≫
    (Functor.rightUnitor (L₁ ⋙ H)).hom).CommShift ℤ
  infer_instance

private theorem adjunct_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F : C ⥤ D} {G : C ⥤ E} {L : D ⥤ E} {R : E ⥤ D}
    [F.CommShift ℤ] [G.CommShift ℤ] [L.CommShift ℤ] [R.CommShift ℤ]
    (adj : L ⊣ R) [adj.CommShift ℤ] (τ : F ⟶ G ⋙ R) [τ.CommShift ℤ] :
    NatTrans.CommShift ((Functor.leftUnitor (F ⋙ L)).inv ≫
      Functor.whiskerRight τ L ≫ (Functor.associator G R L).hom ≫
      Functor.whiskerLeft G adj.counit ≫ (Functor.rightUnitor G).hom) ℤ := by
  -- The leading unitor has identity components. Removing it avoids an extra
  -- identity-functor shift structure on the domain of the whiskered transformation.
  have he : (Functor.leftUnitor (F ⋙ L)).inv ≫
      Functor.whiskerRight τ L ≫ (Functor.associator G R L).hom ≫
      Functor.whiskerLeft G adj.counit ≫ (Functor.rightUnitor G).hom =
      Functor.whiskerRight τ L ≫ (Functor.associator G R L).hom ≫
      Functor.whiskerLeft G adj.counit ≫ (Functor.rightUnitor G).hom := by
    ext X
    simp
  rw [he]
  infer_instance

private theorem leftAdjointUniq_commShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} {R : D ⥤ C}
    [F.CommShift ℤ] [G.CommShift ℤ] [R.CommShift ℤ]
    (a : F ⊣ R) (b : G ⊣ R) [a.CommShift ℤ] [b.CommShift ℤ] :
    NatTrans.CommShift (a.leftAdjointUniq b).hom ℤ := by
  change NatTrans.CommShift ((conjugateEquiv b a).symm (𝟙 R)) ℤ
  infer_instance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- All clauses of the proper/open calculus, using exactly the dependency's normalized
maps. Structure morphisms express quasi-separated finite type over k, without separatedness.
No square map is required to preserve a chosen k-structure, so reindexing isomorphisms
with an unrelated k-structure are included.
Source: Stacks Tags 0F7B, 0F7F and 0F7J
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus). -/
structure QcqsShiftCalculus (k : Type u) [Field k] (data : Pasting Λ) : Prop where
  /-- The specified ambient mate for an isomorphism base change is invertible on all D.
  Applied to r and then p, this gives both exchanges of the statement. -/
  ambient_iso : ∀ {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [X'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X' ↘ Spec (CommRingCat.of k))]
    [Y'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k))]
    {f : X ⟶ Y} {a : X' ⟶ X} {f' : X' ⟶ Y'} {b : Y' ⟶ Y}
    [IsProper f] [IsIso b] (sq : ChosenCartesianSquare a f' f b),
    IsIso (condensedAmbientExchange Λ sq)
  /-- Gamma is the adjunct of inverse restriction, including non-Cartesian proper squares. -/
  gamma_compatibility : ∀ {U W Y Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (U ↘ Spec (CommRingCat.of k))]
    [W.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (W ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k))]
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    [IsProper p] [IsProper r] (sq : CommSq j p r i),
    ShiftTriangleCompatibility (gamma Λ data.units sq)
  /-- The inverse normalized open exchange, with the exact pullback model of the dependency. -/
  open_compatibility : ∀ {U' U W' W : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (U' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (U' ↘ Spec (CommRingCat.of k))]
    [U.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (U ↘ Spec (CommRingCat.of k))]
    [W'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (W' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (W' ↘ Spec (CommRingCat.of k))]
    [W.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (W ↘ Spec (CommRingCat.of k))]
    {a : U' ⟶ U} {j' : U' ⟶ W'} {j : U ⟶ W} {b : W' ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b),
    ShiftTriangleCompatibility (data.B sq).hom
  /-- The exact-model ambient mate used in the cube, with its canonical shifts. -/
  exact_exchange_compatibility : ∀ {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [X'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X' ↘ Spec (CommRingCat.of k))]
    [Y'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k))]
    {f : X ⟶ Y} {a : X' ⟶ X} {f' : X' ⟶ Y'} {b : Y' ⟶ Y}
    (sq : CommSq a f' f b),
    ShiftTriangleCompatibility (derivedDirectImageOpenRestriction Λ sq)
  /-- The very same ambient mate on the K-flat total-left-derived pullback model. -/
  ambient_compatibility : ∀ {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [X'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X' ↘ Spec (CommRingCat.of k))]
    [Y'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k))]
    {f : X ⟶ Y} {a : X' ⟶ X} {f' : X' ⟶ Y'} {b : Y' ⟶ Y}
    (sq : ChosenCartesianSquare a f' f b),
    ShiftTriangleCompatibility
      (F := moduleObjectDerivedPushforward Λ f ⋙ moduleObjectDerivedPullback Λ b)
      (H := moduleObjectDerivedPullback Λ a ⋙ moduleObjectDerivedPushforward Λ f')
      (condensedAmbientExchange Λ sq)
  /-- Canonical derived pullback compositors, in the exact and K-flat models. -/
  pullback_compositors : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z),
    ShiftTriangleCompatibility (pComp Λ f g).hom ∧
      ShiftTriangleCompatibility (modulePullbackDerivedCompositor Λ f g).hom
  /-- The canonical derived direct-image compositors, with fixed K-injective shifts. -/
  direct_image_compositors : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z),
    ShiftTriangleCompatibility (rComp Λ f g).hom
  /-- The canonical open-adjunction compositors. -/
  open_compositors : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k))]
    (j : X ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion i],
    ShiftTriangleCompatibility (jComp Λ j i).hom
  /-- The identity comparisons for all three operations. -/
  identity_comparisons : ∀ (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k))],
    ShiftTriangleCompatibility (pId Λ X).hom ∧
      ShiftTriangleCompatibility (rId Λ X).hom ∧
      ShiftTriangleCompatibility (jId Λ X).hom


/-- Shift-triangle compatibility of direct-image restriction. -/
private theorem derivedDirectImageOpenRestriction_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y X' Y' : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b) :
    ShiftTriangleCompatibility (derivedDirectImageOpenRestriction Λ sq) := by
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f)
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f')
  have : NatTrans.CommShift (derivedOpenCoherencePullbackSquare Λ sq).hom ℤ := by
    dsimp only [derivedOpenCoherencePullbackSquare, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift (derivedDirectImageOpenRestriction Λ sq) ℤ :=
    NatTrans.CommShift.mateEquiv (A := ℤ)
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom)
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the normalized proper/open adjunct. -/
private theorem gamma_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y}
    {r : W ⟶ Z} {i : Y ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion i]
    [QuasiCompact j] [QuasiCompact i] [IsProper p] [IsProper r]
    (units : OpenUnits Λ) (sq : CommSq j p r i) :
    ShiftTriangleCompatibility (gamma Λ units sq) := by
  have := (module_derived_functors_exact_and_comparison_shifts Λ p).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ r).2.1
  have := (derivedDirectImageOpenRestriction_shiftTriangle Λ sq).1
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (units.unitIso j).hom ℤ := by
    rw [units.normalized]
    infer_instance
  have : NatTrans.CommShift (restriction Λ units sq) ℤ := by
    dsimp only [restriction]
    infer_instance
  have : NatTrans.CommShift (comparisonInverse (restriction Λ units sq)) ℤ := by
    classical
    unfold comparisonInverse
    split_ifs with h
    · exact NatTrans.CommShift.of_iso_inv (asIso (restriction Λ units sq)) ℤ
    · constructor
      intro n
      ext K
      simp
  have : NatTrans.CommShift (gamma Λ units sq) ℤ :=
    adjunct_commShift (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i)
      (comparisonInverse (restriction Λ units sq))
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the inverse open exchange. -/
private theorem pasting_B_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (data : Pasting Λ) {U' U W' W : Scheme.{u}}
    {a : U' ⟶ U} {j' : U' ⟶ W'} {j : U ⟶ W} {b : W' ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b) :
    ShiftTriangleCompatibility (data.B sq).hom := by
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j').commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).hom ℤ := by
    dsimp only [derivedOpenCoherencePullbackSquare, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift (openMap Λ sq.toCommSq) ℤ :=
    inverseMate_commShift
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j')
      (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq.toCommSq).inv)
  have : NatTrans.CommShift (data.B sq).inv ℤ := by
    rw [data.B_normalized]
    assumption
  have : NatTrans.CommShift (data.B sq).symm.hom ℤ := by
    change NatTrans.CommShift (data.B sq).inv ℤ
    assumption
  have : NatTrans.CommShift (data.B sq).hom ℤ :=
    NatTrans.CommShift.of_iso_inv (data.B sq).symm ℤ
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of pullback compositors. -/
private theorem pComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShiftTriangleCompatibility (pComp Λ f g).hom := by
  have : NatTrans.CommShift (pComp Λ f g).hom ℤ := by
    dsimp only [pComp, Iso.trans_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

private theorem modulePullbackDerivedCompositor_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShiftTriangleCompatibility (modulePullbackDerivedCompositor Λ f g).hom := by
  have := (module_pullback_compositor_commShift Λ f g).1
  have := (module_derived_functors_exact_and_comparison_shifts Λ f).1
  have := (module_derived_functors_exact_and_comparison_shifts Λ g).1
  have := (module_derived_functors_exact_and_comparison_shifts Λ (f ≫ g)).1
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the direct-image compositor. -/
private theorem rComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShiftTriangleCompatibility (rComp Λ f g).hom := by
  have := (module_derived_functors_exact_and_comparison_shifts Λ f).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ g).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ (f ≫ g)).2.1
  have := (pComp_shiftTriangle Λ f g).1
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f)
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ g)
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ (f ≫ g))
  have : NatTrans.CommShift (rComp Λ f g).hom ℤ := by
    dsimp only [rComp, Iso.symm_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the open compositor. -/
private theorem jComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    ShiftTriangleCompatibility (jComp Λ j i).hom := by
  have := (pComp_shiftTriangle Λ j i).1
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (jComp Λ j i).hom ℤ := by
    dsimp only [jComp, Iso.symm_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

private theorem pId_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (X : Scheme.{u}) :
    ShiftTriangleCompatibility (pId Λ X).hom := by
  have : NatTrans.CommShift (pId Λ X).hom ℤ := by
    dsimp only [pId, Iso.trans_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

private theorem rId_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (X : Scheme.{u}) :
    ShiftTriangleCompatibility (rId Λ X).hom := by
  have := (module_derived_functors_exact_and_comparison_shifts Λ (𝟙 X)).2.1
  have := (pId_shiftTriangle Λ X).1
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ (𝟙 X))
  have : NatTrans.CommShift (rId Λ X).hom ℤ := by
    dsimp only [rId]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

private theorem jId_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (X : Scheme.{u}) :
    ShiftTriangleCompatibility (jId Λ X).hom := by
  have := (pId_shiftTriangle Λ X).1
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).commShift_mapDerivedCategoryAdjunction
  have : ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
      (pId Λ X)).CommShift ℤ :=
    Adjunction.commShift_ofNatIsoRight (A := ℤ)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)) (pId Λ X)
  have : NatTrans.CommShift (jId Λ X).hom ℤ :=
    leftAdjointUniq_commShift
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight (pId Λ X))
      Adjunction.id
  exact shiftTriangleCompatibility_of_commShift _

set_option synthInstance.maxHeartbeats 200000 in
-- The calculus contains many derived-functor instance searches.
/-- Isomorphism exchange and shift compatibility for the specified normalized condensed
proper/open maps, without absolute separatedness or a Cartesian hypothesis on Gamma.
Source: Stacks more-etale.tex Tags 0F7B, 0F7F and 0F7J; latest blueprint
sk-thm-sf-comp-composition, base-change paragraph
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus).

Proof:
1. Base change of an isomorphism has inverse given by the identity and inverse base map.
Apply lem-sf-condensed-isomorphism-square-exchange to r and p: their normalized mates
are the displayed ambient exchanges on the entire unbounded category.
2. The canonical-right-derived-adjunction-shift lemma, applied to the module
upper-star/lower-star adjunction of each scheme map, makes its unit and counit compatible
with the fixed K-injective right shift. The exact open adjunction descends termwise, so its
derived adjunction commutes with shifts. The exact-derived natural-isomorphism, composition
and identity comparisons commute with shifts; the K-flat pullback model is covered by
module-derived-functor-compositor-shifts.
3. The exact-model pullback square comparison is a composite of exact-derived
compositors and the localized square, so it commutes with shifts; its mate under the two
derived adjunctions (the exact ambient restriction mate) does too, for every commutative
square. For the K-flat ambient exchange, ambient-qcqs-exchange-canonical-shifts gives
triangulated composites and the shift equation for all integers.
4. The forward open comparison is open unit, pullback comparison and open counit.
It commutes with shifts; invertibility in the pasting node gives the same equation
for B by multiplying by the two inverse components.
5. Restriction is the ambient restriction mate followed by the inverse open unit.
Both commute with shifts; so do their composite and its inverse. Gamma is its
open-adjunction adjunct, hence open extension of the inverse followed by the counit.
This proves the Gamma equation even for non-Cartesian proper squares, without
asserting that Gamma is invertible.
6. The exact pullback compositor and identity are composites of the exact-derived
comparisons of step 2; the K-flat pullback compositor commutes with shifts by
module-pullback-compositor-commShift. The direct-image compositor and identity are defined
as conjugates of these under the shift-compatible derived adjunctions, so they commute with
shifts; no separate normalization theorem is needed. The open compositor is an inverse
conjugate under the exact open adjunctions. The open identity is the leftAdjointUniq of the
open adjunction transported along the pullback identity and the identity adjunction.
Inverse comparisons satisfy the inverse shift equation.
7. All image triangles are distinguished by exactness and triangulated-functor
composition. Naturality supplies the first two triangle squares. For the third,
H(w) followed by the H-shift comparison composed with tau_C equals tau_A[1]
composed with F(w) and the F-shift comparison, by naturality and the shift equation.
Thus the three specified components give the triangle morphism. The same calculation
applies to inverses whenever the comparison is invertible.
-/
theorem condensedProperOpenQcqsCalculus
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (q : ℕ) [CharP k q] (_hq : 0 < q) (_hneq : q ≠ ℓ)
    (data : Pasting (Profinite.padicAlgClRingObj.{u} ℓ)) :
    QcqsShiftCalculus (Profinite.padicAlgClRingObj.{u} ℓ) k data := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y X' Y' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f a f' b hf hb sq
    have ha : IsIso a := by
      rw [← sq.hom_fst]
      infer_instance
    have : IsIso a := ha
    exact (AlgebraicGeometry.ProEtale.CondensedRing.condensed_isomorphism_square_exchange
      (Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)) sq.toCommSq).2.2.2.2.2.2
  · intros
    exact gamma_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ)
      data.units (by assumption)
  · intros
    exact pasting_B_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ)
      data (by assumption)
  · intros
    exact derivedDirectImageOpenRestriction_shiftTriangle
      (Λ := Profinite.padicAlgClRingObj.{u} ℓ) (by assumption)
  · intro X Y X' Y' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f a f' b sq
    obtain ⟨hF, hH, hs⟩ := ambient_qcqs_exchange_canonical_shifts
      (Profinite.padicAlgClRingObj.{u} ℓ) sq
    have := hF
    have := hH
    have : NatTrans.CommShift
        (F₁ := moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj.{u} ℓ) f ⋙
          moduleObjectDerivedPullback (Profinite.padicAlgClRingObj.{u} ℓ) b)
        (F₂ := moduleObjectDerivedPullback (Profinite.padicAlgClRingObj.{u} ℓ) a ⋙
          moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj.{u} ℓ) f')
        (condensedAmbientExchange (Profinite.padicAlgClRingObj.{u} ℓ) sq) ℤ := by
      constructor
      intro n
      ext K
      exact (hs n K).symm
    exact shiftTriangleCompatibility_of_commShift
      (F := moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj.{u} ℓ) f ⋙
        moduleObjectDerivedPullback (Profinite.padicAlgClRingObj.{u} ℓ) b)
      (H := moduleObjectDerivedPullback (Profinite.padicAlgClRingObj.{u} ℓ) a ⋙
        moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj.{u} ℓ) f') _
  · intros
    exact ⟨pComp_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _ _,
      modulePullbackDerivedCompositor_shiftTriangle
        (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _ _⟩
  · intros
    exact rComp_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _ _
  · intros
    exact jComp_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _ _
  · intros
    exact ⟨pId_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _,
      rId_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _,
      jId_shiftTriangle (Λ := Profinite.padicAlgClRingObj.{u} ℓ) _⟩


end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
