/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Category
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.WeilSheaf.LisseFiltration
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Irreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.WeilSheaf.LisseLocus
import WeilConjectures.WeilSheaf.UpperStarExact
import WeilConjectures.WeilSheaf.UpperStarId
import WeilConjectures.WeilSheaf.StalkUpperStar

/-! # Arithmetic simplicity survives affine-line pullback

Source: the affine-line replacement in `lem-zl-simple-lisse-support-model`.
(blueprint: lem-zl-affine-line-pullback-irreducible).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

private theorem isZero_of_isZero_upperStar
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IrreducibleSpace (Z ↘ Spec (.of k)).geometricFiber]
    (f : Y ⟶ Z) [f.IsOver (Spec (.of k))]
    (t : Spec (.of (AlgebraicClosure k)) ⟶ (Y ↘ Spec (.of k)).geometricFiber)
    (G : WeilSheaf k l Z) (hG : G.IsLisse) (h : IsZero ((upperStar f).obj G)) :
    IsZero G := by
  let b := Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k)))
  let e := asIso (stalkObjHomOfUpperStar f ((upperStar f).obj G) (𝟙 _) t)
  have hst : IsZero (G.stalkObj (t ≫ b)) :=
    ((stalkFunctor k l t).map_isZero h).of_iso e
  have hsub : Subsingleton (G.stalkObj (t ≫ b)) := by
    change Subsingleton ((WeilCoefficients.toModuleCat l).obj (G.stalkObj (t ≫ b)))
    have hz := (WeilCoefficients.toModuleCat l).map_isZero hst
    exact ModuleCat.subsingleton_of_isZero hz
  refine isZero_iff_isZero_carrier.mpr
    (hG.isZero_of_subsingleton_globalSections_upperStar (AlgebraicClosure k) fun y ↦ ?_)
  exact ⟨genericPoint _, t ≫ b, genericPoint_specializes y,
    genericPoint_specializes _, hsub⟩

private theorem irreducibleLisse_of_retraction
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    (P : WeilSheaf k l Y ⥤ WeilSheaf k l Z)
    (S : WeilSheaf k l Z ⥤ WeilSheaf k l Y)
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {V : WeilSheaf k l Y} (hV : V.IsIrreducibleLisse)
    (e : P ⋙ S ≅ 𝟭 (WeilSheaf k l Y)) (hPV : (P.obj V).IsLisse)
    (hS : ∀ G : WeilSheaf k l Z, G.IsLisse → (S.obj G).IsLisse)
    (hdetect : ∀ G : WeilSheaf k l Z, G.IsLisse → IsZero (S.obj G) → IsZero G) :
    (P.obj V).IsIrreducibleLisse := by
  let eV : S.obj (P.obj V) ≅ V := e.app V
  have hnPV : ¬ IsZero (P.obj V) := by
    intro h
    have hs : IsZero (S.obj (P.obj V)) := S.map_isZero h
    exact hV.2.1 (hs.of_iso eV.symm)
  refine ⟨hPV, hnPV, fun G i hi hG ↦ ?_⟩
  let j : S.obj G ⟶ V := S.map i ≫ eV.hom
  have hj : Mono j := inferInstance
  obtain hzero | hiso := hV.2.2 (S.obj G) j hj (hS G hG)
  · exact Or.inl (hdetect G hG hzero)
  · have : IsIso j := hiso
    have : IsIso (S.map i) := IsIso.of_isIso_comp_right _ eV.hom
    have hQ : (cokernel i).IsLisse :=
      (IsLisse.kernel_cokernel (F := G) (G := P.obj V) hG hPV i).2
    have hSQ : IsZero (S.obj (cokernel i)) :=
      (isZero_cokernel_of_epi (S.map i)).of_iso (PreservesCokernel.iso S i)
    have hzero := hdetect (cokernel i) hQ hSQ
    have : Epi i := Preadditive.epi_of_isZero_cokernel i hzero
    exact Or.inr (isIso_of_mono_of_epi i)

private theorem nonempty_iso_trans' {D : Type*} [Category* D] {a b c : D}
    (h : Nonempty (a ≅ b)) (h' : Nonempty (b ≅ c)) : Nonempty (a ≅ c) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e ≪≫ e'⟩

private theorem nonempty_upperStar_section_functorIso
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))]
    (z : Y ⟶ Z) [z.IsOver (Spec (.of k))] (hz : z ≫ p = 𝟙 Y) :
    Nonempty (upperStar (k₀ := k) (l := l) p ⋙ upperStar z ≅ 𝟭 (WeilSheaf k l Y)) := by
  exact nonempty_iso_trans'
    ⟨(upperStarCompIso (k₀ := k) (l := l) z p).symm⟩
    (nonempty_iso_trans' ⟨upperStarCongr (k₀ := k) (l := l) hz⟩
      ⟨upperStarIdIso (k₀ := k) (l := l) Y⟩)

private theorem irreducibleLisse_upperStar_of_section
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [IrreducibleSpace (Z ↘ Spec (.of k)).geometricFiber]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))]
    (z : Y ⟶ Z) [z.IsOver (Spec (.of k))] (hz : z ≫ p = 𝟙 Y)
    (t : Spec (.of (AlgebraicClosure k)) ⟶ (Y ↘ Spec (.of k)).geometricFiber)
    {V : WeilSheaf k l Y} (hV : V.IsIrreducibleLisse) :
    ((upperStar p).obj V).IsIrreducibleLisse := by
  obtain ⟨e⟩ := nonempty_upperStar_section_functorIso (k := k) (l := l) p z hz
  exact irreducibleLisse_of_retraction (k := k) (l := l) (Y := Y) (Z := Z) (V := V)
    (upperStar (k₀ := k) (l := l) p) (upperStar (k₀ := k) (l := l) z) hV e
    (IsLisse.upperStar (k₀ := k) (l := l) (F := V) hV.1 p)
    (fun G hG ↦ IsLisse.upperStar (k₀ := k) (l := l) (F := G) hG z)
    (fun G hG hzero ↦ isZero_of_isZero_upperStar (k := k) (l := l) z t G hG hzero)

private theorem section_isOver
    {Y Z B : Scheme.{u}} [Y.Over B] [Z.Over B]
    (p : Z ⟶ Y) [p.IsOver B] (z : Y ⟶ Z) (hz : z ≫ p = 𝟙 Y) : z.IsOver B := by
  constructor
  rw [← comp_over p B, ← Category.assoc, hz, Category.id_comp]

private theorem exists_affineLine_geometry
    {k : Type u} [Field k] [Finite k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsAffine C]
    [Smooth (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k))] :
    ∃ (A : Scheme.{u}) (_ : A.Over (Spec (.of k))) (_ : IsAffine A)
      (_ : GeometricallyConnected (A ↘ Spec (.of k)))
      (_ : LocallyOfFiniteType (A ↘ Spec (.of k)))
      (_ : QuasiCompact (A ↘ Spec (.of k))) (_ : IsSeparated (A ↘ Spec (.of k)))
      (_ : IrreducibleSpace (A ↘ Spec (.of k)).geometricFiber)
      (p : A ⟶ C) (z : C ⟶ A) (_ : p.IsOver (Spec (.of k)))
      (_ : z.IsOver (Spec (.of k))) (_ : SmoothOfRelativeDimension 1 p), z ≫ p = 𝟙 C := by
  classical
  let A := AffineSpace PUnit.{u + 1} C
  let p : A ⟶ C := A ↘ C
  let z : C ⟶ A := AffineSpace.homOfVector (𝟙 C) (fun _ ↦ 0)
  have hz : z ≫ p = 𝟙 C := AffineSpace.homOfVector_over _ _
  have hp : p ≫ (C ↘ Spec (.of k)) = A ↘ Spec (.of k) := comp_over p _
  have : z.IsOver (Spec (.of k)) := section_isOver p z hz
  have hsmP : SmoothOfRelativeDimension 1 p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} C
  have hsmP' : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have hsm : Smooth (A ↘ Spec (.of k)) := by
    rw [← hp]
    infer_instance
  have hconnP : GeometricallyConnected p :=
    GeometricallyConnected.of_geometricallyIrreducible p
  have hconn : GeometricallyConnected (A ↘ Spec (.of k)) := by
    rw [← hp]
    exact GeometricallyConnected.comp p (C ↘ Spec (.of k))
  have hgeo : GeometricallyIrreducible (A ↘ Spec (.of k)) :=
    GeometricallyIrreducible.of_smooth_of_geometricallyConnected _
  have hgeoFiber : IrreducibleSpace (A ↘ Spec (.of k)).geometricFiber :=
    Scheme.Hom.irreducibleSpace_geometricFiber (A ↘ Spec (.of k))
  have hftA : LocallyOfFiniteType (A ↘ Spec (.of k)) := by
    rw [← hp]
    infer_instance
  refine ⟨A, inferInstance, inferInstance, hconn, hftA, ?_, ?_, hgeoFiber, p, z,
    inferInstance, inferInstance, hsmP, hz⟩
  all_goals infer_instance

/-- A relative affine-line model with a section preserves arithmetic lisse simplicity.

Source: the affine-line replacement in `lem-zl-simple-lisse-support-model`, from the
geometric-component reduction in `sk-i-dl-general-real`.
(blueprint: lem-zl-affine-line-pullback-irreducible).

Proof: Construct the actual relative affine line and its zero section. Smoothness
and geometric connectedness make its geometric fiber irreducible. Expose these
proved geometric data through `exists_affineLine_geometry`; the native functor
argument then works with abstract scheme morphisms instead of unfolding the
large pullback construction of affine space.

Pullback preserves lissity and the zero section retracts the projection, so the
pulled-back object is nonzero. Pull a lisse subobject back along the zero section.
Exactness and the pullback-composition isomorphism make it a lisse subobject of V,
hence zero or all of V. A lisse sheaf on the irreducible geometric fiber whose
zero-section restriction vanishes has a zero geometric stalk, and is zero by the
lisse stalk-vanishing criterion: its generic point specializes to every point
and to that stalk. Apply this to the subobject, and in the isomorphism case to
its lisse cokernel. Exactness identifies the latter restriction with the zero
cokernel of an isomorphism. Thus the original subobject is zero or an isomorphism.
No classification of affine-line local systems or semisimplicity is used. -/
theorem IsIrreducibleLisse.exists_affineLine_model
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsAffine C]
    [Smooth (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k))]
    {V : WeilSheaf k l C} (hV : V.IsIrreducibleLisse) :
    ∃ (A : Scheme.{u}) (_ : A.Over (Spec (.of k))) (_ : IsAffine A)
      (_ : GeometricallyConnected (A ↘ Spec (.of k)))
      (_ : LocallyOfFiniteType (A ↘ Spec (.of k)))
      (_ : QuasiCompact (A ↘ Spec (.of k))) (_ : IsSeparated (A ↘ Spec (.of k)))
      (_ : IrreducibleSpace (A ↘ Spec (.of k)).geometricFiber)
      (p : A ⟶ C) (z : C ⟶ A) (_ : p.IsOver (Spec (.of k)))
      (_ : z.IsOver (Spec (.of k))) (_ : SmoothOfRelativeDimension 1 p),
      z ≫ p = 𝟙 C ∧ ((upperStar p).obj V).IsIrreducibleLisse := by
  obtain ⟨A, hover, haff, hconn, hft, hqc, hsep, hgeo, p, z, hp, hzover, hsm, hz⟩ :=
    exists_affineLine_geometry (k := k) (C := C)
  obtain ⟨x, _⟩ := V.exists_nontrivial_stalk_of_not_isZero hV.2.1
  let t := (C ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x
  refine ⟨A, hover, haff, hconn, hft, hqc, hsep, hgeo, p, z, hp, hzover, hsm, hz, ?_⟩
  exact irreducibleLisse_upperStar_of_section (k := k) (l := l)
    (Y := C) (Z := A) (V := V) p z hz t hV

end AlgebraicGeometry.WeilSheaf
