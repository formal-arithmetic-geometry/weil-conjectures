/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassFiniteRootPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootCartierClassDetection

/-! # Reduced Kummer root naturality

Source: diagonal coefficient changes, paragraph (3). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y')]
  {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
  {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
  {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
  {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
  {e : CompletedRealization l (diagonalSurface Y)}
  {e' : CompletedRealization l (diagonalSurface Y')}

private theorem shifted_single_hom
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    {M N : A}
    (f : ((DerivedCategory.singleFunctor A 0).obj M)⟦(2 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj N)⟦(2 : ℤ)⟧) :
    ∃! a : M ⟶ N, ((DerivedCategory.singleFunctor A 0).map a)⟦(2 : ℤ)⟧' = f := by
  let S := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor (DerivedCategory A) (2 : ℤ)
  refine ⟨S.preimage f, S.map_preimage f, ?_⟩
  intro a ha
  exact S.map_injective (ha.trans (S.map_preimage f).symm)

private theorem conjugation
    {C : Type*} [Category C] {X Y Z T V : C}
    (b : X ≅ Y) (q : Y ≅ Z) (a : Z ≅ T) (f : X ⟶ V) (h : T ⟶ V)
    (hh : a.inv ≫ q.inv ≫ b.inv ≫ f = h) :
    f = b.hom ≫ q.hom ≫ a.hom ≫ h := by
  rw [← hh]
  simp only [Iso.hom_inv_id_assoc]

private theorem boundary_conjugation
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {S T U V : C} {S' T' U' V' : D}
    (a : S ≅ T) (b : U ≅ V) (a' : S' ≅ T') (b' : U' ≅ V')
    (δ : S ⟶ U) (δ' : S' ⟶ U') (s : G.obj S ⟶ S') (t : G.obj U ⟶ U')
    (c : T ⟶ V) (c' : T' ⟶ V') (r : G.obj V ⟶ V')
    (hc : c = a.inv ≫ δ ≫ b.hom) (hc' : c' = a'.inv ≫ δ' ≫ b'.hom)
    (hb : G.map δ ≫ t = s ≫ δ') (hr : t ≫ b'.hom = G.map b.hom ≫ r) :
    G.map c ≫ r = (G.map a.inv ≫ s ≫ a'.hom) ≫ c' := by
  rw [hc, hc']
  simp only [Functor.map_comp, Category.assoc]
  rw [← hr, ← Category.assoc (G.map δ), hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Reduced Kummer units commute with the canonical map of strict root systems.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md,
paragraph (3), canonical Kummer pullback and positive finite normalization.
(blueprint: lem-diagonal-class-kummer-root-naturality).

Proof: conjugate the system target by b, bprime and the exact shifted single
comparisons. Full faithfulness of the shifted single functor extracts an
ordinary tower map h. The two boundary normalizations and the frame boundary
square identify the pulled Cartier class composed with h with the normalized
source comparison followed by the upstairs Cartier class. At each finite level,
positive Cartier pullback gives the same equality for the canonical root map.
The positive supported residue detects the restrictions of h and this map to
the diagonal. Ordinary root-tower rigidity then detects their equality on the
whole product: etale first-projection inverse image is full and the diagonal
is a section. Substitute this equality in the original conjugation equation.
Empty bases give unique maps; exponents n+1 include n=0 and l=2. -/
theorem diagonalClassKummerRootNaturality
    (frame : DiagonalClassPullbackFrame l g d d' e e') :
    frame.systemTarget ≫ d'.b.hom =
      (diagonalClassTowerPull l (baseW g)).mapDerivedCategory.map d.b.hom ≫
        diagonalClassRootShiftedPullback frame := by
  let G := (diagonalClassTowerPull l (baseW g)).mapDerivedCategory
  let q := (G.commShiftIso (2 : ℤ)).app
    ((DerivedCategory.singleFunctor _ 0).obj d.H)
  let r := (diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0
  let a := (shiftFunctor _ (2 : ℤ)).mapIso (r.app d.H)
  let f := a.inv ≫ q.inv ≫ G.map d.b.inv ≫ frame.systemTarget ≫ d'.b.hom
  obtain ⟨h, hh, _⟩ := shifted_single_hom f
  let χ (k : (diagonalClassTowerPull l (baseW g)).obj d.H ⟶ d'.H) :=
    q.hom ≫ a.hom ≫ ((DerivedCategory.singleFunctor _ 0).map k)⟦(2 : ℤ)⟧'
  have ht : frame.systemTarget ≫ d'.b.hom = G.map d.b.hom ≫ χ h := by
    exact conjugation (G.mapIso d.b) q a (frame.systemTarget ≫ d'.b.hom)
      (((DerivedCategory.singleFunctor _ 0).map h)⟦(2 : ℤ)⟧') hh.symm
  have hc : G.map d.c.hom ≫ χ h =
      (G.map d.a.inv ≫ frame.systemSource ≫ d'.a.hom) ≫ d'.c.hom :=
    boundary_conjugation G d.a d.b d'.a d'.b
      (D.T.map (diagonalIntegralBoundary Y).hom)
      (D'.T.map (diagonalIntegralBoundary Y').hom)
      frame.systemSource frame.systemTarget d.c.hom d'.c.hom (χ h)
      d.boundary_normalization d'.boundary_normalization frame.boundary ht
  have hr : h = diagonalClassOrdinaryRootPullback frame := by
    apply diagonalRootCartierClassDetection (d := d) (d' := d')
    intro n
    let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
    have hn := congrArg V.mapDerivedCategory.map hc
    have hk := diagonalClassFiniteRootPullback frame n
    simpa only [χ, q, r, a, G, V, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc,
      diagonalClassRootShiftedPullback] using hn.trans hk.symm
  rw [hr] at ht
  simpa only [χ, q, r, a, G, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc,
    diagonalClassRootShiftedPullback] using ht

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
