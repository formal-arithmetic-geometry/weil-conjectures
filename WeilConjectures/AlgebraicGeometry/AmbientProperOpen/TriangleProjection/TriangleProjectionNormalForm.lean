/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.TriangleProjection.TriangleProjectionSystemNormalForm
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Triangle projection in counit normal form

Source: blueprint main-20261015, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, composition/refinement sentence; the agent expansion
in the DAG (blueprint: lem-sf-triangle-projection-normal-form).

The auxiliary definitions spell out the two words and their common target. They use
canonical open tensor maps, proper projections and adjunction-conjugate compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- Naturality transports a mate identity across an isomorphism in its input. -/
private theorem transport_mate_identity
    {V D : Type*} [Category V] [Category D] {F G : V ⥤ D}
    (gamma : F ⟶ G) {W W' N : V} (a : W ≅ W') (v : W ⟶ N)
    {A B : D} (d : A ⟶ F.obj W) (t : A ⟶ B) (e : B ⟶ G.obj W')
    (h : d ≫ F.map a.hom ≫ gamma.app W' = t ≫ e) :
    d ≫ F.map v ≫ gamma.app N =
      t ≫ e ≫ G.map a.inv ≫ G.map v := by
  calc
    d ≫ F.map v ≫ gamma.app N =
        d ≫ F.map a.hom ≫ F.map (a.inv ≫ v) ≫ gamma.app N := by
      simp only [← F.map_comp_assoc, a.hom_inv_id_assoc]
    _ = (d ≫ F.map a.hom ≫ gamma.app W') ≫ G.map (a.inv ≫ v) := by
      rw [gamma.naturality]
      simp only [Category.assoc]
    _ = t ≫ e ≫ G.map a.inv ≫ G.map v := by
      rw [h, G.map_comp]
      simp only [Category.assoc]

/-- Apply a functor to an inner identity and use an outer naturality square. -/
private theorem whisker_projection_identity
    {D Z : Type*} [Category D] [Category Z] (S : D ⥤ Z)
    {A B C : D} {U V T : Z}
    (f : A ⟶ C) (t : A ⟶ B) (g : B ⟶ C)
    (a : U ⟶ S.obj A) (b : U ⟶ V) (c : V ⟶ S.obj B)
    (d : S.obj C ⟶ T) (h : f = t ≫ g)
    (hn : a ≫ S.map t = b ≫ c) :
    a ≫ S.map f ≫ d = b ≫ c ≫ S.map g ≫ d := by
  rw [h, S.map_comp]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ S.map g ≫ d) hn

/-- An inner mate square and outer projection square paste to the expanded triangle. -/
private theorem triangle_calculation
    {CV CY CB CD CZ : Type*} [Category CV] [Category CY] [Category CB]
    [Category CD] [Category CZ]
    (R : CV ⥤ CY) (J : CY ⥤ CD) (K : CV ⥤ CB) (P : CB ⥤ CD) (S : CD ⥤ CZ)
    (gamma : R ⋙ J ⟶ K ⋙ P)
    {W W' N : CV} {H : CY} {A B : CD} {E : CB} {U V T : CZ}
    (a : W ≅ W') (v : W ⟶ N) (di : A ⟶ J.obj H) (dq : H ⟶ R.obj W)
    (t : A ⟶ B) (e : B ⟶ P.obj E) (delta : E ⟶ K.obj W')
    (pi : U ⟶ S.obj A) (tt : U ⟶ V) (pi' : V ⟶ S.obj B)
    (c : S.obj ((K ⋙ P).obj N) ⟶ T)
    (h : di ≫ J.map dq ≫ J.map (R.map a.hom) ≫ gamma.app W' =
      t ≫ e ≫ P.map delta)
    (hn : pi ≫ S.map t = tt ≫ pi') :
    pi ≫ S.map di ≫ S.map (J.map (dq ≫ R.map v)) ≫ S.map (gamma.app N) ≫ c =
      tt ≫ pi' ≫ S.map e ≫
        S.map (P.map (delta ≫ K.map a.inv ≫ K.map v)) ≫ c := by
  have hi := transport_mate_identity gamma a v (di ≫ J.map dq) t
    (e ≫ P.map delta) (by simpa only [Functor.comp_map, Category.assoc] using h)
  have hw := whisker_projection_identity S _ _ _ pi tt pi' c hi hn
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using hw

attribute [local irreducible] AlgebraicGeometry.ProEtale.properOpenMate
  AlgebraicGeometry.ProEtale.properOpenPullSquareIso
  AlgebraicGeometry.ProEtale.properOpenTensorIso

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace TriangleProjection

variable (F : WeilConjectures.FiniteFieldDatum.{u})
  (A : Type (u + 1)) [CommRing A] [Finite A]
  {X V B Y D Z : Spaces F}
  (j : X ⟶ V) (b : V ⟶ B) (i : Y ⟶ D)
  (q : V ⟶ Y) (p : B ⟶ D) (s : D ⟶ Z)
  [IsOpenImmersion j.hom.left] [IsOpenImmersion b.hom.left]
  [IsOpenImmersion i.hom.left]
  [IsProper q.hom.left] [IsProper p.hom.left] [IsProper s.hom.left]
  (h : b ≫ p = q ≫ i)

/-- The object K' in the displayed triangle formula.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-normal-form). -/
def finiteInput (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Z.obj.left) :=
  ((ProperOpenTensor A X.obj.left).obj K).obj
    ((ProperOpenPull A j.hom.left).obj ((ProperOpenPull A q.hom.left).obj
      ((ProperOpenPull A i.hom.left).obj ((ProperOpenPull A s.hom.left).obj L))))

/-- C is proper composition followed by open composition, with functor associators
implicit at components. Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-normal-form). -/
def finiteC (N : ProperOpenDerived A X.obj.left) :
    (ProperOpenPush A s.hom.left).obj ((ProperOpenPush A p.hom.left).obj
      ((ProperOpenShriek A b.hom.left).obj ((ProperOpenShriek A j.hom.left).obj N))) ⟶
    (ProperOpenPush A (p.hom.left ≫ s.hom.left)).obj
      ((ProperOpenShriek A (j.hom.left ≫ b.hom.left)).obj N) :=
  ((ordinary F A).sComp p s).hom.app
      ((ProperOpenShriek A b.hom.left).obj ((ProperOpenShriek A j.hom.left).obj N)) ≫
    (ProperOpenPush A (p.hom.left ≫ s.hom.left)).map (
      (properOpenShriekComp A j.hom.left b.hom.left).hom.app N)

/-- The triangle's left word, ending in alpha = S_s(gamma) followed by C.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-normal-form). -/
def finiteLeft (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Z.obj.left) :=
  properOpenProjection A s.hom.left
      ((ProperOpenShriek A i.hom.left).obj
        ((ProperOpenPush A q.hom.left).obj ((ProperOpenShriek A j.hom.left).obj K))) L ≫
    (ProperOpenPush A s.hom.left).map
      ((properOpenTensorIso A i.hom.left
        ((ProperOpenPush A q.hom.left).obj ((ProperOpenShriek A j.hom.left).obj K))
        ((ProperOpenPull A s.hom.left).obj L)).hom) ≫
    (ProperOpenPush A s.hom.left).map ((ProperOpenShriek A i.hom.left).map
      (properOpenProjection A q.hom.left ((ProperOpenShriek A j.hom.left).obj K)
        ((ProperOpenPull A i.hom.left).obj ((ProperOpenPull A s.hom.left).obj L)) ≫
      (ProperOpenPush A q.hom.left).map
        (properOpenTensorIso A j.hom.left K ((ProperOpenPull A q.hom.left).obj
          ((ProperOpenPull A i.hom.left).obj ((ProperOpenPull A s.hom.left).obj L)))).hom)) ≫
    (ProperOpenPush A s.hom.left).map
      ((properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h)).app
        ((ProperOpenShriek A j.hom.left).obj (finiteInput F A j i q s K L))) ≫
    finiteC F A j b p s (finiteInput F A j i q s K L)

/-- The counit normal word. The inverse square comparison identifies P_b P_p T with
P_q P_i T; no projection arrow is inverted.
Source: blueprint composition/refinement sentence
(blueprint: lem-sf-triangle-projection-normal-form). -/
def finiteRight (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Z.obj.left) :=
  ((ProperOpenTensor A Z.obj.left).map
    ((ProperOpenPush A s.hom.left).map
      ((properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) h)).app
      ((ProperOpenShriek A j.hom.left).obj K)))).app L ≫
    properOpenProjection A s.hom.left
      ((ProperOpenPush A p.hom.left).obj
        ((ProperOpenShriek A b.hom.left).obj ((ProperOpenShriek A j.hom.left).obj K))) L ≫
    (ProperOpenPush A s.hom.left).map
      (properOpenProjection A p.hom.left
        ((ProperOpenShriek A b.hom.left).obj ((ProperOpenShriek A j.hom.left).obj K))
        ((ProperOpenPull A s.hom.left).obj L)) ≫
    (ProperOpenPush A s.hom.left).map ((ProperOpenPush A p.hom.left).map
      ((properOpenTensorIso A b.hom.left ((ProperOpenShriek A j.hom.left).obj K)
        ((ProperOpenPull A p.hom.left).obj ((ProperOpenPull A s.hom.left).obj L))).hom ≫
      (ProperOpenShriek A b.hom.left).map
        (((ProperOpenTensor A V.obj.left).obj ((ProperOpenShriek A j.hom.left).obj K)).map
          ((properOpenPullSquareIso A b.hom.left q.hom.left p.hom.left i.hom.left
            (congrArg (fun f ↦ f.hom.left) h)).inv.app
              ((ProperOpenPull A s.hom.left).obj L))) ≫
      (ProperOpenShriek A b.hom.left).map
        (properOpenTensorIso A j.hom.left K ((ProperOpenPull A q.hom.left).obj
          ((ProperOpenPull A i.hom.left).obj ((ProperOpenPull A s.hom.left).obj L)))).hom)) ≫
    finiteC F A j b p s (finiteInput F A j i q s K L)

omit [IsProper s.hom.left] in
/-- The finite diagram chase works over every finite coefficient ring. -/
private theorem finite_normalForm
    (K : ProperOpenDerived A X.obj.left) (L : ProperOpenDerived A Z.obj.left) :
    finiteLeft F A j b i q p s h K L = finiteRight F A j b i q p s h K L := by
  let M := (ProperOpenShriek A j.hom.left).obj K
  let T := (ProperOpenPull A s.hom.left).obj L
  let gamma := properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left
    (congrArg (fun f ↦ f.hom.left) h)
  let a := ((ProperOpenTensor A V.obj.left).obj M).mapIso
    ((properOpenPullSquareIso A b.hom.left q.hom.left p.hom.left i.hom.left
      (congrArg (fun f ↦ f.hom.left) h)).app T)
  let v := (properOpenTensorIso A j.hom.left K
    ((ProperOpenPull A q.hom.left).obj ((ProperOpenPull A i.hom.left).obj T))).hom
  have hm := properOpenProjectionMate A b.hom.left q.hom.left p.hom.left i.hom.left
    (congrArg (fun f ↦ f.hom.left) h) M T
  have hc : properOpenMateTensorMap A b.hom.left q.hom.left p.hom.left i.hom.left
      (congrArg (fun f ↦ f.hom.left) h) M T =
      ((ProperOpenTensor A D.obj.left).map (gamma.app M)).app T := by
    exact (Category.id_comp _).trans (Category.comp_id _)
  have hn := congrArg (fun f ↦ f.app L)
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) s.hom.left).naturality
      (gamma.app M))
  change ((ProperOpenTensor A Z.obj.left).map
      ((ProperOpenPush A s.hom.left).map (gamma.app M))).app L ≫
      properOpenProjection A s.hom.left
        ((ProperOpenPush A p.hom.left).obj ((ProperOpenShriek A b.hom.left).obj M)) L =
    properOpenProjection A s.hom.left
        ((ProperOpenShriek A i.hom.left).obj ((ProperOpenPush A q.hom.left).obj M)) L ≫
      (ProperOpenPush A s.hom.left).map
        (((ProperOpenTensor A D.obj.left).map (gamma.app M)).app T) at hn
  dsimp only [finiteLeft, finiteRight]
  have hw := triangle_calculation (ProperOpenPush A q.hom.left)
    (ProperOpenShriek A i.hom.left) (ProperOpenShriek A b.hom.left)
    (ProperOpenPush A p.hom.left) (ProperOpenPush A s.hom.left) gamma a v
    (properOpenTensorIso A i.hom.left ((ProperOpenPush A q.hom.left).obj M) T).hom
    (properOpenProjection A q.hom.left M ((ProperOpenPull A i.hom.left).obj T))
    (((ProperOpenTensor A D.obj.left).map (gamma.app M)).app T)
    (properOpenProjection A p.hom.left ((ProperOpenShriek A b.hom.left).obj M) T)
    (properOpenTensorIso A b.hom.left M ((ProperOpenPull A p.hom.left).obj T)).hom
    (properOpenProjection A s.hom.left
      ((ProperOpenShriek A i.hom.left).obj ((ProperOpenPush A q.hom.left).obj M)) L)
    _ _ (finiteC F A j b p s (finiteInput F A j i q s K L))
    (by
      dsimp only [a, gamma, Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj]
      exact hm.trans (congrArg (fun t ↦ t ≫ _ ≫ _) hc)) hn.symm
  dsimp only [a, v, gamma, M, T, Functor.mapIso_inv, Iso.app_inv,
    finiteInput, Functor.comp_obj] at hw ⊢
  exact hw

end TriangleProjection
end AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

end AlgebraicGeometry.ProEtale.AmbientProperOpen
