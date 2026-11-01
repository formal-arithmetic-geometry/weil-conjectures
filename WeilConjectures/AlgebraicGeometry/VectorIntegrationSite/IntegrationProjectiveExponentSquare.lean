/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.IntegrationExponentTransposeData

import all WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateNormalizedCoherence
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.P1KummerTraceSiteTransport
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology

/-! # Root transitions and the forward projective decomposition square

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-amb-vector-bundle-purity.proof.md, projective-line diagonal and ordinary adjunctions;
accepted exponent-transport proof Steps 6--7; Stacks, Tag 03PK, section-kummer.
(blueprint: lem-pur-projective-exponent-square)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

attribute [local implicit_reducible] Scheme.rootsOfUnitySheaf Scheme.finiteEtaleTateTwist
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor

private theorem single_shift_transition
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (I : C ⥤ C') (J : D ⥤ D') (G : C' ⥤ D')
    (SX : C' ⥤ C') (SY : D' ⥤ D')
    (α : I ⋙ G ≅ F ⋙ J) (β : SX ⋙ G ≅ G ⋙ SY)
    {X Y : C} {Z : D} (t : X ⟶ Y) (br : F.obj Y ≅ Z) (bs : F.obj X ≅ Z)
    (ht : F.map t ≫ br.hom = bs.hom) :
    G.map (SX.map (I.map t)) ≫ β.hom.app (I.obj Y) ≫
        SY.map (α.hom.app Y ≫ J.map br.hom) =
      β.hom.app (I.obj X) ≫ SY.map (α.hom.app X ≫ J.map bs.hom) := by
  rw [reassoc_of% β.hom.naturality (I.map t)]
  rw [← SY.map_comp]
  congr 1
  rw [reassoc_of% α.hom.naturality t, ← J.map_comp, ht]

private theorem transition_comparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (comparison (Scheme.finiteTateCoefficient l E n) T).map
        (integrationLineTransition l E n T hT r s hrs hr hs).hom ≫
      (twistDerived l E n T hT r hr 1 2).hom =
        (twistDerived l E n T hT s hs 1 2).hom := by
  have ht :
      (comparisonUpperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).map
          (exponentTransition l E n T hT r s hrs hr hs 1).hom ≫
        (twistComparison l E n T hT r hr 1).hom =
          (twistComparison l E n T hT s hs 1).hom := by
    simpa only [exponentTransition, twistComparison, Iso.trans_hom, Functor.mapIso_hom]
      using congrArg Iso.hom
        (((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1
          T hT r s hrs hr hs 1).exists.choose_spec.2)
  let F := comparisonUpperStar
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T
  have h := single_shift_transition F (DerivedCategory.singleFunctor _ 0)
    (DerivedCategory.singleFunctor _ 0)
    (comparison (Scheme.finiteTateCoefficient l E n) T)
    (shiftFunctor _ (2 : ℤ)) (shiftFunctor _ (2 : ℤ))
    (F.mapDerivedCategorySingleFunctor 0)
    ((comparison (Scheme.finiteTateCoefficient l E n) T).commShiftIso (2 : ℤ))
    (exponentTransition l E n T hT r s hrs hr hs 1).hom
    (twistComparison l E n T hT r hr 1) (twistComparison l E n T hT s hs 1) ht
  simpa only [integrationLineTransition, twistDerived, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom] using h

-- Normalization and shifted naturality, following OrderedTateExponentPullback.
-- These helpers keep the root-generator calculation within this module.
private theorem integration_single_square
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (S : C₀ ⥤ C) (T : D₀ ⥤ D) (U : C₀ ⥤ D₀) (F : C ⥤ D)
    (c : S ⋙ F ≅ U ⋙ T) {K L : C₀} {K' L' : D₀}
    (a : K ⟶ L) (b : U.obj L ⟶ L') (e : U.obj K ⟶ K') (d : K' ⟶ L')
    (h : U.map a ≫ b = e ≫ d) :
    F.map (S.map a) ≫ (c.hom.app L ≫ T.map b) =
      (c.hom.app K ≫ T.map e) ≫ T.map d := by
  have hn := c.hom.naturality a
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← T.map_comp, h, T.map_comp]

private theorem integration_shift_square
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {K L : C} {K' L' : D}
    (a : K ⟶ L) (b : F.obj L ⟶ L') (c : F.obj K ⟶ K') (d : K' ⟶ L')
    (h : F.map a ≫ b = c ≫ d) (m : ℤ) :
    F.map (a⟦m⟧') ≫ ((F.commShiftIso m).hom.app L ≫ b⟦m⟧') =
      ((F.commShiftIso m).hom.app K ≫ c⟦m⟧') ≫ d⟦m⟧' := by
  have hn := (F.commShiftIso m).hom.naturality a
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, h, Functor.map_comp]

private theorem integration_roots_pullback_value (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A m hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (m : Γ(Y, ⊤)))
    (U : Y.Etaleᵒᵖ) (z : (Y.rootsOfUnitySheaf m).obj.obj U) :
    Scheme.finiteTateEtaleRootValue X m _
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (t.roots f hY).hom).hom.app U z) =
      Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom
        (Scheme.finiteTateEtaleRootValue Y m U z) := by
  have h := congrArg
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
      (t.roots_normalization f hY)
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  unfold Scheme.upperStarGmSheafToGmSheaf at h
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun g ↦ Additive.toMul ((g.hom.app U z).down)) h.symm

private theorem integration_exponent_sheaf_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs) :
    (Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) f).map
        (exponentTransition l E n Y hY r s hrs hr hs 1).hom ≫
      (tr.line f (by simpa only [Nat.cast_pow] using hY.pow (r + 1))).hom =
    (ts.line f (by simpa only [Nat.cast_pow] using hY.pow (s + 1))).hom ≫
      (exponentTransition l E n X (by simpa using hY.map f.appTop.hom)
        r s hrs hr hs 1).hom := by
  let A := Scheme.finiteTateCoefficient l E n
  let hX : IsUnit (l : Γ(X, ⊤)) := by simpa using hY.map f.appTop.hom
  have hy := ((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1
    Y hY r s hrs hr hs 1).exists.choose_spec.1
  have hx := ((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1
    X hX r s hrs hr hs 1).exists.choose_spec.1
  with_unfolding_all
    change Scheme.IsFiniteTateEtaleTransition l E n Y r s hr hs 1
      (exponentTransition l E n Y hY r s hrs hr hs 1) at hy
  with_unfolding_all
    change Scheme.IsFiniteTateEtaleTransition l E n X r s hr hs 1
      (exponentTransition l E n X hX r s hrs hr hs 1) at hx
  obtain ⟨q, _, hq, _⟩ := Scheme.etale_transition_normalized l E n Y hY r s hrs hr hs 1
  apply ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply (Scheme.lineHomEquiv Y (l ^ (s + 1)) A hs _).injective
  ext U z
  simp only [Scheme.lineHomEquiv_generator]
  change ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      (tr.line f _).hom).hom.app U
      ((exponentTransition l E n Y hY r s hrs hr hs 1).hom.hom.app U
        (Scheme.finiteEtaleTateOneGenerator A (l ^ (s + 1)) Y hs U 1 z)) =
    (exponentTransition l E n X hX r s hrs hr hs 1).hom.hom.app _
      (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
        (ts.line f _).hom).hom.app U
          (Scheme.finiteEtaleTateOneGenerator A (l ^ (s + 1)) Y hs U 1 z))
  have hyz := hy U 1 (fun _ ↦ z) (fun _ ↦ q.hom.app U z) (fun _ ↦ hq U z)
  change (exponentTransition l E n Y hY r s hrs hr hs 1).hom.hom.app U
      (Scheme.finiteEtaleTateOneGenerator A (l ^ (s + 1)) Y hs U 1 z) =
    Scheme.finiteEtaleTateOneGenerator A (l ^ (r + 1)) Y hr U 1
      (q.hom.app U z) at hyz
  rw [hyz, tr.line_normalization, ts.line_normalization]
  symm
  apply hx _ 1 (fun _ ↦ _) (fun _ ↦ _)
  intro i
  rw [integration_roots_pullback_value, integration_roots_pullback_value, hq, map_pow]
  rfl

private theorem integration_shifted_line_square (A : Type (u + 1)) [CommRing A]
    (Nr Ns : ℕ) (hr : (Nr : A) = 0) (hs : (Ns : A) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport A Nr hr)
    (ts : Etale.OrdinaryFiniteTwistTransport A Ns hs)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hYr : IsUnit (Nr : Γ(Y, ⊤))) (hYs : IsUnit (Ns : Γ(Y, ⊤)))
    (a : Scheme.finiteEtaleTateLine Y Ns A hs ⟶ Scheme.finiteEtaleTateLine Y Nr A hr)
    (b : Scheme.finiteEtaleTateLine X Ns A hs ⟶ Scheme.finiteEtaleTateLine X Nr A hr)
    (h : (Etale.upperStar (ModuleCat.{u + 1} A) f).map a ≫ (tr.line f hYr).hom =
      (ts.line f hYs).hom ≫ b) :
    (Etale.ordinaryFinitePullback A f).map
        (((DerivedCategory.singleFunctor _ 0).map a)⟦(2 : ℤ)⟧') ≫
      (Etale.ordinaryFiniteShiftedLinePullback A Nr hr tr f hYr).hom =
    (Etale.ordinaryFiniteShiftedLinePullback A Ns hs ts f hYs).hom ≫
      ((DerivedCategory.singleFunctor _ 0).map b)⟦(2 : ℤ)⟧' := by
  have h₀ := integration_single_square (Etale.ordinaryFiniteSingleFunctor A Y)
    (Etale.ordinaryFiniteSingleFunctor A X) (Etale.upperStar (ModuleCat.{u + 1} A) f)
    (Etale.ordinaryFinitePullback A f) (Etale.ordinaryFiniteSinglePullbackIso A f)
    a (tr.line f hYr).hom (ts.line f hYs).hom b h
  let : (Etale.ordinaryFinitePullback A f).CommShift ℤ :=
    Etale.commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have h₂ := integration_shift_square (Etale.ordinaryFinitePullback A f)
    ((Etale.ordinaryFiniteSingleFunctor A Y).map a) _ _
    ((Etale.ordinaryFiniteSingleFunctor A X).map b) h₀ (2 : ℤ)
  simpa only [Etale.ordinaryFiniteShiftedLinePullback_eq, Iso.trans_hom,
    Iso.app, Functor.mapIso_hom, Functor.map_comp,
    Etale.ordinaryFiniteSingleFunctor_eq, Etale.ordinaryFiniteLine,
    Etale.ordinaryFiniteDegreeZero, Category.assoc] using h₂

private theorem transition_pullback (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs) :
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n) f).map
        (integrationLineTransition l E n Y hY r s hrs hr hs).hom ≫
      (Etale.ordinaryFiniteShiftedLinePullback _ (l ^ (r + 1)) hr tr f
        (by simpa only [Nat.cast_pow] using hY.pow (r + 1))).hom =
    (Etale.ordinaryFiniteShiftedLinePullback _ (l ^ (s + 1)) hs ts f
        (by simpa only [Nat.cast_pow] using hY.pow (s + 1))).hom ≫
      (integrationLineTransition l E n X
        (by simpa using hY.map f.appTop.hom) r s hrs hr hs).hom := by
  let A := Scheme.finiteTateCoefficient l E n
  have h := integration_shifted_line_square A (l ^ (r + 1)) (l ^ (s + 1)) hr hs tr ts f
    (by simpa only [Nat.cast_pow] using hY.pow (r + 1))
    (by simpa only [Nat.cast_pow] using hY.pow (s + 1))
    (exponentTransition l E n Y hY r s hrs hr hs 1).hom
    (exponentTransition l E n X (by simpa using hY.map f.appTop.hom)
      r s hrs hr hs 1).hom
    (integration_exponent_sheaf_pullback l E n f hY r s hrs hr hs tr ts)
  simpa only [integrationLineTransition, Functor.mapIso_hom] using h

private theorem ordinary_chern_transition (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (kummerTraceOrdinaryDatum l E n S hS s hs).chern ≫
      (integrationLineTransition l E n (ProjectiveLine S)
        (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)
        r s hrs hr hs).hom =
    (kummerTraceOrdinaryDatum l E n S hS r hr).chern := by
  let A := Scheme.finiteTateCoefficient l E n
  let P := ProjectiveLine S
  let hP : IsUnit (l : Γ(P, ⊤)) := by
    simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom
  apply (bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) (X := P) _ _ (linePlus l E n r hr P).property).1
  change (comparison A P).map (_ ≫ _) = (comparison A P).map _
  rw [Functor.map_comp, compare_chern, compare_chern]
  dsimp [P]
  apply (cancel_mono (twistDerived l E n P hP r hr 1 2).hom).1
  rw [Category.assoc, transition_comparison]
  unfold projectiveChern
  simp [Category.assoc]

private theorem compared_square
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesBinaryBiproducts F]
    {X X' U Y Y' : C} {Z Z' : D}
    (br : X' ⊞ U ≅ Y') (bs : X ⊞ U ≅ Y)
    (e : X ⟶ X') (q : Y ⟶ Y') (p : Z ⟶ Z')
    (βr : F.obj Y' ≅ Z') (βs : F.obj Y ≅ Z)
    (pr : F.obj X' ⊞ F.obj U ⟶ Z') (ps : F.obj X ⊞ F.obj U ⟶ Z)
    (hr : F.map br.hom ≫ βr.hom = (F.mapBiprod X' U).hom ≫ pr)
    (hs : F.map bs.hom ≫ βs.hom = (F.mapBiprod X U).hom ≫ ps)
    (hq : F.map q ≫ βr.hom = βs.hom ≫ p)
    (hb : bs.hom ≫ q = biprod.map e (𝟙 U) ≫ br.hom) :
    ps ≫ p = biprod.map (F.map e) (𝟙 (F.obj U)) ≫ pr := by
  have hn : F.map (biprod.map e (𝟙 U)) ≫ (F.mapBiprod X' U).hom =
      (F.mapBiprod X U).hom ≫ biprod.map (F.map e) (𝟙 (F.obj U)) := by
    simp only [Functor.mapBiprod_hom]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst]
      rw [← Category.assoc, biprod.lift_fst, ← F.map_comp, biprod.map_fst]
      exact F.map_comp _ _
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, Category.comp_id]
      rw [← F.map_comp, biprod.map_snd, Category.comp_id]
  apply (cancel_epi (F.mapBiprod X U).hom).1
  calc
    (F.mapBiprod X U).hom ≫ ps ≫ p = F.map bs.hom ≫ βs.hom ≫ p := by
      rw [← Category.assoc, ← hs, Category.assoc]
    _ = F.map (bs.hom ≫ q) ≫ βr.hom := by
      rw [← hq, Functor.map_comp, Category.assoc]
    _ = F.map (biprod.map e (𝟙 U)) ≫ (F.mapBiprod X' U).hom ≫ pr := by
      rw [hb, Functor.map_comp, Category.assoc, hr]
    _ = (F.mapBiprod X U).hom ≫ biprod.map (F.map e) (𝟙 _) ≫ pr := by
      rw [← Category.assoc, hn, Category.assoc]

/-- Root-power transitions preserve the actual ordinary projective decomposition and
supported pro-etale projective decomposition, in the forward direction.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-amb-vector-bundle-purity.proof.md, final sentence; accepted parent proof Steps 6--7;
Stacks, Tag 03PK, section-kummer (blueprint: lem-pur-projective-exponent-square).

Proof:
1. Prove the normalized sheaf transition square on root generators and lift it
   through the degree-zero embedding and shift. Finite Tate descent and the
   naturality of the single-degree and shift comparisons identify the transition
   under site comparison. The supported Chern comparison and faithfulness on bounded
   targets then give the ordinary Chern transition equation.
2. Adjunction naturality gives the ordinary unit and pushed Chern component squares.
   Their biproduct universal property gives the ordinary forward square.
3. Use projectiveB_isIso for the prescribed pro-etale decomposition isomorphisms.
   The general Noetherian decomposition comparison and naturality of the fixed proper
   direct-image mate transport the ordinary square to the pro-etale square.
-/
theorem integrationProjectiveExponentSquare (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
  IntegrationDecompositionSquare
    (integrationLineTransition l E n S hS r s hrs hr hs).hom
    ((Etale.ordinaryFinitePushforward _ (ProjectiveLine S ↘ S)).map
      (integrationLineTransition l E n (ProjectiveLine S)
        (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) r s hrs hr hs).hom)
    (kummerTraceOrdinaryDatum l E n S hS r hr).decomposition
    (kummerTraceOrdinaryDatum l E n S hS s hs).decomposition ∧
  ∃ (br : (line l E n r hr S ⊞ unit (Scheme.finiteTateCoefficient l E n) S) ≅
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n r hr (ProjectiveLine S)))
    (bs : (line l E n s hs S ⊞ unit (Scheme.finiteTateCoefficient l E n) S) ≅
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n s hs (ProjectiveLine S))),
    br.hom = projectiveB l E n S hS (infinityCartier S) r hr ∧
    bs.hom = projectiveB l E n S hS (infinityCartier S) s hs ∧
    IntegrationDecompositionSquare
      ((comparison (Scheme.finiteTateCoefficient l E n) S).map
        (integrationLineTransition l E n S hS r s hrs hr hs).hom)
      ((lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.map
          ((comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
            (integrationLineTransition l E n (ProjectiveLine S)
              (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom)
              r s hrs hr hs).hom)) br bs := by
  let A := Scheme.finiteTateCoefficient l E n
  let q := ProjectiveLine S ↘ S
  let P := ProjectiveLine S
  let hP : IsUnit (l : Γ(P, ⊤)) := by simpa using hS.map q.appTop.hom
  let eS := (integrationLineTransition l E n S hS r s hrs hr hs).hom
  let eP := (integrationLineTransition l E n P hP r s hrs hr hs).hom
  let dr := kummerTraceOrdinaryDatum l E n S hS r hr
  let ds := kummerTraceOrdinaryDatum l E n S hS s hs
  let R := Etale.ordinaryFinitePushforward A q
  let adj := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q
  have hline := transition_pullback l E n q hS r s hrs hr hs
    (Etale.projectiveLineTraceTransport (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hr)
    (Etale.projectiveLineTraceTransport (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hs)
  have hchern := ordinary_chern_transition l E n S hS r s hrs hr hs
  have hu : Etale.ordinaryFiniteP1Unit A (l ^ (s + 1)) hs
        (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) A hs)
        S (by simpa only [Nat.cast_pow] using hS.pow (s + 1)) ≫ R.map eP =
      eS ≫ Etale.ordinaryFiniteP1Unit A (l ^ (r + 1)) hr
        (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) A hr)
        S (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) := by
    unfold Etale.ordinaryFiniteP1Unit
    change adj.homEquiv _ _ _ ≫ R.map eP = eS ≫ adj.homEquiv _ _ _
    dsimp only [R, Etale.ordinaryFinitePushforward]
    rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
    exact congrArg (adj.homEquiv _ _) hline.symm
  have hh : Etale.ordinaryFiniteP1ChernPushforward A (l ^ (s + 1)) hs S ds.chern ≫
        R.map eP = Etale.ordinaryFiniteP1ChernPushforward A (l ^ (r + 1)) hr S
          dr.chern := by
    unfold Etale.ordinaryFiniteP1ChernPushforward
    dsimp only [R, Etale.ordinaryFinitePushforward]
    rw [← adj.homEquiv_naturality_right, Category.assoc, hchern]
  have hb : ds.decomposition.hom ≫ R.map eP =
      biprod.map eS (𝟙 _) ≫ dr.decomposition.hom := by
    rw [ds.decomposition_hom, dr.decomposition_hom]
    apply biprod.hom_ext'
    · simpa only [biprod.inl_desc_assoc, biprod.inl_map_assoc,
        biprod.inl_desc, Category.assoc] using hu
    · simpa only [biprod.inr_desc_assoc, biprod.inr_map_assoc,
        biprod.inr_desc, Category.id_comp] using hh
  refine ⟨hb, ?_⟩
  let := projectiveB_isIso l E n S hS (infinityCartier S) r hr
  let := projectiveB_isIso l E n S hS (infinityCartier S) s hs
  refine ⟨asIso (projectiveB l E n S hS (infinityCartier S) r hr),
    asIso (projectiveB l E n S hS (infinityCartier S) s hs), rfl, rfl, ?_⟩
  let C := comparison A S
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts C
  apply compared_square C dr.decomposition ds.decomposition eS (R.map eP)
    ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
      ((comparison A P).map eP))
    (directImage A q (linePlus l E n r hr P))
    (directImage A q (linePlus l E n s hs P))
    (projectiveB l E n S hS (infinityCartier S) r hr)
    (projectiveB l E n S hS (infinityCartier S) s hs)
  · simpa only [projectiveSum, Functor.mapBiprod_hom] using
      decomposition l E n S hS r hr (compare_chern l E n S hS r hr)
  · simpa only [projectiveSum, Functor.mapBiprod_hom] using
      decomposition l E n S hS s hs (compare_chern l E n S hS s hs)
  · rw [directImage_hom, directImage_hom]
    exact pushComparison_naturality A q eP
  · exact hb

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
