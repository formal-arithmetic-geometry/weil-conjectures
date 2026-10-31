/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.SmoothRepresentingPair
public import WeilConjectures.AlgebraicGeometry.EtaleLocalNormalForm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.TowerConstructibleShifts
import WeilConjectures.AlgebraicGeometry.TowerOpenCoverGeneration
import WeilConjectures.AlgebraicGeometry.TowerRepresentingPairFiniteEvaluation
import WeilConjectures.AlgebraicGeometry.TowerRepresentingPairScalarChange
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Gluing the representing-pair Hom bijection

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs
(blueprint: lem-dla1-tower-representing-pair-five-lemma).

The local pairs are written in their specified identifications with restrictions
of the proposed global pair. This removes redundant isomorphic copies of the
local objects, and fixes all local counits by the open adjunction counit.
Natural-number coefficient level n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

open CategoryTheory.Pretriangulated.Opposite

private theorem open_hom_bijective
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (F : B ⥤ D) (G : A ⥤ D) (e : L ⋙ F ≅ G)
    (H : B) (K : D) (eps : F.obj H ⟶ K) (M : A)
    (hlocal : Function.Bijective (fun z : M ⟶ R.obj H ↦
      G.map z ≫ e.inv.app (R.obj H) ≫ F.map (adj.counit.app H) ≫ eps)) :
    Function.Bijective (fun z : L.obj M ⟶ H ↦ F.map z ≫ eps) := by
  let h := (adj.homEquiv M H).trans (Equiv.ofBijective _ hlocal)
  let e' := Iso.homCongr (e.app M) (Iso.refl K)
  have heq : (fun z : L.obj M ⟶ H ↦ F.map z ≫ eps) =
      fun z ↦ e'.symm (h z) := by
    funext z
    dsimp [e', h, Iso.homCongr]
    simp only [Category.comp_id]
    rw [← e.hom.naturality_assoc]
    simp only [Iso.hom_inv_id_app_assoc, Functor.comp_map, ← F.map_comp_assoc,
      ← adj.homEquiv_counit, Equiv.symm_apply_apply]
  rw [heq]
  exact e'.symm.bijective.comp h.bijective

section Homological

open CategoryTheory.Pretriangulated

variable {A : Type*} [Category* A] [HasZeroObject A] [Preadditive A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  {B : Type*} [Category* B] [Abelian B]

private theorem homological_five (S T : A ⥤ B) [S.IsHomological] [T.IsHomological]
    (τ : S ⟶ T) (Δ : Triangle A) (hΔ : Δ ∈ distTriang A)
    [IsIso (τ.app Δ.obj₁)] [IsIso (τ.app Δ.obj₂)]
    [IsIso (τ.app (Δ.obj₁⟦(1 : ℤ)⟧))] [IsIso (τ.app (Δ.obj₂⟦(1 : ℤ)⟧))] :
    IsIso (τ.app Δ.obj₃) := by
  let row (J : A ⥤ B) : ComposableArrows B 4 :=
    ComposableArrows.mk₄ (J.map Δ.mor₁) (J.map Δ.mor₂) (J.map Δ.mor₃)
      (J.map Δ.rotate.rotate.mor₂)
  have exact_row (J : A ⥤ B) [J.IsHomological] : (row J).Exact := by
    exact ComposableArrows.exact_of_δ₀
      (J.map_distinguished_exact Δ hΔ).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (J.map_distinguished_exact Δ.rotate (rot_of_distTriang _ hΔ)).exact_toComposableArrows
        (J.map_distinguished_exact Δ.rotate.rotate
          (rot_of_distTriang _ (rot_of_distTriang _ hΔ))).exact_toComposableArrows)
  let φ : row S ⟶ row T := ComposableArrows.homMk₄
    (τ.app _) (τ.app _) (τ.app _) (τ.app _) (τ.app _)
    (τ.naturality _) (τ.naturality _) (τ.naturality _) (τ.naturality _)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (exact_row S) (exact_row T) φ
    (by dsimp [φ, row]; infer_instance) (by dsimp [φ, row]; infer_instance)
    (by dsimp [φ, row]; infer_instance)
    (by change Mono (τ.app (Δ.obj₂⟦(1 : ℤ)⟧)); infer_instance)

private def homologicalLocus {S T : A ⥤ B} (τ : S ⟶ T) : ObjectProperty A :=
  fun M ↦ ∀ n : ℤ, IsIso (τ.app (M⟦n⟧))

omit [HasZeroObject A] [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive]
  [Pretriangulated A] [Abelian B] in
private theorem homologicalLocus_iso {S T : A ⥤ B} (τ : S ⟶ T) {M N : A}
    (e : M ≅ N) (hN : homologicalLocus τ N) : homologicalLocus τ M := by
  intro n
  exact (NatTrans.isIso_app_iff_of_iso τ ((shiftFunctor A n).mapIso e)).mpr (hN n)

private instance locus_closed {S T : A ⥤ B} (τ : S ⟶ T) :
    (homologicalLocus τ).IsClosedUnderIsomorphisms where
  of_iso e h := homologicalLocus_iso τ e.symm h

omit [HasZeroObject A] [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive]
  [Pretriangulated A] [Abelian B] in
private theorem locus_shift_shift {S T : A ⥤ B} (τ : S ⟶ T) {M : A}
    (hM : homologicalLocus τ M) (m n : ℤ) : IsIso (τ.app (M⟦m⟧⟦n⟧)) :=
  (NatTrans.isIso_app_iff_of_iso τ ((shiftFunctorAdd A m n).app M)).mp (hM (m + n))

private instance locus_shift {S T : A ⥤ B} (τ : S ⟶ T) :
    (homologicalLocus τ).IsStableUnderShift ℤ where
  isStableUnderShiftBy m := ⟨fun _ hM n ↦ locus_shift_shift τ hM m n⟩

private instance locus_zero {S T : A ⥤ B} [S.IsHomological] [T.IsHomological]
    (τ : S ⟶ T) : (homologicalLocus τ).ContainsZero where
  exists_zero := ⟨0, isZero_zero A, fun n ↦ by
    have hz := (shiftFunctor A n).map_isZero (isZero_zero A)
    have hS := S.map_isZero hz
    have hT := T.map_isZero hz
    exact ⟨⟨0, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩⟩

private instance locus_triangle {S T : A ⥤ B} [S.IsHomological] [T.IsHomological]
    (τ : S ⟶ T) : (homologicalLocus τ).IsTriangulatedClosed₃ :=
  .mk' fun Δ hΔ h₁ h₂ n ↦ by
    have h1 : IsIso (τ.app (Δ.obj₁⟦n⟧)) := h₁ n
    have h2 : IsIso (τ.app (Δ.obj₂⟦n⟧)) := h₂ n
    have h1s : IsIso (τ.app (Δ.obj₁⟦n⟧⟦(1 : ℤ)⟧)) :=
      locus_shift_shift τ h₁ n 1
    have h2s : IsIso (τ.app (Δ.obj₂⟦n⟧⟦(1 : ℤ)⟧)) :=
      locus_shift_shift τ h₂ n 1
    let Δn := (Triangle.shiftFunctor A n).obj Δ
    let : IsIso (τ.app Δn.obj₁) := by
      change IsIso (τ.app (Δ.obj₁⟦n⟧))
      exact h1
    let : IsIso (τ.app Δn.obj₂) := by
      change IsIso (τ.app (Δ.obj₂⟦n⟧))
      exact h2
    let : IsIso (τ.app (Δn.obj₁⟦(1 : ℤ)⟧)) := by
      change IsIso (τ.app (Δ.obj₁⟦n⟧⟦(1 : ℤ)⟧))
      exact h1s
    let : IsIso (τ.app (Δn.obj₂⟦(1 : ℤ)⟧)) := by
      change IsIso (τ.app (Δ.obj₂⟦n⟧⟦(1 : ℤ)⟧))
      exact h2s
    exact homological_five S T τ Δn (Triangle.shift_distinguished Δ hΔ n)

private instance locus_triangulated {S T : A ⥤ B} [S.IsHomological] [T.IsHomological]
    (τ : S ⟶ T) : (homologicalLocus τ).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

end Homological

private def homComparison {A B : Type*} [Category.{v} A] [Category.{v} B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive]
    (H : A) (K : B) (eps : F.obj H ⟶ K) :
    preadditiveYoneda.obj H ⟶ F.op ⋙ preadditiveYoneda.obj K where
  app M := AddCommGrpCat.ofHom
    { toFun := fun z ↦ F.map z ≫ eps
      map_zero' := by simp
      map_add' := by intro x y; rw [F.map_add, Preadditive.add_comp] }
  naturality M N f := by
    ext z
    change F.map (f.unop ≫ z) ≫ eps = F.map f.unop ≫ (F.map z ≫ eps)
    simp only [Functor.map_comp, Category.assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The restriction of the specified counit, with the canonical open composition.
Source: latest blueprint, tower-geometric Gluing paragraph
(blueprint: lem-dla1-tower-representing-pair-five-lemma). -/
def restrictedCounit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : SpTowerCalculus.C l E b q X) (K : SpTowerCalculus.C l E b q Y)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj) (U : X.Opens) :
    (SpTowerCalculus.F l E b o q (c.precomp U.ι)).obj
      ((SpTowerCalculus.etalePullback l E b o q U.ι).obj H.obj) ⟶ K.obj :=
  (SpTowerCalculus.openComposition l E b o q U.ι c).inv.app _ ≫
    (SpTowerCalculus.F l E b o q c).map
      (((((SpTowerCalculus.realization l E b U.toScheme (q.abelian U.toScheme)).toAdjunction.comp
        (o.openOp U.ι).derivedAdjunction).comp
        (SpTowerCalculus.realization l E b X (q.abelian X)).symm.toAdjunction).counit.app
          H.obj)) ≫ eps

/-- Evaluation of the given counit, using the normalized compact-support comparison.
Source: latest blueprint, tower-geometric Levels paragraph
(blueprint: lem-dla1-tower-representing-pair-five-lemma). -/
def finiteCounit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : SpTowerCalculus.C l E b q X) (K : SpTowerCalculus.C l E b q Y)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n) :
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).obj
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj H.obj) ⟶
      (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K.obj :=
  v.comparison.inv.app H.obj ≫
    (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map eps

/-- Transport of a counit along the actual quotient-transition support comparison.
Source: latest blueprint, tower-geometric Levels paragraph
(blueprint: lem-dla1-tower-representing-pair-five-lemma). -/
def scalarCounit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : SpTowerCalculus.C l E b q X) (K : SpTowerCalculus.C l E b q Y)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (m n : ℕ) (h : m ≤ n) (v : SpTowerCalculus.Evaluation l E b o q c n)
    (hb : IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
      c.i c.g).app ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj H.obj))) :
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).obj
      ((scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X).obj
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj H.obj)) ⟶
      (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).obj
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K.obj) :=
  @inv _ _ _ _ ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
    c.i c.g).app ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj H.obj)) hb ≫
    (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y).map
      (finiteCounit l E b o q c H K eps n v)

/-- Local representing pairs imply the representing property for the given global pair.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs
(blueprint: lem-dla1-tower-representing-pair-five-lemma).

Proof:
1. Realization equivalences, exact open extension and unbounded right derived
   direct image make compact support triangulated and compatible with shifts.
   The map z to F(z) followed by eps is an additive natural transformation
   between the two contravariant homological functors on the opposite category.
2. Define its isomorphism locus using every integer shift. Naturality gives
   a map of the five-term exact rows associated to three rotations of a
   distinguished triangle. The abelian five lemma proves that this locus is
   closed under triangles; zero, shifts and isomorphisms give a strictly full
   triangulated subcategory.
3. For each indexed intersection, the open adjunction and openComposition
   identify the local Hom bijection with the global Hom comparison on an
   extended test. The adjunction counit identity is exactly restrictedCounit.
   Apply this also to the negative shifts of the test; constructibility and
   both uniform intervals are preserved by tower_constructible_shift.
4. The finite-type source is Noetherian. Finite-open-cover generation, proved
   from the actual open-cover triangle and finite-union induction, places
   every global test in the isomorphism locus. The zero-shift isomorphism
   gives precisely the first conclusion.
5. Finite evaluation of the tower representing pair gives the second
   conclusion with finiteCounit. Quotient scalar change of those finite
   pairs supplies the inverse comparison and scalarCounit in the third
   conclusion. These are separate coefficient assertions; neither assumes
   an identification of different levels of an unnormalized tower.
-/
theorem tower_representing_pair_five_lemma
    (k : Type u) [Field k] [PerfectField k] (_hell : IsUnit (l : k))
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (r : ℕ) [SmoothOfRelativeDimension r f.left]
    (c : Compactification f.left) (a : ℕ) (U : Fin a → X.left.Opens)
    (_cover : iSup U = ⊤)
    (_charts : ∀ i : Fin a, ∃ e : (U i).toScheme ⟶
      AffineSpace (ULift.{u} (Fin r)) Y.left,
      Etale e ∧ e ≫ (AffineSpace (ULift.{u} (Fin r)) Y.left ↘ Y.left) =
        (U i).ι ≫ f.left)
    (_extension : ∀ (V : X.left.Opens) (M : SpTowerCalculus.C l E b q V.toScheme),
      spConstructibleTorTowers l E X.left (q.abelian X.left)
        ((SpTowerCalculus.openExtension l E b o q V.ι).obj M.obj))
    (K : SpTowerCalculus.C l E b q Y.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (_local : ∀ (s : Finset (Fin a)), s.Nonempty →
      ∀ M : SpTowerCalculus.C l E b q (s.inf U).toScheme,
      Function.Bijective (fun z : M.obj ⟶
          (SpTowerCalculus.etalePullback l E b o q (s.inf U).ι).obj H.obj ↦
        (SpTowerCalculus.F l E b o q (c.precomp (s.inf U).ι)).map z ≫
          restrictedCounit l E b o q c H K eps (s.inf U))) :
    (∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun z : M.obj ⟶ H.obj ↦
        (SpTowerCalculus.F l E b o q c).map z ≫ eps)) ∧
    (∀ (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n)
      (M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n)),
      Function.Bijective (fun z : M.obj ⟶
          (spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj ↦
        (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map z ≫
          finiteCounit l E b o q c H K eps n v)) ∧
    (∀ (m n : ℕ) (h : m ≤ n) (v : SpTowerCalculus.Evaluation l E b o q c n),
      ∃ hb : IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
        c.i c.g).app
          ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj)),
      ∀ M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E m),
        Function.Bijective (fun z : M.obj ⟶
            (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X.left).obj
              ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj) ↦
          (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map z ≫
            scalarCounit l E b o q c H K eps m n h v hb)) := by
  let := (q.abelian X.left).hasDerived
  let := (q.abelian Y.left).hasDerived
  let := b.realizationAdditive X.left
  let := b.realizationAdditive Y.left
  let := b.kinjective c.Z
  let F := SpTowerCalculus.F l E b o q c
  let _ : F.CommShift ℤ := by
    change ((b.realization X.left).functor.mapDerivedCategory ⋙
      ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor) ⋙
      (b.realization Y.left).inverse.mapDerivedCategory).CommShift ℤ
    infer_instance
  have : F.IsTriangulated := by
    change ((b.realization X.left).functor.mapDerivedCategory ⋙
      ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor) ⋙
      (b.realization Y.left).inverse.mapDerivedCategory).IsTriangulated
    infer_instance
  have : F.Additive := by
    change ((b.realization X.left).functor.mapDerivedCategory ⋙
      ((o.openOp c.i).extension.mapDerivedCategory ⋙
        (o.geometry c.g).push.rightDerivedFunctor) ⋙
      (b.realization Y.left).inverse.mapDerivedCategory).Additive
    infer_instance
  let τ := homComparison F H.obj K.obj eps
  let P := (homologicalLocus τ).unop
  have hP : ∀ (s : Finset (Fin a)), s.Nonempty →
      ∀ M : SpTowerCalculus.C l E b q (s.inf U).toScheme,
        P ((SpTowerCalculus.openExtension l E b o q (s.inf U).ι).obj M.obj) := by
    intro s hs M n
    let V := s.inf U
    let := (q.abelian V.toScheme).hasDerived
    let := b.realizationAdditive V.toScheme
    let L := SpTowerCalculus.openExtension l E b o q V.ι
    let R := SpTowerCalculus.etalePullback l E b o q V.ι
    let G := SpTowerCalculus.F l E b o q (c.precomp V.ι)
    let adj : L ⊣ R :=
      (((SpTowerCalculus.realization l E b V.toScheme (q.abelian V.toScheme)).toAdjunction.comp
        (o.openOp V.ι).derivedAdjunction).comp
        (SpTowerCalculus.realization l E b X.left (q.abelian X.left)).symm.toAdjunction)
    let M' : SpTowerCalculus.C l E b q V.toScheme :=
      ⟨M.obj⟦-n⟧, tower_constructible_shift l E b q V.toScheme M (-n)⟩
    have hlocal := _local s hs M'
    have hglobal := open_hom_bijective L R adj F G
      (SpTowerCalculus.openComposition l E b o q V.ι c) H.obj K.obj eps M'.obj hlocal
    have hτ : IsIso (τ.app (Opposite.op (L.obj M'.obj))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hglobal
    let _ : L.CommShift ℤ := by
      change ((b.realization V.toScheme).functor.mapDerivedCategory ⋙
        (o.openOp V.ι).extension.mapDerivedCategory ⋙
        (b.realization X.left).inverse.mapDerivedCategory).CommShift ℤ
      infer_instance
    let e := (L.commShiftIso (-n)).app M.obj
    exact (NatTrans.isIso_app_iff_of_iso τ e.op).mpr hτ
  have hglobal : ∀ M : SpTowerCalculus.C l E b q X.left,
      Function.Bijective (fun z : M.obj ⟶ H.obj ↦ F.map z ≫ eps) := by
    intro M
    let : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    have hM := tower_finite_open_cover_generation l E b o q X.left a U _cover P hP M
    have hτ : IsIso (τ.app (Opposite.op M.obj)) :=
      (NatTrans.isIso_app_iff_of_iso τ
        ((shiftFunctorZero _ ℤ).app (Opposite.op M.obj))).mp (hM 0)
    exact ConcreteCategory.bijective_of_isIso (τ.app (Opposite.op M.obj))
  have hfinite := tower_representing_pair_finite_evaluation l E b o q
    k _hell X Y f r c K H eps hglobal
  exact ⟨hglobal, hfinite, tower_representing_pair_scalar_change l E b o q
    k _hell X Y f r c K H eps hfinite⟩

end AlgebraicGeometry.ProEtale.SpTowerGluing
