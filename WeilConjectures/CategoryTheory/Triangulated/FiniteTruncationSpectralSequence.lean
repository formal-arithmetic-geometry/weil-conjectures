/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HalfPlaneConvergence
public import WeilConjectures.CategoryTheory.TruncationHypercohomology
public import WeilConjectures.CategoryTheory.Triangulated.CoefficientStageDescent
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import WeilConjectures.CategoryTheory.AbutmentImageFiltration
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import all Mathlib.CategoryTheory.Triangulated.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Shift.ShiftSequence
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import WeilConjectures.CategoryTheory.ExactFunctorCouple

/-! # Finite canonical truncation spectral sequences

Source: BBD, §1.3.3–1.3.7; Stacks Tags 011R, 011S, 012W; the first paragraph of
`lem-zl-composition-weight-bound.proof.md` in the latest blueprint
(blueprint: lem-zl-finite-truncation-spectral-sequence).

The structures package the conclusions, including the equations specifying the canonical
maps. They do not choose a spectral sequence from a bare existence assertion. Cohomology
in a heart is `shiftFunctor _ n ⋙ t.homology₀`. The existing ambient cohomology convention
`CoefficientStageDescent.cohomology` identifies the adjacent truncation layer shifted by n.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uD vD uB vB uA vA wA wB

namespace CategoryTheory.Triangulated

open Limits Pretriangulated TStructure

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]

/-- The D-terms, before packaging exactness. Source: BBD 1.3.3–1.3.6
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationD (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    (a b : ℤ) : C ⥤ s.heart.FullSubcategory :=
  t.truncLT (b + 1) ⋙ T ⋙ shiftFunctor D (a + b) ⋙ s.homology₀

/-- The adjacent-layer terms, before the canonical E₂ shift identification.
Source: BBD 1.3.3–1.3.6 (blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationE (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    (a b : ℤ) : C ⥤ s.heart.FullSubcategory :=
  t.truncGELT b (b + 1) ⋙ T ⋙ shiftFunctor D (a + b) ⋙ s.homology₀

/-- The canonical shift identification of a layer term with Hᵃ(T(HᵇK)).
Source: BBD 1.3.6 and the prescribed shift comparison of T
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationE₂Iso (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    [T.CommShift ℤ] (K : C) (a b : ℤ) :
    (finiteTruncationE t s T a b).obj K ≅
      (shiftFunctor D a ⋙ s.homology₀).obj
        (T.obj ((CoefficientStageDescent.cohomology t b).obj K)) :=
  s.homology₀.mapIso
    ((shiftFunctorAdd' D b a (a + b) (by omega)).app
        (T.obj ((t.truncGELT b (b + 1)).obj K)) ≪≫
      (shiftFunctor D a).mapIso
        ((T.commShiftIso b).app ((t.truncGELT b (b + 1)).obj K)).symm)

/-- The connecting arrow of the adjacent-layer triangle after T and Hᵃ⁺ᵇ.
Source: BBD 1.3.3–1.3.6 (blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationConnecting (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] (K : C) (a b : ℤ) :
    (finiteTruncationE t s T a b).obj K ⟶
      (finiteTruncationD t s T (a + 2) (b - 1)).obj K :=
  s.homology₀.map
    ((shiftFunctor D (a + b)).map
        (T.map ((t.truncGELTδLT b (b + 1)).app K) ≫
          (T.commShiftIso (1 : ℤ)).hom.app ((t.truncLT b).obj K)) ≫
      (shiftFunctorAdd' D 1 (a + b) ((a + 2) + (b - 1)) (by omega)).inv.app
        (T.obj ((t.truncLT b).obj K))) ≫
    eqToHom (by simp only [finiteTruncationD, Functor.comp_obj, sub_add_cancel])

/-- A canonical truncation couple, with its three structure arrows specified.
Source: BBD 1.3.3–1.3.6; Stacks 011Q, 011R, 011S
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
structure FiniteTruncationCouple (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] (K : C) where
  /-- The exact couple in the abelian heart, with the recorded page convention. -/
  X : BigradedExactCouple s.heart.FullSubcategory 0
  /-- Its canonical D-identification. -/
  dIso : ∀ a b : ℤ, X.D a b ≅ (finiteTruncationD t s T a b).obj K
  /-- Its canonical adjacent-layer E-identification. -/
  eIso : ∀ a b : ℤ, X.E a b ≅ (finiteTruncationE t s T a b).obj K
  /-- Alpha is induced by the upper truncation inclusion. -/
  alpha_eq : ∀ a b : ℤ,
    X.alpha a b ≫ (dIso (a - 1) (b + 1)).hom =
      (dIso a b).hom ≫ (shiftFunctor D (a + b) ⋙ s.homology₀).map
        (T.map ((t.natTransTruncLTOfLE (b + 1) (b + 1 + 1) (by omega)).app K)) ≫
        eqToHom (by
          simp only [finiteTruncationD, Functor.comp_obj]
          congr 3; omega)
  /-- The projection is induced by the canonical lower-truncation unit. -/
  g_eq : ∀ a b : ℤ,
    X.initialG a b ≫ (eIso a b).hom = (dIso a b).hom ≫
      (shiftFunctor D (a + b) ⋙ s.homology₀).map
        (T.map ((t.truncGEπ b).app ((t.truncLT (b + 1)).obj K)))
  /-- The connecting arrow, with the given shift comparison and its sign. -/
  f_eq : ∀ a b : ℤ,
    X.f a b ≫ (dIso (a + 2) (b - 1)).hom =
      (eIso a b).hom ≫ finiteTruncationConnecting t s T K a b

/-- The canonical morphism from a truncation term to Hⁿ(TK).
Source: BBD 1.3.3–1.3.6 (blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def FiniteTruncationCouple.toAbutment {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] {K : C}
    (S : FiniteTruncationCouple t s T K) (n p : ℤ) :
    S.X.D p (n - p) ⟶ (shiftFunctor D n ⋙ s.homology₀).obj (T.obj K) :=
  (S.dIso p (n - p)).hom ≫ eqToHom (by
      simp only [finiteTruncationD, Functor.comp_obj]
      congr 3; omega) ≫
    (shiftFunctor D n ⋙ s.homology₀).map
      (T.map ((t.truncLTι (n - p + 1)).app K))

/-- Convergence with the literal cohomology object as diagonal colimit, and the canonical
infinite-page/graded comparison. Source: BBD 1.3.3–1.3.7; Stacks 012W
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
structure FiniteTruncationAbutment {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] {K : C}
    (S : FiniteTruncationCouple t s T K) (l u : ℤ) where
  /-- The lower vanishing bound of D. -/
  d_zero : ∀ a b : ℤ, b < l → IsZero (S.X.D a b)
  /-- The finite strip persists on every page (pageCouple r is E_(r+2)). -/
  page_zero : ∀ (r : ℕ) (a b : ℤ),
    a < 0 ∨ b < l ∨ u < b → IsZero ((S.X.pageCouple r).E a b)
  /-- The limiting cycle and boundary subobjects. -/
  limits : S.X.LimitSubobjects
  /-- The alpha diagonal has the stated cohomology as colimit. -/
  abutment : ∀ n : ℤ, S.X.AlphaColimit n
  /-- Its object is exactly Hⁿ(TK). -/
  obj_eq : ∀ n : ℤ, (abutment n).obj =
    (shiftFunctor D n ⋙ s.homology₀).obj (T.obj K)
  /-- The cocone consists of the canonical truncation counits. -/
  map_eq : ∀ n p : ℤ,
    (abutment n).ι p ≫ eqToHom (obj_eq n) = S.toAbutment n p
  /-- The image filtration is finite. -/
  finite : ∀ n : ℤ, (S.X.imageFiltration n (abutment n)).IsFinite
  /-- It is exhaustive. -/
  exhaustive : ∀ n : ℤ, (S.X.imageFiltration n (abutment n)).IsExhaustive
  /-- It is separated. -/
  separated : ∀ n : ℤ, (S.X.imageFiltration n (abutment n)).IsSeparated
  /-- Regularity of the couple. -/
  regular : S.X.IsRegular
  /-- Completeness of the couple. -/
  complete : S.X.IsComplete
  /-- Convergence in the recorded exact-couple sense. -/
  converges : S.X.ConvergesTo limits abutment
  /-- The canonical isomorphism from the infinite page to the graded image filtration. -/
  graded : ∀ a b : ℤ, S.X.pageInfinity limits a b ≅
    (S.X.imageFiltration (a + b) (abutment (a + b))).gradedPiece a
  /-- Its normalization by the canonical maps, not an arbitrary graded isomorphism. -/
  graded_eq : ∀ a b : ℤ,
    S.X.toPageInfinity limits a b ≫ (graded a b).hom =
      S.X.toGradedPiece abutment a b

/-- Compatibility of all derived couples, their image inclusions and page quotient maps.
This packages maps, rather than asserting an uncharacterized isomorphism of pages.
Source: Stacks 011R, 011S and BBD 1.3.3(ii)
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
structure FiniteTruncationPageMap (s : TStructure D)
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (Φ : s.heart.FullSubcategory ⥤ B)
    (X : BigradedExactCouple s.heart.FullSubcategory 0)
    (Y : BigradedExactCouple B 0) where
  /-- Maps of all D terms. -/
  dMap : ∀ (r : ℕ) (a b : ℤ),
    Φ.obj ((X.pageCouple r).D a b) ⟶ (Y.pageCouple r).D a b
  /-- Maps of all E terms. -/
  eMap : ∀ (r : ℕ) (a b : ℤ),
    Φ.obj ((X.pageCouple r).E a b) ⟶ (Y.pageCouple r).E a b
  /-- Alpha compatibility. -/
  alpha_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map ((X.pageCouple r).alpha a b) ≫ dMap r (a - 1) (b + 1) =
      dMap r a b ≫ (Y.pageCouple r).alpha a b
  /-- Connecting-arrow compatibility. -/
  f_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map ((X.pageCouple r).f a b) ≫ dMap r (a + 2) (b - 1) =
      eMap r a b ≫ (Y.pageCouple r).f a b
  /-- Projection compatibility. -/
  g_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map ((X.pageCouple r).g a b) ≫ eMap r (a + r) (b - r) =
      dMap r a b ≫ (Y.pageCouple r).g a b
  /-- Differential compatibility. -/
  differential_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map ((X.pageCouple r).d a b) ≫ eMap r (a + 2 + r) (b - 1 - r) =
      eMap r a b ≫ (Y.pageCouple r).d a b
  /-- The derived D maps are induced on images. -/
  image_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map ((X.pageCouple r).derivedDInclusion a b) ≫ dMap r a b =
      dMap (r + 1) a b ≫ (Y.pageCouple r).derivedDInclusion a b
  /-- The induced maps on cycles. -/
  cycles : ∀ (r : ℕ) (a b : ℤ),
    Φ.obj (kernel ((X.pageCouple r).d a b)) ⟶ kernel ((Y.pageCouple r).d a b)
  /-- Cycle inclusion compatibility. -/
  cycles_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map (kernel.ι ((X.pageCouple r).d a b)) ≫ eMap r a b =
      cycles r a b ≫ kernel.ι ((Y.pageCouple r).d a b)
  /-- Each next-page map is induced by the quotient of cycles. -/
  quotient_comm : ∀ (r : ℕ) (a b : ℤ),
    Φ.map ((X.pageCouple r).derivedEProjection a b) ≫ eMap (r + 1) a b =
      cycles r a b ≫ (Y.pageCouple r).derivedEProjection a b

/-- Compatibility at the finite filtered abutment, including the normalized graded maps.
Source: Stacks 012W; BBD 1.3.3(ii)
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
structure FiniteTruncationFilteredMap {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] {K K' : C}
    {S : FiniteTruncationCouple t s T K} {S' : FiniteTruncationCouple t s T K'}
    {l u l' u' : ℤ} (A : FiniteTruncationAbutment S l u)
    (A' : FiniteTruncationAbutment S' l' u')
    (Φ : s.heart.FullSubcategory ⥤ s.heart.FullSubcategory)
    (M : FiniteTruncationPageMap s Φ S.X S'.X) where
  /-- The map of abutment objects. -/
  hom : ∀ n : ℤ, Φ.obj (A.abutment n).obj ⟶ (A'.abutment n).obj
  /-- Compatibility with the entire diagonal cocone. -/
  cocone_comm : ∀ n p : ℤ,
    Φ.map ((A.abutment n).ι p) ≫ hom n =
      M.dMap 0 p (n - p) ≫ (A'.abutment n).ι p
  /-- Maps on all image-filtration terms. -/
  step : ∀ n p : ℤ,
    Φ.obj ((S.X.imageFiltration n (A.abutment n)).step p : s.heart.FullSubcategory) ⟶
      ((S'.X.imageFiltration n (A'.abutment n)).step p : s.heart.FullSubcategory)
  /-- Filtration inclusion compatibility. -/
  step_comm : ∀ n p : ℤ,
    Φ.map (((S.X.imageFiltration n (A.abutment n)).step p).arrow) ≫ hom n =
      step n p ≫ ((S'.X.imageFiltration n (A'.abutment n)).step p).arrow
  /-- The induced map on associated graded objects. -/
  graded : ∀ n p : ℤ,
    Φ.obj ((S.X.imageFiltration n (A.abutment n)).gradedPiece p) ⟶
      (S'.X.imageFiltration n (A'.abutment n)).gradedPiece p
  /-- It is induced on the quotient by the next filtration step. -/
  quotient_comm : ∀ n p : ℤ,
    Φ.map (cokernel.π (Subobject.ofLE
      ((S.X.imageFiltration n (A.abutment n)).step (p + 1))
      ((S.X.imageFiltration n (A.abutment n)).step p)
      ((S.X.imageFiltration n (A.abutment n)).antitone_step (by omega)))) ≫ graded n p =
    step n p ≫ cokernel.π (Subobject.ofLE
      ((S'.X.imageFiltration n (A'.abutment n)).step (p + 1))
      ((S'.X.imageFiltration n (A'.abutment n)).step p)
      ((S'.X.imageFiltration n (A'.abutment n)).antitone_step (by omega)))
  /-- The infinite-page map. -/
  infinity : ∀ a b : ℤ,
    Φ.obj (S.X.pageInfinity A.limits a b) ⟶ S'.X.pageInfinity A'.limits a b
  /-- Its canonical normalization. -/
  infinity_comm : ∀ a b : ℤ,
    Φ.map (S.X.toPageInfinity A.limits a b) ≫ infinity a b =
      M.dMap 0 a b ≫ S'.X.toPageInfinity A'.limits a b
  /-- Naturality of the canonical infinite-page/graded identification. -/
  graded_comm : ∀ a b : ℤ,
    Φ.map (A.graded a b).hom ≫ graded (a + b) a =
      infinity a b ≫ (A'.graded a b).hom

/-- Restrict a t-exact endofunctor to the existing heart, using the existing restriction.
Source: BBD 1.3.17 (blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationHeartAction (s : TStructure D) (Q : D ⥤ D) [Q.IsTExact s s] :
    s.heart.FullSubcategory ⥤ s.heart.FullSubcategory :=
  CoefficientStageDescent.heartRestriction s s Q (fun X h ↦ by
    let : s.IsLE X 0 := ⟨h.1⟩
    let : s.IsGE X 0 := ⟨h.2⟩
    exact ⟨(Functor.IsTExact.isLE_obj s s Q X 0).le,
      (Functor.IsTExact.isGE_obj s s Q X 0).ge⟩)

/-- The canonical t-exact cohomology comparison Q_B Hⁿ ≅ Hⁿ Q, obtained from the
upper and lower truncation comparisons at zero and then the prescribed shift comparison.
Source: BBD 1.3.3, 1.3.6 (blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationHeartComparison (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s] (V : D) (n : ℤ) :
    (finiteTruncationHeartAction s Q).obj ((shiftFunctor D n ⋙ s.homology₀).obj V) ≅
      (shiftFunctor D n ⋙ s.homology₀).obj (Q.obj V) :=
  ObjectProperty.isoMk s.heart
    (Q.eTruncGELTIsoApp s s 0 1 ((shiftFunctor D n).obj V) ≪≫
      (s.truncGELT 0 1).mapIso ((Q.commShiftIso n).app V))

/-- The equivariant map of the truncation tower specified in the node.
The comparison P τ≤b ≅ τ≤b P is the published canonical comparison.
Source: BBD 1.3.3(ii); explicit tower map in the node's proof, Step 7
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationTowerIso (t : TStructure C) (T : C ⥤ D)
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) (K : C) (θ : P.functor.obj K ≅ K) (b : ℤ) :
    Q.functor.obj (T.obj ((t.truncLT (b + 1)).obj K)) ≅
      T.obj ((t.truncLT (b + 1)).obj K) :=
  β.app ((t.truncLT (b + 1)).obj K) ≪≫
    T.mapIso ((P.functor.eTruncLTIso t t (b + 1 : ℤ)).app K) ≪≫
    T.mapIso ((t.truncLT (b + 1)).mapIso θ)

/-- The equivariant map on an adjacent truncation layer. Source: BBD 1.3.3(ii),
1.3.6 (blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationLayerIso (t : TStructure C) (T : C ⥤ D)
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) (K : C) (θ : P.functor.obj K ≅ K) (b : ℤ) :
    Q.functor.obj (T.obj ((t.truncGELT b (b + 1)).obj K)) ≅
      T.obj ((t.truncGELT b (b + 1)).obj K) :=
  β.app ((t.truncGELT b (b + 1)).obj K) ≪≫
    T.mapIso (P.functor.eTruncGELTIsoApp t t (b : EInt) ((b + 1 : ℤ) : EInt) K) ≪≫
    T.mapIso ((t.truncGELT b (b + 1)).mapIso θ)

private instance heartAction_additive (s : TStructure D) (Q : D ⥤ D)
    [Q.IsTExact s s] [Q.Additive] : (finiteTruncationHeartAction s Q).Additive where
  map_add := by
    intro X Y f g
    apply s.heart.ι.map_injective
    exact Q.map_add

private theorem heartAction_exact (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s]
    (S : ShortComplex s.heart.FullSubcategory) (hS : S.ShortExact) :
    (S.map (finiteTruncationHeartAction s Q)).ShortExact := by
  let := s.hasHeartFullSubcategory
  obtain ⟨δ, hδ⟩ := (s.shortExact_iff_exists_distTriang S).1 hS
  apply (s.shortExact_iff_exists_distTriang _).2
  exact ⟨Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app _, Q.map_distinguished _ hδ⟩

private instance heartAction_limits (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s] :
    PreservesFiniteLimits (finiteTruncationHeartAction s Q) := by
  have h : PreservesFiniteLimits (finiteTruncationHeartAction s Q) ∧
      PreservesFiniteColimits (finiteTruncationHeartAction s Q) :=
    ((finiteTruncationHeartAction s Q).exact_tfae.out 0 3).mp (heartAction_exact s Q)
  exact h.1

private instance heartAction_colimits (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s] :
    PreservesFiniteColimits (finiteTruncationHeartAction s Q) := by
  have h : PreservesFiniteLimits (finiteTruncationHeartAction s Q) ∧
      PreservesFiniteColimits (finiteTruncationHeartAction s Q) :=
    ((finiteTruncationHeartAction s Q).exact_tfae.out 0 3).mp (heartAction_exact s Q)
  exact h.2

private theorem heartComparison_natural (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s]
    {U V : D} (f : U ⟶ V) (n : ℤ) :
    (finiteTruncationHeartAction s Q).map ((shiftFunctor D n ⋙ s.homology₀).map f) ≫
        (finiteTruncationHeartComparison s Q V n).hom =
      (finiteTruncationHeartComparison s Q U n).hom ≫
        (shiftFunctor D n ⋙ s.homology₀).map (Q.map f) := by
  apply s.heart.ι.map_injective
  simp only [Functor.map_comp]
  change Q.map ((s.truncGELT 0 1).map ((shiftFunctor D n).map f)) ≫
      ((Q.eTruncGELTIsoApp s s 0 1 ((shiftFunctor D n).obj V)).hom ≫
        (s.truncGELT 0 1).map ((Q.commShiftIso n).hom.app V)) =
    ((Q.eTruncGELTIsoApp s s 0 1 ((shiftFunctor D n).obj U)).hom ≫
      (s.truncGELT 0 1).map ((Q.commShiftIso n).hom.app U)) ≫
        (s.truncGELT 0 1).map ((shiftFunctor D n).map (Q.map f))
  have h := Q.eTruncGELTIsoApp_hom_naturality_obj s s 0 1
    ((shiftFunctor D n).map f)
  erw [← Category.assoc, h, Category.assoc]
  change (Q.eTruncGELTIsoApp s s 0 1 ((shiftFunctor D n).obj U)).hom ≫
      (s.truncGELT 0 1).map (Q.map ((shiftFunctor D n).map f)) ≫
        (s.truncGELT 0 1).map ((Q.commShiftIso n).hom.app V) = _
  erw [← (s.truncGELT 0 1).map_comp, (Q.commShiftIso n).hom.naturality,
    (s.truncGELT 0 1).map_comp, Category.assoc]
  simp only [Functor.eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, Category.assoc]

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
private theorem map_shiftAdd_inv (Q : D ⥤ D) [Q.CommShift ℤ]
    (V : D) (a n c : ℤ) (h : a + n = c) :
    Q.map ((shiftFunctorAdd' D a n c h).inv.app V) ≫
        (Q.commShiftIso c).hom.app V =
      (Q.commShiftIso n).hom.app ((shiftFunctor D a).obj V) ≫
        (shiftFunctor D n).map ((Q.commShiftIso a).hom.app V) ≫
        (shiftFunctorAdd' D a n c h).inv.app (Q.obj V) := by
  rw [Q.commShiftIso_add' h]
  simp only [Functor.CommShift.isoAdd'_hom_app]
  rw [← Q.map_comp_assoc, Iso.inv_hom_id_app, Q.map_id, Category.id_comp]

private theorem heartComparison_shift (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s]
    (V : D) (a n c : ℤ) (h : a + n = c) :
    (finiteTruncationHeartAction s Q).map
        (s.homology₀.map ((shiftFunctorAdd' D a n c h).inv.app V)) ≫
        (finiteTruncationHeartComparison s Q V c).hom =
      (finiteTruncationHeartComparison s Q ((shiftFunctor D a).obj V) n).hom ≫
        (shiftFunctor D n ⋙ s.homology₀).map ((Q.commShiftIso a).hom.app V) ≫
        s.homology₀.map ((shiftFunctorAdd' D a n c h).inv.app (Q.obj V)) := by
  apply s.heart.ι.map_injective
  simp only [Functor.map_comp]
  change Q.map ((s.truncGELT 0 1).map ((shiftFunctorAdd' D a n c h).inv.app V)) ≫
      ((Q.eTruncGELTIsoApp s s 0 1 ((shiftFunctor D c).obj V)).hom ≫
        (s.truncGELT 0 1).map ((Q.commShiftIso c).hom.app V)) =
    ((Q.eTruncGELTIsoApp s s 0 1
        ((shiftFunctor D n).obj ((shiftFunctor D a).obj V))).hom ≫
      (s.truncGELT 0 1).map ((Q.commShiftIso n).hom.app ((shiftFunctor D a).obj V))) ≫
        ((s.truncGELT 0 1).map ((shiftFunctor D n).map
          ((Q.commShiftIso a).hom.app V)) ≫
      (s.truncGELT 0 1).map ((shiftFunctorAdd' D a n c h).inv.app (Q.obj V)))
  have hh := Q.eTruncGELTIsoApp_hom_naturality_obj s s 0 1
    ((shiftFunctorAdd' D a n c h).inv.app V)
  calc
    _ = (Q.eTruncGELTIsoApp s s 0 1
        ((shiftFunctor D n).obj ((shiftFunctor D a).obj V))).hom ≫
        (s.truncGELT 0 1).map (Q.map ((shiftFunctorAdd' D a n c h).inv.app V)) ≫
        (s.truncGELT 0 1).map ((Q.commShiftIso c).hom.app V) := by
      erw [← Category.assoc, hh, Category.assoc]
      try rfl
    _ = _ := by
      erw [← (s.truncGELT 0 1).map_comp, map_shiftAdd_inv,
        (s.truncGELT 0 1).map_comp, (s.truncGELT 0 1).map_comp, Category.assoc]
      simp only [Functor.eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom,
        Functor.comp_map, Category.assoc]

private theorem heartComparison_connecting (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s]
    {U V : D} (δ : U ⟶ (shiftFunctor D (1 : ℤ)).obj V)
    (n n' : ℤ) (h : 1 + n = n') :
    (finiteTruncationHeartAction s Q).map
        ((shiftFunctor D n ⋙ s.homology₀).map δ ≫
          s.homology₀.map ((shiftFunctorAdd' D 1 n n' h).inv.app V)) ≫
        (finiteTruncationHeartComparison s Q V n').hom =
      (finiteTruncationHeartComparison s Q U n).hom ≫
        (shiftFunctor D n ⋙ s.homology₀).map
          (Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app V) ≫
        s.homology₀.map ((shiftFunctorAdd' D 1 n n' h).inv.app (Q.obj V)) := by
  rw [Functor.map_comp, Category.assoc, heartComparison_shift,
    ← Category.assoc, heartComparison_natural]
  simp only [Functor.map_comp, Category.assoc]

private theorem heartComparison_square (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s]
    {U V : D} (f : U ⟶ V) (u : Q.obj U ⟶ U) (v : Q.obj V ⟶ V)
    (h : Q.map f ≫ v = u ≫ f) (n : ℤ) :
    (finiteTruncationHeartAction s Q).map ((shiftFunctor D n ⋙ s.homology₀).map f) ≫
        ((finiteTruncationHeartComparison s Q V n).hom ≫
          (shiftFunctor D n ⋙ s.homology₀).map v) =
      ((finiteTruncationHeartComparison s Q U n).hom ≫
        (shiftFunctor D n ⋙ s.homology₀).map u) ≫
          (shiftFunctor D n ⋙ s.homology₀).map f := by
  erw [← Category.assoc, heartComparison_natural, Category.assoc,
    ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 800000 in
-- The shift and t-exact comparison isomorphisms require several coherence rewrites.
private theorem heartComparison_triangle_delta (s : TStructure D) (Q : D ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.IsTExact s s]
    (U : Triangle D) (ψ : Q.mapTriangle.obj U ⟶ U)
    (n n' : ℤ) (h : n + 1 = n') :
    (finiteTruncationHeartAction s Q).map
        ((shiftFunctor D n ⋙ s.homology₀).map U.mor₃ ≫
          s.homology₀.map ((shiftFunctorAdd' D 1 n n' (by omega)).inv.app U.obj₁)) ≫
        (finiteTruncationHeartComparison s Q U.obj₁ n').hom ≫
          (shiftFunctor D n' ⋙ s.homology₀).map ψ.hom₁ =
      ((finiteTruncationHeartComparison s Q U.obj₃ n).hom ≫
        (shiftFunctor D n ⋙ s.homology₀).map ψ.hom₃) ≫
      ((shiftFunctor D n ⋙ s.homology₀).map U.mor₃ ≫
        s.homology₀.map ((shiftFunctorAdd' D 1 n n' (by omega)).inv.app U.obj₁)) := by
  have hn := (shiftFunctorAdd' D 1 n n' (by omega)).inv.naturality ψ.hom₁
  dsimp only [Functor.comp_map] at hn
  have hδ : (Q.map U.mor₃ ≫ (Q.commShiftIso (1 : ℤ)).hom.app U.obj₁) ≫
      (shiftFunctor D (1 : ℤ)).map ψ.hom₁ = ψ.hom₃ ≫ U.mor₃ := ψ.comm₃
  have hx : (shiftFunctor D n ⋙ s.homology₀).map
        (Q.map U.mor₃ ≫ (Q.commShiftIso (1 : ℤ)).hom.app U.obj₁) ≫
        s.homology₀.map ((shiftFunctorAdd' D 1 n n' (by omega)).inv.app (Q.obj U.obj₁)) ≫
        (shiftFunctor D n' ⋙ s.homology₀).map ψ.hom₁ =
      (shiftFunctor D n ⋙ s.homology₀).map ψ.hom₃ ≫
        (shiftFunctor D n ⋙ s.homology₀).map U.mor₃ ≫
        s.homology₀.map ((shiftFunctorAdd' D 1 n n' (by omega)).inv.app U.obj₁) := by
    simp only [Functor.comp_map, ← s.homology₀.map_comp]
    erw [← hn, ← Category.assoc, ← (shiftFunctor D n).map_comp, hδ]
    simp only [Functor.map_comp, Category.assoc]
  erw [← Category.assoc, heartComparison_connecting, Category.assoc,
    Category.assoc, hx, ← Category.assoc]

private theorem truncationComparison_delta (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t]
    (K : C) (b c : ℤ) :
    P.map ((t.truncGELTδLT b c).app K) ≫
        (P.commShiftIso (1 : ℤ)).hom.app ((t.truncLT b).obj K) ≫
        (shiftFunctor C (1 : ℤ)).map ((P.eTruncLTIso t t b).hom.app K) =
      (P.eTruncGELTIsoApp t t b c K).hom ≫
        (t.truncGELTδLT b c).app (P.obj K) := by
  have hn := (P.eTruncLTIso t t b).hom.naturality ((t.truncLTι c).app K)
  dsimp only [Functor.comp_map] at hn
  have hd := P.eTruncGEδLT_comm t t b ((t.truncLT c).obj K)
  have hd' := (t.truncGEδLT b).naturality ((P.eTruncLTIso t t c).hom.app K)
  dsimp only [Functor.comp_map] at hd'
  dsimp only [TStructure.truncGELTδLT, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [P.map_comp, Category.assoc]
  erw [P.commShiftIso_hom_naturality_assoc, ← (shiftFunctor C (1 : ℤ)).map_comp,
    hn, Functor.map_comp]
  try simp only [Category.assoc]
  erw [reassoc_of% hd]
  have hp := P.eTruncLTIsoApp_hom_eTruncLTι_app t t c K
  change (P.eTruncGEIso t t b).hom.app ((t.truncLT c).obj K) ≫
      (t.truncGEδLT b).app (P.obj ((t.truncLT c).obj K)) ≫
      (shiftFunctor C (1 : ℤ)).map ((t.truncLT b).map (P.map ((t.truncLTι c).app K))) =
    ((P.eTruncGEIso t t b).hom.app ((t.truncLT c).obj K) ≫
      (t.truncGE b).map ((P.eTruncLTIso t t c).hom.app K)) ≫
      (t.truncGEδLT b).app ((t.truncLT c).obj (P.obj K)) ≫
      (shiftFunctor C (1 : ℤ)).map ((t.truncLT b).map ((t.truncLTι c).app (P.obj K)))
  erw [← hp, (t.truncLT b).map_comp, (shiftFunctor C (1 : ℤ)).map_comp,
    Category.assoc, Category.assoc, ← reassoc_of% hd']
  simp only [Functor.eTruncGEIso_hom_app, Functor.eTruncGEIsoApp,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  try rfl

private def truncationComparison_triangle (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t]
    (K : C) (b c : ℤ) (h : b ≤ c) :
    P.mapTriangle.obj ((t.triangleLTLTGELT b c h).obj K) ⟶
      (t.triangleLTLTGELT b c h).obj (P.obj K) where
  hom₁ := (P.eTruncLTIso t t b).hom.app K
  hom₂ := (P.eTruncLTIso t t c).hom.app K
  hom₃ := (P.eTruncGELTIsoApp t t b c K).hom
  comm₁ := by
    change P.map ((t.natTransTruncLTOfLE b c h).app K) ≫
        (P.eTruncLTIso t t c).hom.app K =
      (P.eTruncLTIso t t b).hom.app K ≫
        (t.natTransTruncLTOfLE b c h).app (P.obj K)
    have : t.IsLE (P.obj ((t.truncLT b).obj K)) (b - 1) :=
      Functor.IsTExact.isLE_obj t t P _ _
    have := t.isLE_of_le (P.obj ((t.truncLT b).obj K)) (b - 1) (c - 1) (by omega)
    apply t.to_truncLT_obj_ext
    erw [Category.assoc, P.eTruncLTIsoApp_hom_eTruncLTι_app t t c K,
      ← P.map_comp, t.natTransTruncLTOfLE_ι_app, Category.assoc,
      t.natTransTruncLTOfLE_ι_app, P.eTruncLTIsoApp_hom_eTruncLTι_app t t b K]
    try rfl
  comm₂ := by
    change P.map ((t.truncGEπ b).app ((t.truncLT c).obj K)) ≫
        (P.eTruncGELTIsoApp t t b c K).hom =
      (P.eTruncLTIso t t c).hom.app K ≫
        (t.truncGEπ b).app ((t.truncLT c).obj (P.obj K))
    dsimp only [Functor.eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom]
    erw [← Category.assoc, P.eTruncGEπ_app_eTruncGEIsoApp_hom t t b ((t.truncLT c).obj K)]
    exact ((t.truncGEπ b).naturality ((P.eTruncLTIso t t c).hom.app K)).symm
  comm₃ := by
    change (P.map ((t.truncGELTδLT b c).app K) ≫
        (P.commShiftIso (1 : ℤ)).hom.app ((t.truncLT b).obj K)) ≫ _ = _
    exact (Category.assoc _ _ _).trans (truncationComparison_delta t P K b c)

private def equivariant_triangle (t : TStructure C) (T : C ⥤ D)
    [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) (b : ℤ) :
    Q.functor.mapTriangle.obj
        (T.mapTriangle.obj ((t.triangleLTLTGELT b (b + 1) (by omega)).obj K)) ⟶
      T.mapTriangle.obj ((t.triangleLTLTGELT b (b + 1) (by omega)).obj K) :=
  ((Functor.mapTriangleCompIso T Q.functor).app _).inv ≫
    ((Functor.mapTriangleIso β).app _).hom ≫
    ((Functor.mapTriangleCompIso P.functor T).app _).hom ≫
    T.mapTriangle.map (truncationComparison_triangle t P.functor K b (b + 1) (by omega)) ≫
    T.mapTriangle.map ((t.triangleLTLTGELT b (b + 1) (by omega)).map θ.hom)

private def upperEquivariantIso (t : TStructure C) (T : C ⥤ D)
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) (K : C) (θ : P.functor.obj K ≅ K) (b : ℤ) :
    Q.functor.obj (T.obj ((t.truncLT b).obj K)) ≅ T.obj ((t.truncLT b).obj K) :=
  β.app ((t.truncLT b).obj K) ≪≫
    T.mapIso ((P.functor.eTruncLTIso t t b).app K) ≪≫
    T.mapIso ((t.truncLT b).mapIso θ)

omit [IsTriangulated D] in
private theorem equivariant_triangle_components (t : TStructure C) (T : C ⥤ D)
    [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) (b : ℤ) :
    (equivariant_triangle t T P Q β K θ b).hom₁ =
        (upperEquivariantIso t T P Q β K θ b).hom ∧
      (equivariant_triangle t T P Q β K θ b).hom₂ =
        (upperEquivariantIso t T P Q β K θ (b + 1)).hom ∧
      (equivariant_triangle t T P Q β K θ b).hom₃ =
        (finiteTruncationLayerIso t T P Q β K θ b).hom := by
  dsimp [equivariant_triangle, upperEquivariantIso, finiteTruncationLayerIso,
    Functor.mapTriangleCompIso, Functor.mapTriangleIso, Functor.mapTriangle,
    truncationComparison_triangle, Triangle.isoMk, NatIso.ofComponents,
    TriangleMorphism.comp, triangleMorphismId, Triangle.homMk, Triangle.mk,
    TStructure.triangleLTLTGELT, Triangle.functorMk]
  constructor
  · try simp only [Category.id_comp]
    try rfl
  constructor
  · try simp only [Category.id_comp]
    try rfl
  · try simp only [Category.id_comp]
    try rfl

omit [Preadditive D] [HasShift D ℤ] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
private theorem upperEquivariant_counit (t : TStructure C) (T : C ⥤ D)
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) (K : C) (θ : P.functor.obj K ≅ K) (b : ℤ) :
    (upperEquivariantIso t T P Q β K θ b).hom ≫ T.map ((t.truncLTι b).app K) =
      Q.functor.map (T.map ((t.truncLTι b).app K)) ≫
        (β.app K).hom ≫ T.map θ.hom := by
  have hp := P.functor.eTruncLTIsoApp_hom_eTruncLTι_app t t b K
  have hn := (t.truncLTι b).naturality θ.hom
  dsimp only [Functor.id_map] at hn
  have hβ := β.hom.naturality ((t.truncLTι b).app K)
  dsimp only [Functor.comp_map] at hβ
  change ((β.app ((t.truncLT b).obj K)).hom ≫
      T.map ((P.functor.eTruncLTIso t t b).hom.app K) ≫
      T.map ((t.truncLT b).map θ.hom)) ≫ T.map ((t.truncLTι b).app K) = _
  calc
    _ = (β.app ((t.truncLT b).obj K)).hom ≫
        T.map ((P.functor.eTruncLTIso t t b).hom.app K) ≫
        T.map ((t.truncLT b).map θ.hom ≫ (t.truncLTι b).app K) := by
      erw [T.map_comp, Category.assoc, Category.assoc]
      simp only [
        Iso.symm_hom, asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
      try rfl
    _ = (β.app ((t.truncLT b).obj K)).hom ≫
        T.map ((P.functor.eTruncLTIso t t b).hom.app K ≫
          (t.truncLTι b).app (P.functor.obj K)) ≫ T.map θ.hom := by
      erw [hn, T.map_comp, T.map_comp, Category.assoc]
      simp only [Functor.eTruncLTIso_hom_app, Functor.eTruncLTIsoApp,
        Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
      try rfl
    _ = _ := by
      erw [hp, ← Category.assoc, ← hβ, Category.assoc]
      try rfl

private def rawAlpha (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    (K : C) (a b : ℤ) :
    (finiteTruncationD t s T a b).obj K ⟶
      (finiteTruncationD t s T (a - 1) (b + 1)).obj K :=
  (shiftFunctor D (a + b) ⋙ s.homology₀).map
    (T.map ((t.natTransTruncLTOfLE (b + 1) (b + 1 + 1) (by omega)).app K)) ≫
      eqToHom (by
        simp only [finiteTruncationD, Functor.comp_obj]
        congr 3; omega)

private def rawG (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    (K : C) (a b : ℤ) :
    (finiteTruncationD t s T a b).obj K ⟶ (finiteTruncationE t s T a b).obj K :=
  (shiftFunctor D (a + b) ⋙ s.homology₀).map
    (T.map ((t.truncGEπ b).app ((t.truncLT (b + 1)).obj K)))

private def equivariantDMap (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) (K : C) (θ : P.functor.obj K ≅ K)
    (n b : ℤ) :
    (finiteTruncationHeartAction s Q.functor).obj
        ((shiftFunctor D n ⋙ s.homology₀).obj (T.obj ((t.truncLT b).obj K))) ⟶
      (shiftFunctor D n ⋙ s.homology₀).obj (T.obj ((t.truncLT b).obj K)) :=
  (finiteTruncationHeartComparison s Q.functor (T.obj ((t.truncLT b).obj K)) n).hom ≫
    (shiftFunctor D n ⋙ s.homology₀).map (upperEquivariantIso t T P Q β K θ b).hom

private def equivariantEMap (t : TStructure C) (s : TStructure D) (T : C ⥤ D)
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) (K : C) (θ : P.functor.obj K ≅ K)
    (n b : ℤ) :
    (finiteTruncationHeartAction s Q.functor).obj
        ((shiftFunctor D n ⋙ s.homology₀).obj (T.obj ((t.truncGELT b (b + 1)).obj K))) ⟶
      (shiftFunctor D n ⋙ s.homology₀).obj (T.obj ((t.truncGELT b (b + 1)).obj K)) :=
  (finiteTruncationHeartComparison s Q.functor
    (T.obj ((t.truncGELT b (b + 1)).obj K)) n).hom ≫
    (shiftFunctor D n ⋙ s.homology₀).map (finiteTruncationLayerIso t T P Q β K θ b).hom

private theorem equivariant_alpha (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) (a b : ℤ) :
    (finiteTruncationHeartAction s Q.functor).map (rawAlpha t s T K a b) ≫
        equivariantDMap t s T P Q β K θ (a - 1 + (b + 1)) (b + 1 + 1) =
      equivariantDMap t s T P Q β K θ (a + b) (b + 1) ≫ rawAlpha t s T K a b := by
  have hc := (equivariant_triangle t T P Q β K θ (b + 1)).comm₁
  have he := equivariant_triangle_components t T P Q β K θ (b + 1)
  rw [he.1, he.2.1] at hc
  have hh := heartComparison_square s Q.functor _ _ _ hc (a + b)
  dsimp only [rawAlpha]
  rw [Functor.map_comp, Category.assoc, eqToHom_map]
  erw [← eqToHom_naturality (fun nb : ℤ × ℤ ↦
    equivariantDMap t s T P Q β K θ nb.1 nb.2)
    (show (a + b, b + 1 + 1) = (a - 1 + (b + 1), b + 1 + 1) by ext <;> omega)]
  erw [← Category.assoc, hh, Category.assoc]
  try rfl

private theorem equivariant_g (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) (a b : ℤ) :
    (finiteTruncationHeartAction s Q.functor).map (rawG t s T K a b) ≫
        equivariantEMap t s T P Q β K θ (a + b) b =
      equivariantDMap t s T P Q β K θ (a + b) (b + 1) ≫ rawG t s T K a b := by
  have hc := (equivariant_triangle t T P Q β K θ b).comm₂
  have he := equivariant_triangle_components t T P Q β K θ b
  rw [he.2.1, he.2.2] at hc
  exact heartComparison_square s Q.functor _ _ _ hc (a + b)

private theorem equivariant_f (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) (a b : ℤ) :
    (finiteTruncationHeartAction s Q.functor).map
        (finiteTruncationConnecting t s T K a b) ≫
        equivariantDMap t s T P Q β K θ ((a + 2) + (b - 1)) (b - 1 + 1) =
      equivariantEMap t s T P Q β K θ (a + b) b ≫
        finiteTruncationConnecting t s T K a b := by
  have hh := heartComparison_triangle_delta s Q.functor
    (T.mapTriangle.obj ((t.triangleLTLTGELT b (b + 1) (by omega)).obj K))
    (equivariant_triangle t T P Q β K θ b) (a + b) ((a + 2) + (b - 1)) (by omega)
  have he := equivariant_triangle_components t T P Q β K θ b
  rw [he.1, he.2.2] at hh
  dsimp only [finiteTruncationConnecting]
  erw [Functor.map_comp, Category.assoc, eqToHom_map,
    ← eqToHom_naturality (fun c : ℤ ↦
      equivariantDMap t s T P Q β K θ ((a + 2) + (b - 1)) c)
      (show b = b - 1 + 1 by omega), ← Category.assoc]
  dsimp only [Functor.mapTriangle, TStructure.triangleLTLTGELT,
    Triangle.functorMk, Triangle.mk] at hh
  simpa only [equivariantDMap, equivariantEMap, Functor.comp_map, Functor.map_comp,
    Category.assoc, finiteTruncationHeartAction] using congrArg (fun f ↦ f ≫ eqToHom
      (congrArg (fun c : ℤ ↦ (shiftFunctor D ((a + 2) + (b - 1)) ⋙ s.homology₀).obj
        (T.obj ((t.truncLT c).obj K))) (show b = b - 1 + 1 by omega))) hh

private theorem exactTransport
    {B : Type*} [Category B] [Abelian B]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (w : a ≫ b = 0) (h : (ShortComplex.mk a b w).Exact)
    {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (h₁ : e₁.hom ≫ a' = a ≫ e₂.hom)
    (h₂ : e₂.hom ≫ b' = b ≫ e₃.hom) :
    ∃ w' : a' ≫ b' = 0, (ShortComplex.mk _ _ w').Exact := by
  have w' : a' ≫ b' = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, h₁, Category.assoc, h₂,
      ← Category.assoc, w, zero_comp, comp_zero]
  exact ⟨w', ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂) h⟩

private theorem raw_exact_f (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) (a b : ℤ) :
    imageSubobject (rawG t s T K a b) =
      kernelSubobject (finiteTruncationConnecting t s T K a b) := by
  let seq := Functor.ShiftSequence.tautological s.homology₀ ℤ
  let U := T.mapTriangle.obj ((t.triangleLTLTGELT b (b + 1) (by omega)).obj K)
  have hU := T.map_distinguished _
    (t.triangleLTLTGELT_distinguished b (b + 1) (by omega) K)
  have h := s.homology₀.homologySequence_exact₃ U hU (a + b)
    ((a + 2) + (b - 1)) (by omega)
  have he := (ShortComplex.exact_iff_image_eq_kernel _).mp h
  change imageSubobject ((shiftFunctor D (a + b) ⋙ s.homology₀).map U.mor₂) =
    kernelSubobject ((shiftFunctor D (a + b) ⋙ s.homology₀).map U.mor₃ ≫
      (s.homology₀.shiftIso 1 (a + b) ((a + 2) + (b - 1)) (by omega)).hom.app
        U.obj₁) at he
  rw [kernelSubobject_comp_mono] at he
  change imageSubobject (rawG t s T K a b) =
    kernelSubobject ((shiftFunctor D (a + b) ⋙ s.homology₀).map
      (T.map ((t.truncGELTδLT b (b + 1)).app K) ≫
        (T.commShiftIso (1 : ℤ)).hom.app ((t.truncLT b).obj K))) at he
  simpa only [finiteTruncationConnecting, Functor.map_comp, Functor.comp_map,
    kernelSubobject_comp_mono] using he

private theorem raw_exact_g (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) (a b : ℤ) :
    imageSubobject (rawAlpha t s T K a b) =
      kernelSubobject (rawG t s T K (a - 1) (b + 1)) := by
  let seq := Functor.ShiftSequence.tautological s.homology₀ ℤ
  let U := T.mapTriangle.obj
    ((t.triangleLTLTGELT (b + 1) (b + 1 + 1) (by omega)).obj K)
  have hU := T.map_distinguished _
    (t.triangleLTLTGELT_distinguished (b + 1) (b + 1 + 1) (by omega) K)
  have h := s.homology₀.homologySequence_exact₂ U hU (a + b)
  have w := s.homology₀.homologySequence_comp U hU (a + b)
  obtain ⟨w', h'⟩ := exactTransport _ _ w h
    (a' := rawAlpha t s T K a b) (b' := rawG t s T K (a - 1) (b + 1))
    (Iso.refl _) (eqToIso (congrArg
      (fun n : ℤ ↦ (shiftFunctor D n ⋙ s.homology₀).obj U.obj₂)
      (show a + b = a - 1 + (b + 1) by omega)))
    (eqToIso (congrArg
      (fun n : ℤ ↦ (shiftFunctor D n ⋙ s.homology₀).obj U.obj₃)
      (show a + b = a - 1 + (b + 1) by omega)))
    (by simp only [Iso.refl_hom, Category.id_comp]; rfl) (by
      dsimp only [eqToIso.hom, rawG]
      exact (eqToHom_naturality
        (fun n : ℤ ↦ (shiftFunctor D n ⋙ s.homology₀).map U.mor₂)
        (show a + b = a - 1 + (b + 1) by omega)).symm)
  exact (ShortComplex.exact_iff_image_eq_kernel _).mp h'

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] in
private theorem taut_shiftIso_hom {B : Type uB} [Category.{vB} B]
    (F : D ⥤ B) (n n' : ℤ) (h : 1 + n = n') (X : D) :
    letI := Functor.ShiftSequence.tautological F ℤ
    (F.shiftIso 1 n n' h).hom.app X =
      F.map ((shiftFunctorAdd' D 1 n n' h).inv.app X) := by
  dsimp [Functor.shiftIso, Functor.ShiftSequence.tautological]
  exact Category.id_comp _

omit [IsTriangulated C] in
private theorem connecting_eq (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] (K : C) (a b : ℤ) :
    finiteTruncationConnecting t s T K a b =
      ((shiftFunctor D (a + b) ⋙ s.homology₀).map
        (T.map ((t.truncGELTδLT b (b + 1)).app K) ≫
          (T.commShiftIso (1 : ℤ)).hom.app ((t.truncLT b).obj K)) ≫
        s.homology₀.map ((shiftFunctorAdd' D 1 (a + b) ((a + 2) + (b - 1))
          (by omega)).inv.app (T.obj ((t.truncLT b).obj K)))) ≫
      (eqToHom (congrArg (fun c : ℤ ↦
        (shiftFunctor D ((a + 2) + (b - 1)) ⋙ s.homology₀).obj
          (T.obj ((t.truncLT c).obj K))) (show b = b - 1 + 1 by omega)) :
        (shiftFunctor D ((a + 2) + (b - 1)) ⋙ s.homology₀).obj
          (T.obj ((t.truncLT b).obj K)) ⟶
        (shiftFunctor D ((a + 2) + (b - 1)) ⋙ s.homology₀).obj
          (T.obj ((t.truncLT (b - 1 + 1)).obj K))) := by
  dsimp only [finiteTruncationConnecting]
  erw [s.homology₀.map_comp]
  rfl

set_option maxHeartbeats 500000 in
-- Transporting the long exact sequence checks both degree and truncation-index casts.
private theorem raw_exact_alpha (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) (a b : ℤ) :
    imageSubobject (finiteTruncationConnecting t s T K a b) =
      kernelSubobject (rawAlpha t s T K (a + 2) (b - 1)) := by
  let seq := Functor.ShiftSequence.tautological s.homology₀ ℤ
  let U := T.mapTriangle.obj ((t.triangleLTLTGELT b (b + 1) (by omega)).obj K)
  have hU := T.map_distinguished _
    (t.triangleLTLTGELT_distinguished b (b + 1) (by omega) K)
  have h := s.homology₀.homologySequence_exact₁ U hU (a + b)
    ((a + 2) + (b - 1)) (by omega)
  have hi := taut_shiftIso_hom s.homology₀ (a + b) ((a + 2) + (b - 1))
    (by omega) U.obj₁
  let e₁ : (s.homology₀.shift (a + b)).obj U.obj₃ ≅
      (finiteTruncationE t s T a b).obj K := Iso.refl _
  let e₂ : (s.homology₀.shift ((a + 2) + (b - 1))).obj U.obj₁ ≅
      (finiteTruncationD t s T (a + 2) (b - 1)).obj K :=
    eqToIso (congrArg (fun c : ℤ ↦
      (shiftFunctor D ((a + 2) + (b - 1)) ⋙ s.homology₀).obj
        (T.obj ((t.truncLT c).obj K))) (show b = b - 1 + 1 by omega))
  let e₃ : (s.homology₀.shift ((a + 2) + (b - 1))).obj U.obj₂ ≅
      (finiteTruncationD t s T (a + 2 - 1) (b - 1 + 1)).obj K :=
    eqToIso (congrArg₂ (fun (m c : ℤ) ↦
      (shiftFunctor D m ⋙ s.homology₀).obj (T.obj ((t.truncLT c).obj K)))
        (show (a + 2) + (b - 1) = (a + 2 - 1) + (b - 1 + 1) by omega)
        (show b + 1 = b - 1 + 1 + 1 by omega))
  have w₀ := s.homology₀.homologySequenceδ_comp U hU (a + b)
    ((a + 2) + (b - 1)) (by omega)
  obtain ⟨w', h'⟩ := exactTransport _ _ w₀ h
    (a' := finiteTruncationConnecting t s T K a b)
    (b' := rawAlpha t s T K (a + 2) (b - 1)) e₁ e₂ e₃
    (by
      dsimp only [e₁, Iso.refl_hom]
      rw [Category.id_comp, connecting_eq]
      dsimp only [Functor.homologySequenceδ, Functor.shiftMap]
      rw [hi]
      rfl)
    (by
      dsimp only [e₂, e₃, eqToIso.hom, rawAlpha]
      have hn := eqToHom_naturality (fun nc : ℤ × ℤ ↦
        (shiftFunctor D nc.1 ⋙ s.homology₀).map
          (T.map ((t.natTransTruncLTOfLE nc.2 (nc.2 + 1) (by omega)).app K)))
        (show (((a + 2) + (b - 1)), b) =
          (((a + 2) + (b - 1)), b - 1 + 1) by ext <;> omega)
      erw [← Category.assoc, ← hn, Category.assoc, eqToHom_trans]
      rfl)
  exact (ShortComplex.exact_iff_image_eq_kernel _).mp h'

private theorem zero_of_exact {B : Type*} [Category B] [Abelian B]
    {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : imageSubobject f = kernelSubobject g) : f ≫ g = 0 := by
  apply (kernelSubobject_factors_iff g f).mp
  rw [← h]
  simpa only [Category.id_comp] using imageSubobject_factors_comp_self f (𝟙 _)

private theorem raw_exact_f_transport (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (K : C) (a b a' b' : ℤ) (ha : a = a') (hb : b = b') :
    imageSubobject (rawG t s T K a b ≫
      eqToHom (congrArg₂ (fun a b : ℤ ↦ (finiteTruncationE t s T a b).obj K) ha hb)) =
      kernelSubobject (finiteTruncationConnecting t s T K a' b') := by
  subst a'
  subst b'
  simpa only [eqToHom_refl, Category.comp_id] using raw_exact_f t s T K a b

private def rawCouple (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) :
    BigradedExactCouple s.heart.FullSubcategory 0 where
  D a b := (finiteTruncationD t s T a b).obj K
  E a b := (finiteTruncationE t s T a b).obj K
  alpha a b := rawAlpha t s T K a b
  f a b := finiteTruncationConnecting t s T K a b
  g a b := rawG t s T K a b ≫
    eqToHom (congrArg₂ (fun a b : ℤ ↦ (finiteTruncationE t s T a b).obj K)
      (by omega) (by omega))
  alpha_f_zero a b := zero_of_exact _ _ (raw_exact_alpha t s T K a b)
  f_g_zero a b := zero_of_exact _ _
    (raw_exact_f_transport t s T K a b _ _ (by omega) (by omega))
  g_alpha_zero a b := by
    rw [← Category.assoc, zero_of_exact _ _ (raw_exact_g t s T K a b), zero_comp]
  exact_alpha a b := raw_exact_alpha t s T K a b
  exact_f a b := raw_exact_f_transport t s T K a b _ _ (by omega) (by omega)
  exact_g a b := by
    rw [kernelSubobject_comp_mono]
    exact raw_exact_g t s T K a b

private def canonicalCouple (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) :
    FiniteTruncationCouple t s T K where
  X := rawCouple t s T K
  dIso _ _ := Iso.refl _
  eIso _ _ := Iso.refl _
  alpha_eq a b := by simp only [rawCouple, rawAlpha, Iso.refl_hom,
    Category.comp_id, Category.id_comp]
  g_eq a b := by
    simp [BigradedExactCouple.initialG, rawCouple, rawG, Category.assoc]
  f_eq a b := by simp only [rawCouple, Iso.refl_hom, Category.comp_id, Category.id_comp]

omit [IsTriangulated C] in
private theorem rawAlpha_natural (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) {K K' : C} (v : K ⟶ K') (a b : ℤ) :
    (finiteTruncationD t s T a b).map v ≫ rawAlpha t s T K' a b =
      rawAlpha t s T K a b ≫ (finiteTruncationD t s T (a - 1) (b + 1)).map v := by
  dsimp only [rawAlpha, finiteTruncationD, Functor.comp_map]
  erw [← Category.assoc, ← s.homology₀.map_comp, ← Functor.map_comp, ← T.map_comp,
    (t.natTransTruncLTOfLE (b + 1) (b + 1 + 1) (by omega)).naturality,
    T.map_comp, Functor.map_comp, s.homology₀.map_comp, Category.assoc]
  erw [eqToHom_naturality
    (fun n : ℤ ↦ (shiftFunctor D n ⋙ s.homology₀).map
      (T.map ((t.truncLT (b + 1 + 1)).map v)))
    (show a + b = a - 1 + (b + 1) by omega)]
  simp only [Functor.comp_map, Category.assoc]

omit [IsTriangulated C] in
private theorem rawG_natural (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) {K K' : C} (v : K ⟶ K') (a b : ℤ) :
    (finiteTruncationD t s T a b).map v ≫ rawG t s T K' a b =
      rawG t s T K a b ≫ (finiteTruncationE t s T a b).map v := by
  dsimp only [rawG, finiteTruncationD, finiteTruncationE, Functor.comp_map]
  simp only [← Functor.map_comp]
  congr 3
  exact (t.truncGEπ b).naturality ((t.truncLT (b + 1)).map v)

omit [IsTriangulated C] in
private theorem connecting_natural (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] {K K' : C} (v : K ⟶ K') (a b : ℤ) :
    (finiteTruncationE t s T a b).map v ≫
        finiteTruncationConnecting t s T K' a b =
      finiteTruncationConnecting t s T K a b ≫
        (finiteTruncationD t s T (a + 2) (b - 1)).map v := by
  dsimp only [finiteTruncationConnecting, finiteTruncationD,
    finiteTruncationE, Functor.comp_map]
  simp only [Category.assoc]
  erw [← eqToHom_naturality (fun c : ℤ ↦
    (shiftFunctor D ((a + 2) + (b - 1)) ⋙ s.homology₀).map
      (T.map ((t.truncLT c).map v))) (show b = b - 1 + 1 by omega)]
  simp only [← Category.assoc]
  congr 1
  have hd := (t.truncGELTδLT b (b + 1)).naturality v
  dsimp only [Functor.comp_map] at hd
  have hδ : T.map ((t.truncGELT b (b + 1)).map v) ≫
      (T.map ((t.truncGELTδLT b (b + 1)).app K') ≫
        (T.commShiftIso (1 : ℤ)).hom.app _) =
      (T.map ((t.truncGELTδLT b (b + 1)).app K) ≫
        (T.commShiftIso (1 : ℤ)).hom.app _) ≫
          (shiftFunctor D (1 : ℤ)).map (T.map ((t.truncLT b).map v)) := by
    erw [← Category.assoc, ← T.map_comp, hd, T.map_comp, Category.assoc,
      T.commShiftIso_hom_naturality]
    exact (Category.assoc _ _ _).symm
  have hn := (shiftFunctorAdd' D 1 (a + b) ((a + 2) + (b - 1))
    (by omega)).inv.naturality (T.map ((t.truncLT b).map v))
  dsimp only [Functor.comp_map] at hn
  dsimp only [Functor.comp_map]
  erw [← s.homology₀.map_comp, ← s.homology₀.map_comp]
  congr 1
  erw [Category.assoc, ← hn, ← Category.assoc,
    ← (shiftFunctor D (a + b)).map_comp, hδ,
    (shiftFunctor D (a + b)).map_comp, Category.assoc]

private def rawMorphism (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] {K K' : C} (v : K ⟶ K') :
    BigradedExactCouple.CoupleMorphism (rawCouple t s T K) (rawCouple t s T K') where
  tD a b := (finiteTruncationD t s T a b).map v
  tE a b := (finiteTruncationE t s T a b).map v
  alpha_comm a b := rawAlpha_natural t s T v a b
  f_comm a b := connecting_natural t s T v a b
  g_comm a b := by
    dsimp only [rawCouple]
    erw [← Category.assoc, rawG_natural, Category.assoc,
      eqToHom_naturality (fun pq : ℤ × ℤ ↦ (finiteTruncationE t s T pq.1 pq.2).map v)
        (show (a, b) = (a + (0 : ℕ), b - (0 : ℕ)) by ext <;> omega)]
    simp only [Category.assoc]

private theorem pageMap_exists (s : TStructure D)
    (X Y : BigradedExactCouple s.heart.FullSubcategory 0)
    (v : BigradedExactCouple.CoupleMorphism X Y) :
    ∃ M : FiniteTruncationPageMap s (𝟭 _) X Y,
      (∀ a b : ℤ, M.dMap 0 a b = v.tD a b) ∧
      (∀ a b : ℤ, M.eMap 0 a b = v.tE a b) := by
  classical
  obtain ⟨⟨P, hD, hE, hι, hk, hd⟩, _⟩ :=
    BigradedExactCouple.derivedCoupleFunctoriality X Y v
  choose k hkι hkπ using hk
  refine ⟨{ dMap := fun r a b ↦ (P r).tD a b
            eMap := fun r a b ↦ (P r).tE a b
            alpha_comm := fun r a b ↦ ((P r).alpha_comm a b).symm
            f_comm := fun r a b ↦ ((P r).f_comm a b).symm
            g_comm := fun r a b ↦ ((P r).g_comm a b).symm
            differential_comm := fun r a b ↦ (hd r a b).symm
            image_comm := fun r a b ↦ (hι r a b).symm
            cycles := k
            cycles_comm := fun r a b ↦ (hkι r a b).symm
            quotient_comm := hkπ }, hD, hE⟩

private theorem pageMap_ext (s : TStructure D)
    {X Y : BigradedExactCouple s.heart.FullSubcategory 0}
    (M N : FiniteTruncationPageMap s (𝟭 _) X Y)
    (hD : ∀ a b : ℤ, M.dMap 0 a b = N.dMap 0 a b)
    (hE : ∀ a b : ℤ, M.eMap 0 a b = N.eMap 0 a b) :
    ∀ (r : ℕ) (a b : ℤ), M.dMap r a b = N.dMap r a b ∧
      M.eMap r a b = N.eMap r a b := by
  have h (r : ℕ) : (∀ a b, M.dMap r a b = N.dMap r a b) ∧
      (∀ a b, M.eMap r a b = N.eMap r a b) := by
    induction r with
    | zero => exact ⟨hD, hE⟩
    | succ r ih =>
      have hc (a b : ℤ) : M.cycles r a b = N.cycles r a b := by
        apply (cancel_mono (kernel.ι ((Y.pageCouple r).d a b))).mp
        erw [← M.cycles_comm, ← N.cycles_comm, ih.2]
      constructor
      · intro a b
        apply (cancel_mono ((Y.pageCouple r).derivedDInclusion a b)).mp
        erw [← M.image_comm, ← N.image_comm, ih.1]
      · intro a b
        apply (cancel_epi ((X.pageCouple r).derivedEProjection a b)).mp
        erw [show _ from M.quotient_comm r a b,
          show _ from N.quotient_comm r a b, hc]
  exact fun r a b ↦ ⟨h r |>.1 a b, h r |>.2 a b⟩

private def pageId (s : TStructure D) (X : BigradedExactCouple s.heart.FullSubcategory 0) :
    FiniteTruncationPageMap s (𝟭 _) X X where
  dMap _ _ _ := 𝟙 _
  eMap _ _ _ := 𝟙 _
  cycles _ _ _ := 𝟙 _
  alpha_comm := by intros; simp
  f_comm := by intros; simp
  g_comm := by intros; simp
  differential_comm := by intros; simp
  image_comm := by intros; simp
  cycles_comm := by intros; simp
  quotient_comm := by
    intro r a b
    change (X.pageCouple r).derivedEProjection a b ≫
      𝟙 ((X.pageCouple r).derivedE a b) = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]

private def pageComp (s : TStructure D)
    {X Y Z : BigradedExactCouple s.heart.FullSubcategory 0}
    (M : FiniteTruncationPageMap s (𝟭 _) X Y)
    (N : FiniteTruncationPageMap s (𝟭 _) Y Z) :
    FiniteTruncationPageMap s (𝟭 _) X Z where
  dMap r a b := M.dMap r a b ≫ N.dMap r a b
  eMap r a b := M.eMap r a b ≫ N.eMap r a b
  cycles r a b := M.cycles r a b ≫ N.cycles r a b
  alpha_comm := by
    intro r a b
    have hm := M.alpha_comm r a b
    have hn := N.alpha_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]

  f_comm := by
    intro r a b
    have hm := M.f_comm r a b
    have hn := N.f_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]

  g_comm := by
    intro r a b
    have hm := M.g_comm r a b
    have hn := N.g_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]

  differential_comm := by
    intro r a b
    have hm := M.differential_comm r a b
    have hn := N.differential_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]

  image_comm := by
    intro r a b
    have hm := M.image_comm r a b
    have hn := N.image_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]

  cycles_comm := by
    intro r a b
    have hm := M.cycles_comm r a b
    have hn := N.cycles_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]

  quotient_comm := by
    intro r a b
    have hm := M.quotient_comm r a b
    have hn := N.quotient_comm r a b
    simp only [Functor.id_map] at hm hn
    simp only [Functor.id_map, Category.assoc]
    erw [← Category.assoc, hm, Category.assoc, hn]
private theorem canonicalPages (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] :
    ∃ M : ∀ {K K' : C}, (K ⟶ K') →
      FiniteTruncationPageMap s (𝟭 _) (canonicalCouple t s T K).X
        (canonicalCouple t s T K').X,
      (∀ {K K' : C} (v : K ⟶ K') (a b : ℤ),
        (M v).dMap 0 a b = (finiteTruncationD t s T a b).map v ∧
        (M v).eMap 0 a b = (finiteTruncationE t s T a b).map v) ∧
      (∀ (K : C) (r : ℕ) (a b : ℤ),
        (M (𝟙 K)).dMap r a b = 𝟙 _ ∧ (M (𝟙 K)).eMap r a b = 𝟙 _) ∧
      (∀ {K K' K'' : C} (v : K ⟶ K') (w : K' ⟶ K'') (r : ℕ) (a b : ℤ),
        (M (v ≫ w)).dMap r a b = (M v).dMap r a b ≫ (M w).dMap r a b ∧
        (M (v ≫ w)).eMap r a b = (M v).eMap r a b ≫ (M w).eMap r a b) := by
  classical
  have H (K K' : C) (v : K ⟶ K') :
      ∃ M : FiniteTruncationPageMap s (𝟭 _) (canonicalCouple t s T K).X
          (canonicalCouple t s T K').X,
        (∀ a b, M.dMap 0 a b = (finiteTruncationD t s T a b).map v) ∧
        (∀ a b, M.eMap 0 a b = (finiteTruncationE t s T a b).map v) :=
    pageMap_exists s _ _ (rawMorphism t s T v)
  choose M' hD' hE' using H
  let M {K K' : C} (v : K ⟶ K') := M' K K' v
  have hD {K K' : C} (v : K ⟶ K') := hD' K K' v
  have hE {K K' : C} (v : K ⟶ K') := hE' K K' v
  refine ⟨M, ?_, ?_, ?_⟩
  · intro K K' v a b
    exact ⟨hD v a b, hE v a b⟩
  · intro K r a b
    exact pageMap_ext s (M (𝟙 K)) (pageId s _) (by
      intro a b
      dsimp only [M, pageId]
      rw [hD', Functor.map_id]
      rfl) (by
      intro a b
      dsimp only [M, pageId]
      rw [hE', Functor.map_id]
      rfl) r a b
  · intro K K' K'' v w r a b
    exact pageMap_ext s (M (v ≫ w)) (pageComp s (M v) (M w)) (by
      intro a b
      dsimp only [M, pageComp]
      rw [hD', hD', hD', Functor.map_comp]) (by
      intro a b
      dsimp only [M, pageComp]
      rw [hE', hE', hE', Functor.map_comp]) r a b

private theorem exactPages (s : TStructure D)
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (Φ : s.heart.FullSubcategory ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (X : BigradedExactCouple s.heart.FullSubcategory 0) :
    ∃ (Y : BigradedExactCouple B 0)
      (hD : ∀ a b : ℤ, Φ.obj (X.D a b) = Y.D a b)
      (hE : ∀ a b : ℤ, Φ.obj (X.E a b) = Y.E a b)
      (M : FiniteTruncationPageMap s Φ X Y),
      (∀ a b : ℤ, M.dMap 0 a b = eqToHom (hD a b) ∧
        M.eMap 0 a b = eqToHom (hE a b)) ∧
      (∀ (r : ℕ) (a b : ℤ), IsIso (M.dMap r a b) ∧ IsIso (M.eMap r a b)) := by
  classical
  obtain ⟨Y, hD, hE, _, _, _, δ, φ, iX, iY, hzero, _, hsucc, hinc,
    ha, hf, hg, hd, hk, _⟩ := BigradedExactCouple.exactFunctor_couple Φ X
  choose k hki hkι hkπ using hk
  refine ⟨Y, hD, hE,
    { dMap := fun r a b ↦ (δ r a b).hom
      eMap := fun r a b ↦ (φ r a b).hom
      alpha_comm := ha
      f_comm := hf
      g_comm := hg
      differential_comm := hd
      image_comm := ?_
      cycles := k
      cycles_comm := fun r a b ↦ (hkι r a b).symm
      quotient_comm := hkπ }, ?_, fun _ _ _ ↦ ⟨inferInstance, inferInstance⟩⟩
  · intro r a b
    have := (hinc r a b).2.1
    apply (cancel_mono (iY r a b)).mp
    simp only [Category.assoc]
    erw [← (hsucc r a b).2, (hinc (r + 1) a b).2.2,
      (hinc r a b).2.2, ← Φ.map_comp_assoc, ← (hsucc r a b).1]
  · intro a b
    exact ⟨congrArg Iso.hom (hzero a b).1, congrArg Iso.hom (hzero a b).2⟩

private structure PageData {B : Type uB} [Category.{vB} B] [Abelian B]
    (X Y : BigradedExactCouple B 0) where
  d : ∀ r a b, (X.pageCouple r).D a b ⟶ (Y.pageCouple r).D a b
  e : ∀ r a b, (X.pageCouple r).E a b ⟶ (Y.pageCouple r).E a b
  k : ∀ r a b, kernel ((X.pageCouple r).d a b) ⟶ kernel ((Y.pageCouple r).d a b)
  image_comm : ∀ r a b, (X.pageCouple r).derivedDInclusion a b ≫ d r a b =
    d (r + 1) a b ≫ (Y.pageCouple r).derivedDInclusion a b
  kernel_comm : ∀ r a b, kernel.ι ((X.pageCouple r).d a b) ≫ e r a b =
    k r a b ≫ kernel.ι ((Y.pageCouple r).d a b)
  quotient_comm : ∀ r a b, (X.pageCouple r).derivedEProjection a b ≫ e (r + 1) a b =
    k r a b ≫ (Y.pageCouple r).derivedEProjection a b

private def PageData.id {B : Type uB} [Category.{vB} B] [Abelian B]
    (X : BigradedExactCouple B 0) : PageData X X where
  d _ _ _ := 𝟙 _
  e _ _ _ := 𝟙 _
  k _ _ _ := 𝟙 _
  image_comm := by intros; simp
  kernel_comm := by intros; simp
  quotient_comm := by
    intro r a b
    change (X.pageCouple r).derivedEProjection a b ≫
      𝟙 ((X.pageCouple r).derivedE a b) = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]

private def PageData.comp {B : Type uB} [Category.{vB} B] [Abelian B]
    {X Y Z : BigradedExactCouple B 0} (M : PageData X Y) (N : PageData Y Z) :
    PageData X Z where
  d r a b := M.d r a b ≫ N.d r a b
  e r a b := M.e r a b ≫ N.e r a b
  k r a b := M.k r a b ≫ N.k r a b
  image_comm := by
    intro r a b
    simp only [← Category.assoc]
    erw [M.image_comm, Category.assoc, N.image_comm, Category.assoc]
  kernel_comm := by
    intro r a b
    simp only [← Category.assoc]
    erw [M.kernel_comm, Category.assoc, N.kernel_comm, Category.assoc]
  quotient_comm := by
    intro r a b
    simp only [← Category.assoc]
    erw [M.quotient_comm, Category.assoc, N.quotient_comm, Category.assoc]

private theorem PageData.ext {B : Type uB} [Category.{vB} B] [Abelian B]
    {X Y : BigradedExactCouple B 0} (M N : PageData X Y)
    (hD : ∀ a b, M.d 0 a b = N.d 0 a b) (hE : ∀ a b, M.e 0 a b = N.e 0 a b) :
    ∀ r a b, M.d r a b = N.d r a b ∧ M.e r a b = N.e r a b := by
  have h (r : ℕ) : (∀ a b, M.d r a b = N.d r a b) ∧
      (∀ a b, M.e r a b = N.e r a b) := by
    induction r with
    | zero => exact ⟨hD, hE⟩
    | succ r ih =>
      have hk (a b : ℤ) : M.k r a b = N.k r a b := by
        apply (cancel_mono (kernel.ι ((Y.pageCouple r).d a b))).mp
        erw [← M.kernel_comm, ← N.kernel_comm, ih.2]
      constructor
      · intro a b
        apply (cancel_mono ((Y.pageCouple r).derivedDInclusion a b)).mp
        erw [← M.image_comm, ← N.image_comm, ih.1]
      · intro a b
        apply (cancel_epi ((X.pageCouple r).derivedEProjection a b)).mp
        erw [show _ from M.quotient_comm r a b,
          show _ from N.quotient_comm r a b, hk]
  exact fun r a b ↦ ⟨(h r).1 a b, (h r).2 a b⟩

private theorem inverse_square {B : Type uB} [Category.{vB} B]
    {W X Y Z : B} (a : W ⟶ X) (b : Y ⟶ Z) (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso f] [IsIso g] (h : f ≫ b = a ≫ g) : inv f ≫ a = b ≫ inv g := by
  apply (cancel_epi f).mp
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private def inverseCoupleMorphism {B : Type uB} [Category.{vB} B] [Abelian B]
    {X Y : BigradedExactCouple B 0} (v : BigradedExactCouple.CoupleMorphism X Y)
    (hD : ∀ a b, IsIso (v.tD a b)) (hE : ∀ a b, IsIso (v.tE a b)) :
    BigradedExactCouple.CoupleMorphism Y X where
  tD a b := @inv _ _ _ _ (v.tD a b) (hD a b)
  tE a b := @inv _ _ _ _ (v.tE a b) (hE a b)
  alpha_comm a b := by
    have := hD a b
    have := hD (a - 1) (b + 1)
    exact inverse_square _ _ _ _ (v.alpha_comm a b)
  f_comm a b := by
    have := hE a b
    have := hD (a + 2) (b - 1)
    exact inverse_square _ _ _ _ (v.f_comm a b)
  g_comm a b := by
    have := hD a b
    have := hE (a + (0 : ℕ)) (b - (0 : ℕ))
    exact inverse_square _ _ _ _ (v.g_comm a b)

private theorem couple_pages_isIso {B : Type uB} [Category.{vB} B] [Abelian B]
    {X Y : BigradedExactCouple B 0} (v : BigradedExactCouple.CoupleMorphism X Y)
    (hD : ∀ a b, IsIso (v.tD a b)) (hE : ∀ a b, IsIso (v.tE a b))
    (P : PageData X Y) (hP : ∀ a b, P.d 0 a b = v.tD a b ∧ P.e 0 a b = v.tE a b) :
    ∀ r a b, IsIso (P.d r a b) ∧ IsIso (P.e r a b) := by
  classical
  let vi := inverseCoupleMorphism v hD hE
  obtain ⟨⟨Q, hQD, hQE, hQi, hQk, _⟩, _⟩ :=
    BigradedExactCouple.derivedCoupleFunctoriality Y X vi
  choose k hki hkπ using hQk
  let R : PageData Y X :=
    { d := fun r a b ↦ (Q r).tD a b
      e := fun r a b ↦ (Q r).tE a b
      k := k
      image_comm := fun r a b ↦ (hQi r a b).symm
      kernel_comm := fun r a b ↦ (hki r a b).symm
      quotient_comm := hkπ }
  have hPR := PageData.ext (P.comp R) (PageData.id X) (by
    intro a b
    dsimp only [PageData.comp, PageData.id, R]
    rw [(hP a b).1, hQD]
    have := hD a b
    exact IsIso.hom_inv_id _) (by
    intro a b
    dsimp only [PageData.comp, PageData.id, R]
    rw [(hP a b).2, hQE]
    have := hE a b
    exact IsIso.hom_inv_id _)
  have hRP := PageData.ext (R.comp P) (PageData.id Y) (by
    intro a b
    dsimp only [PageData.comp, PageData.id, R]
    rw [hQD, (hP a b).1]
    have := hD a b
    exact IsIso.inv_hom_id _) (by
    intro a b
    dsimp only [PageData.comp, PageData.id, R]
    rw [hQE, (hP a b).2]
    have := hE a b
    exact IsIso.inv_hom_id _)
  intro r a b
  exact ⟨⟨⟨R.d r a b, (hPR r a b).1, (hRP r a b).1⟩⟩,
    ⟨⟨R.e r a b, (hPR r a b).2, (hRP r a b).2⟩⟩⟩

private theorem transport_square {B : Type uB} [Category.{vB} B]
    {U U' V V' W Z : B} (a : U ⟶ V) (b : U' ⟶ V')
    (f : U ⟶ U') (g : V ⟶ V') [IsIso f] [IsIso g]
    (c : U ⟶ W) (d : V ⟶ Z) (k : W ⟶ Z)
    (h : f ≫ b = a ≫ g) (hc : a ≫ d = c ≫ k) :
    (inv f ≫ c) ≫ k = b ≫ inv g ≫ d := by
  rw [Category.assoc, ← hc, ← Category.assoc, inverse_square a b f g h,
    Category.assoc]

private theorem pages_of_initial_iso (s : TStructure D)
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (Φ : s.heart.FullSubcategory ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (X : BigradedExactCouple s.heart.FullSubcategory 0)
    (Y : BigradedExactCouple B 0)
    (d : ∀ a b : ℤ, Φ.obj (X.D a b) ⟶ Y.D a b)
    (e : ∀ a b : ℤ, Φ.obj (X.E a b) ⟶ Y.E a b)
    (hD : ∀ a b, IsIso (d a b)) (hE : ∀ a b, IsIso (e a b))
    (ha : ∀ a b, Φ.map (X.alpha a b) ≫ d (a - 1) (b + 1) = d a b ≫ Y.alpha a b)
    (hf : ∀ a b, Φ.map (X.f a b) ≫ d (a + 2) (b - 1) = e a b ≫ Y.f a b)
    (hg : ∀ a b, Φ.map (X.g a b) ≫ e (a + (0 : ℕ)) (b - (0 : ℕ)) =
      d a b ≫ Y.g a b) :
    ∃ M : FiniteTruncationPageMap s Φ X Y,
      (∀ a b, M.dMap 0 a b = d a b ∧ M.eMap 0 a b = e a b) ∧
      (∀ r a b, IsIso (M.dMap r a b) ∧ IsIso (M.eMap r a b)) := by
  classical
  obtain ⟨Z, _, _, M, _, hM⟩ := exactPages s Φ X
  let v : BigradedExactCouple.CoupleMorphism Z Y :=
    { tD := fun a b ↦ @inv _ _ _ _ (M.dMap 0 a b) (hM 0 a b).1 ≫ d a b
      tE := fun a b ↦ @inv _ _ _ _ (M.eMap 0 a b) (hM 0 a b).2 ≫ e a b
      alpha_comm := fun a b ↦ by
        have := (hM 0 a b).1
        have := (hM 0 (a - 1) (b + 1)).1
        exact transport_square _ _ _ _ _ _ _ (M.alpha_comm 0 a b).symm (ha a b)
      f_comm := fun a b ↦ by
        have := (hM 0 a b).2
        have := (hM 0 (a + 2) (b - 1)).1
        exact transport_square _ _ _ _ _ _ _ (M.f_comm 0 a b).symm (hf a b)
      g_comm := fun a b ↦ by
        have := (hM 0 a b).1
        have := (hM 0 (a + (0 : ℕ)) (b - (0 : ℕ))).2
        exact transport_square _ _ _ _ _ _ _ (M.g_comm 0 a b).symm (hg a b) }
  obtain ⟨⟨P, hPD, hPE, hPi, hPk, hPd⟩, _⟩ :=
    BigradedExactCouple.derivedCoupleFunctoriality Z Y v
  choose k hki hkπ using hPk
  let R : PageData Z Y :=
    { d := fun r a b ↦ (P r).tD a b
      e := fun r a b ↦ (P r).tE a b
      k := k
      image_comm := fun r a b ↦ (hPi r a b).symm
      kernel_comm := fun r a b ↦ (hki r a b).symm
      quotient_comm := hkπ }
  have hR := couple_pages_isIso v (fun a b ↦ by
    have := (hM 0 a b).1
    have := hD a b
    dsimp only [v]
    infer_instance) (fun a b ↦ by
    have := (hM 0 a b).2
    have := hE a b
    dsimp only [v]
    infer_instance) R (fun a b ↦ ⟨hPD a b, hPE a b⟩)
  let N : FiniteTruncationPageMap s Φ X Y :=
    { dMap := fun r a b ↦ M.dMap r a b ≫ (P r).tD a b
      eMap := fun r a b ↦ M.eMap r a b ≫ (P r).tE a b
      cycles := fun r a b ↦ M.cycles r a b ≫ k r a b
      alpha_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.alpha_comm, Category.assoc, ← (P r).alpha_comm, Category.assoc]
      f_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.f_comm, Category.assoc, ← (P r).f_comm, Category.assoc]
      g_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.g_comm, Category.assoc, ← (P r).g_comm, Category.assoc]
      differential_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.differential_comm, Category.assoc, ← hPd, Category.assoc]
      image_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.image_comm, Category.assoc, ← hPi, Category.assoc]
      cycles_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.cycles_comm, Category.assoc, ← hki, Category.assoc]
      quotient_comm := fun r a b ↦ by
        simp only [← Category.assoc]
        erw [M.quotient_comm, Category.assoc, hkπ, Category.assoc] }
  refine ⟨N, ?_, ?_⟩
  · intro a b
    have := (hM 0 a b).1
    have := (hM 0 a b).2
    dsimp only [N]
    rw [hPD, hPE]
    simp only [v, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp, and_self]
  · intro r a b
    have := (hM r a b).1
    have := (hM r a b).2
    have := (hR r a b).1
    have := (hR r a b).2
    exact ⟨inferInstance, inferInstance⟩

private theorem cast_square {B : Type uB} [Category.{vB} B]
    {U V W Z W' Z' : B} (f : U ⟶ V) (g : W ⟶ Z) (d : U ⟶ W) (e : V ⟶ Z)
    (h : f ≫ e = d ≫ g) (hW : W = W') (hZ : Z = Z')
    (g' : W' ⟶ Z') (hg : g' = eqToHom hW.symm ≫ g ≫ eqToHom hZ) :
    f ≫ (e ≫ eqToHom hZ) = (d ≫ eqToHom hW) ≫ g' := by
  rw [hg]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc]

private theorem initialG_square {B : Type uB} [Category.{vB} B] [Abelian B]
    (s : TStructure D) (Φ : s.heart.FullSubcategory ⥤ B)
    (X : BigradedExactCouple s.heart.FullSubcategory 0) (Y : BigradedExactCouple B 0)
    (d : ∀ a b : ℤ, Φ.obj (X.D a b) ⟶ Y.D a b)
    (e : ∀ a b : ℤ, Φ.obj (X.E a b) ⟶ Y.E a b)
    (h : ∀ a b : ℤ, Φ.map (X.initialG a b) ≫ e a b = d a b ≫ Y.initialG a b)
    (a b : ℤ) :
    Φ.map (X.g a b) ≫ e (a + (0 : ℕ)) (b - (0 : ℕ)) = d a b ≫ Y.g a b := by
  apply (cancel_mono (eqToHom (congrArg (fun pq : ℤ × ℤ ↦ Y.E pq.1 pq.2)
    (show (a + (0 : ℕ), b - (0 : ℕ)) = (a, b) by ext <;> omega)))).mp
  erw [Category.assoc,
    eqToHom_naturality (fun pq : ℤ × ℤ ↦ e pq.1 pq.2)
      (show (a + (0 : ℕ), b - (0 : ℕ)) = (a, b) by ext <;> omega),
    ← eqToHom_map Φ (congrArg (fun pq : ℤ × ℤ ↦ X.E pq.1 pq.2)
      (show (a + (0 : ℕ), b - (0 : ℕ)) = (a, b) by ext <;> omega)),
    ← Category.assoc, ← Φ.map_comp]
  simpa only [BigradedExactCouple.initialG, Category.assoc] using h a b

private theorem raw_initialG (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) (a b : ℤ) :
    (rawCouple t s T K).initialG a b = rawG t s T K a b := by
  simp [BigradedExactCouple.initialG, rawCouple, rawG, Category.assoc]

private theorem equivariantPages (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) :
    ∃ M : FiniteTruncationPageMap s (finiteTruncationHeartAction s Q.functor)
        (canonicalCouple t s T K).X (canonicalCouple t s T K).X,
      (∀ a b, M.dMap 0 a b = equivariantDMap t s T P Q β K θ (a + b) (b + 1) ∧
        M.eMap 0 a b = equivariantEMap t s T P Q β K θ (a + b) b) ∧
      (∀ r a b, IsIso (M.dMap r a b) ∧ IsIso (M.eMap r a b)) := by
  apply pages_of_initial_iso s (finiteTruncationHeartAction s Q.functor)
    (rawCouple t s T K) (rawCouple t s T K)
    (fun a b ↦ equivariantDMap t s T P Q β K θ (a + b) (b + 1))
    (fun a b ↦ equivariantEMap t s T P Q β K θ (a + b) b)
  · intro a b
    dsimp only [equivariantDMap]
    infer_instance
  · intro a b
    dsimp only [equivariantEMap]
    infer_instance
  · exact equivariant_alpha t s T P Q β K θ
  · exact equivariant_f t s T P Q β K θ
  · intro a b
    dsimp only [rawCouple]
    erw [Functor.map_comp, Category.assoc, eqToHom_map,
      ← eqToHom_naturality (fun pq : ℤ × ℤ ↦
        equivariantEMap t s T P Q β K θ (pq.1 + pq.2) pq.2)
        (show (a, b) = (a + (0 : ℕ), b - (0 : ℕ)) by ext <;> omega),
      ← Category.assoc, equivariant_g, Category.assoc]

private def imagePreservation (s : TStructure D)
    (Φ : s.heart.FullSubcategory ⥤ s.heart.FullSubcategory) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {U V : s.heart.FullSubcategory} (f : U ⟶ V) :
    Φ.obj (imageSubobject f : s.heart.FullSubcategory) ≅
      (imageSubobject (Φ.map f) : s.heart.FullSubcategory) :=
  Φ.mapIso (imageSubobjectIso f) ≪≫ (PreservesImage.iso Φ f).symm ≪≫
    (imageSubobjectIso (Φ.map f)).symm

private theorem imagePreservation_arrow (s : TStructure D)
    (Φ : s.heart.FullSubcategory ⥤ s.heart.FullSubcategory) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {U V : s.heart.FullSubcategory} (f : U ⟶ V) :
    (imagePreservation s Φ f).hom ≫ (imageSubobject (Φ.map f)).arrow =
      Φ.map (imageSubobject f).arrow := by
  dsimp only [imagePreservation, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Category.assoc, Category.assoc, imageSubobject_arrow',
    PreservesImage.inv_comp_image_ι_map, ← Φ.map_comp, imageSubobject_arrow]

omit [IsTriangulated C] in
private theorem filteredMap_exists {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] {K K' : C}
    {S : FiniteTruncationCouple t s T K} {S' : FiniteTruncationCouple t s T K'}
    {l u l' u' : ℤ} (A : FiniteTruncationAbutment S l u)
    (A' : FiniteTruncationAbutment S' l' u')
    (Φ : s.heart.FullSubcategory ⥤ s.heart.FullSubcategory) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (M : FiniteTruncationPageMap s Φ S.X S'.X)
    (f : ∀ n : ℤ, Φ.obj (A.abutment n).obj ⟶ (A'.abutment n).obj)
    (hf : ∀ n p : ℤ,
      Φ.map ((A.abutment n).ι p) ≫ f n =
        M.dMap 0 p (n - p) ≫ (A'.abutment n).ι p) :
    ∃ N : FiniteTruncationFilteredMap A A' Φ M, ∀ n : ℤ, N.hom n = f n := by
  classical
  let e (n p : ℤ) := imagePreservation s Φ ((A.abutment n).ι p)
  let v (n p : ℤ) : Arrow.mk (Φ.map ((A.abutment n).ι p)) ⟶
      Arrow.mk ((A'.abutment n).ι p) :=
    Arrow.homMk (M.dMap 0 p (n - p)) (f n) (hf n p).symm
  let step (n p : ℤ) := (e n p).hom ≫ imageSubobjectMap (v n p)
  have hs (n p : ℤ) :
      Φ.map (((S.X.imageFiltration n (A.abutment n)).step p).arrow) ≫ f n =
        step n p ≫ ((S'.X.imageFiltration n (A'.abutment n)).step p).arrow := by
    dsimp only [step]
    erw [Category.assoc, imageSubobjectMap_arrow, ← Category.assoc,
      imagePreservation_arrow]
    try rfl
  let ix (n p : ℤ) := Subobject.ofLE
    ((S.X.imageFiltration n (A.abutment n)).step (p + 1))
    ((S.X.imageFiltration n (A.abutment n)).step p)
    ((S.X.imageFiltration n (A.abutment n)).antitone_step (by omega))
  let iy (n p : ℤ) := Subobject.ofLE
    ((S'.X.imageFiltration n (A'.abutment n)).step (p + 1))
    ((S'.X.imageFiltration n (A'.abutment n)).step p)
    ((S'.X.imageFiltration n (A'.abutment n)).antitone_step (by omega))
  have hq (n p : ℤ) : Φ.map (ix n p) ≫ step n p = step n (p + 1) ≫ iy n p := by
    apply (cancel_mono ((S'.X.imageFiltration n (A'.abutment n)).step p).arrow).mp
    erw [Category.assoc, ← hs, ← Category.assoc, ← Φ.map_comp,
      Subobject.ofLE_arrow, Category.assoc, Subobject.ofLE_arrow, hs]
  let gr (n p : ℤ) := (PreservesCokernel.iso Φ (ix n p)).hom ≫
    cokernel.map (Φ.map (ix n p)) (iy n p) (step n (p + 1)) (step n p) (hq n p)
  have hgr (n p : ℤ) : Φ.map (cokernel.π (ix n p)) ≫ gr n p =
      step n p ≫ cokernel.π (iy n p) := by
    dsimp only [gr]
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    exact cokernel.π_desc _ _ _
  have hfac (n p : ℤ) :
      Φ.map (factorThruImageSubobject ((A.abutment n).ι p)) ≫ step n p =
        M.dMap 0 p (n - p) ≫ factorThruImageSubobject ((A'.abutment n).ι p) := by
    apply (cancel_mono (imageSubobject ((A'.abutment n).ι p)).arrow).mp
    erw [Category.assoc, ← hs, ← Category.assoc, ← Φ.map_comp,
      imageSubobject_arrow_comp, Category.assoc, imageSubobject_arrow_comp, hf]
  have hgraded (a b : ℤ) :
      Φ.map (S.X.toGradedPiece A.abutment a b) ≫ gr (a + b) a =
        M.dMap 0 a b ≫ S'.X.toGradedPiece A'.abutment a b := by
    dsimp only [BigradedExactCouple.toGradedPiece]
    simp only [Φ.map_comp, Category.assoc]
    erw [hgr, ← Category.assoc (Φ.map (factorThruImageSubobject _)), hfac]
    rw [eqToHom_map]
    simp only [Category.assoc]
    erw [← eqToHom_naturality_assoc (fun pq : ℤ × ℤ ↦ M.dMap 0 pq.1 pq.2)
      (show (a, b) = (a, a + b - a) by ext <;> omega)]
    try simp only [Category.assoc]
  let inf (a b : ℤ) := Φ.map (A.graded a b).hom ≫
    gr (a + b) a ≫ (A'.graded a b).inv
  have hp (a b : ℤ) : Φ.map (S.X.toPageInfinity A.limits a b) ≫ inf a b =
      M.dMap 0 a b ≫ S'.X.toPageInfinity A'.limits a b := by
    dsimp only [inf]
    calc
      _ = Φ.map (S.X.toGradedPiece A.abutment a b) ≫ gr (a + b) a ≫
          (A'.graded a b).inv := by
        rw [← Φ.map_comp_assoc, A.graded_eq]
      _ = M.dMap 0 a b ≫ S'.X.toGradedPiece A'.abutment a b ≫
          (A'.graded a b).inv := by erw [← Category.assoc, hgraded, Category.assoc]
      _ = _ := by
        erw [← A'.graded_eq]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨{ hom := f
            cocone_comm := hf
            step := step
            step_comm := hs
            graded := gr
            quotient_comm := hgr
            infinity := inf
            infinity_comm := hp
            graded_comm := ?_ }, fun _ ↦ rfl⟩
  intro a b
  dsimp only [inf]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [IsTriangulated C] in
private theorem filteredMap_isIso {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] {K K' : C}
    {S : FiniteTruncationCouple t s T K} {S' : FiniteTruncationCouple t s T K'}
    {l u l' u' : ℤ} {A : FiniteTruncationAbutment S l u}
    {A' : FiniteTruncationAbutment S' l' u'}
    (Φ : s.heart.FullSubcategory ⥤ s.heart.FullSubcategory) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {M : FiniteTruncationPageMap s Φ S.X S'.X}
    (N : FiniteTruncationFilteredMap A A' Φ M)
    (hD : ∀ a b, IsIso (M.dMap 0 a b)) (hN : ∀ n, IsIso (N.hom n)) :
    (∀ n p, IsIso (N.hom n) ∧ IsIso (N.step n p) ∧ IsIso (N.graded n p)) ∧
      (∀ a b, IsIso (N.infinity a b)) := by
  have hs (n p : ℤ) : IsIso (N.step n p) := by
    let sq : Arrow.mk (Φ.map ((A.abutment n).ι p)) ⟶ Arrow.mk ((A'.abutment n).ι p) :=
      Arrow.homMk (M.dMap 0 p (n - p)) (N.hom n) (N.cocone_comm n p).symm
    have : IsIso sq.left := hD p (n - p)
    have : IsIso sq.right := hN n
    have : IsIso sq := Arrow.isIso_of_isIso_left_of_isIso_right sq
    have hi : IsIso (imageSubobjectMap sq) := by
      have : IsIso (image.map sq) := (im (C := s.heart.FullSubcategory)).map_isIso sq
      dsimp only [imageSubobjectMap]
      infer_instance
    have he : N.step n p =
        (imagePreservation s Φ ((A.abutment n).ι p)).hom ≫ imageSubobjectMap sq := by
      apply (cancel_mono ((S'.X.imageFiltration n (A'.abutment n)).step p).arrow).mp
      erw [← N.step_comm, Category.assoc, imageSubobjectMap_arrow,
        ← Category.assoc, imagePreservation_arrow]
      try rfl
    rw [he]
    infer_instance
  have hg (n p : ℤ) : IsIso (N.graded n p) := by
    let ix := Subobject.ofLE
      ((S.X.imageFiltration n (A.abutment n)).step (p + 1))
      ((S.X.imageFiltration n (A.abutment n)).step p)
      ((S.X.imageFiltration n (A.abutment n)).antitone_step (by omega))
    let iy := Subobject.ofLE
      ((S'.X.imageFiltration n (A'.abutment n)).step (p + 1))
      ((S'.X.imageFiltration n (A'.abutment n)).step p)
      ((S'.X.imageFiltration n (A'.abutment n)).antitone_step (by omega))
    have hq : Φ.map ix ≫ N.step n p = N.step n (p + 1) ≫ iy := by
      apply (cancel_mono ((S'.X.imageFiltration n (A'.abutment n)).step p).arrow).mp
      erw [Category.assoc, ← N.step_comm, ← Category.assoc, ← Φ.map_comp,
        Subobject.ofLE_arrow, Category.assoc, Subobject.ofLE_arrow, N.step_comm]
    have : IsIso (N.step n p) := hs n p
    have : IsIso (N.step n (p + 1)) := hs n (p + 1)
    let g := (PreservesCokernel.iso Φ ix).hom ≫
      cokernel.map (Φ.map ix) iy (N.step n (p + 1)) (N.step n p) hq
    have he : N.graded n p = g := by
      apply (cancel_epi (Φ.map (cokernel.π ix))).mp
      dsimp only [g]
      erw [N.quotient_comm, ← Category.assoc, PreservesCokernel.π_iso_hom,
        cokernel.π_desc]
    rw [he]
    dsimp only [g]
    infer_instance
  refine ⟨fun n p ↦ ⟨hN n, hs n p, hg n p⟩, fun a b ↦ ?_⟩
  have := hg (a + b) a
  have hi : IsIso (N.infinity a b ≫ (A'.graded a b).hom) := by
    rw [← N.graded_comm]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

private theorem toAbutment_natural (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    {K K' : C} (v : K ⟶ K') (n p : ℤ) :
    (finiteTruncationD t s T p (n - p)).map v ≫
        (canonicalCouple t s T K').toAbutment n p =
      (canonicalCouple t s T K).toAbutment n p ≫
        (shiftFunctor D n ⋙ s.homology₀).map (T.map v) := by
  dsimp only [FiniteTruncationCouple.toAbutment, canonicalCouple]
  simp only [Iso.refl_hom, Category.id_comp, Category.assoc]
  dsimp only [finiteTruncationD, Functor.comp_map]
  erw [← Category.assoc, eqToHom_naturality
    (fun q : ℤ ↦ s.homology₀.map ((shiftFunctor D q).map
      (T.map ((t.truncLT (n - p + 1)).map v))))
    (show p + (n - p) = n by omega)]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 3
  exact congrArg T.map ((t.truncLTι (n - p + 1)).naturality v)

set_option maxHeartbeats 800000 in
-- The heart comparison and the indexed truncation counits carry nested casts.
private theorem equivariant_toAbutment (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) (n p : ℤ) :
    (finiteTruncationHeartAction s Q.functor).map
        ((canonicalCouple t s T K).toAbutment n p) ≫
        (finiteTruncationHeartComparison s Q.functor (T.obj K) n).hom ≫
          (shiftFunctor D n ⋙ s.homology₀).map ((β.app K).hom ≫ T.map θ.hom) =
      equivariantDMap t s T P Q β K θ (p + (n - p)) (n - p + 1) ≫
        (canonicalCouple t s T K).toAbutment n p := by
  dsimp only [FiniteTruncationCouple.toAbutment, canonicalCouple]
  simp only [Iso.refl_hom, Category.id_comp, Functor.map_comp, Category.assoc]
  erw [eqToHom_map,
    eqToHom_naturality_assoc (fun m : ℤ ↦
      equivariantDMap t s T P Q β K θ m (n - p + 1))
      (show p + (n - p) = n by omega)]
  try simp only [Category.assoc]
  congr 1
  dsimp only [equivariantDMap]
  erw [← Category.assoc, heartComparison_natural]
  have hc := congrArg ((shiftFunctor D n ⋙ s.homology₀).map)
    (upperEquivariant_counit t T P Q β K θ (n - p + 1))
  simp only [Functor.map_comp] at hc
  simpa only [Category.assoc] using congrArg (fun f ↦
    (finiteTruncationHeartComparison s Q.functor
      (T.obj ((t.truncLT (n - p + 1)).obj K)) n).hom ≫ f) hc.symm

private theorem equivariantFiltered {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] [T.IsTriangulated]
    (P : C ≌ C) (Q : D ≌ D) [P.functor.CommShift ℤ]
    [P.functor.IsTriangulated] [P.functor.IsTExact t t]
    [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
    (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
    (K : C) (θ : P.functor.obj K ≅ K) {l u : ℤ}
    (A : FiniteTruncationAbutment (canonicalCouple t s T K) l u)
    (M : FiniteTruncationPageMap s (finiteTruncationHeartAction s Q.functor)
      (canonicalCouple t s T K).X (canonicalCouple t s T K).X)
    (hM : ∀ a b, M.dMap 0 a b = equivariantDMap t s T P Q β K θ (a + b) (b + 1)) :
    ∃ N : FiniteTruncationFilteredMap A A (finiteTruncationHeartAction s Q.functor) M,
      (∀ n, (finiteTruncationHeartAction s Q.functor).map (eqToHom (A.obj_eq n)) ≫
          (finiteTruncationHeartComparison s Q.functor (T.obj K) n).hom ≫
          (shiftFunctor D n ⋙ s.homology₀).map ((β.app K).hom ≫ T.map θ.hom) =
        N.hom n ≫ eqToHom (A.obj_eq n)) ∧
      (∀ n, IsIso (N.hom n)) := by
  let Φ := finiteTruncationHeartAction s Q.functor
  let f (n : ℤ) := Φ.map (eqToHom (A.obj_eq n)) ≫
    (finiteTruncationHeartComparison s Q.functor (T.obj K) n).hom ≫
    (shiftFunctor D n ⋙ s.homology₀).map ((β.app K).hom ≫ T.map θ.hom) ≫
    eqToHom (A.obj_eq n).symm
  have hf (n p : ℤ) : Φ.map ((A.abutment n).ι p) ≫ f n =
      M.dMap 0 p (n - p) ≫ (A.abutment n).ι p := by
    dsimp only [f]
    apply (cancel_mono (eqToHom (A.obj_eq n))).mp
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    erw [← Category.assoc, ← Φ.map_comp, A.map_eq]
    erw [hM]
    simpa only [Category.assoc] using equivariant_toAbutment t s T P Q β K θ n p
  obtain ⟨N, hN⟩ := filteredMap_exists A A Φ M f hf
  refine ⟨N, fun n ↦ ?_, fun n ↦ ?_⟩
  · rw [hN]
    simp only [f, Φ, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · rw [hN]
    dsimp only [f]
    infer_instance

private theorem naturalFiltered {t : TStructure C} {s : TStructure D}
    {T : C ⥤ D} [T.CommShift ℤ] [T.IsTriangulated] {K K' : C}
    {l u l' u' : ℤ}
    (A : FiniteTruncationAbutment (canonicalCouple t s T K) l u)
    (A' : FiniteTruncationAbutment (canonicalCouple t s T K') l' u')
    (v : K ⟶ K')
    (M : FiniteTruncationPageMap s (𝟭 _)
      (canonicalCouple t s T K).X (canonicalCouple t s T K').X)
    (hM : ∀ a b : ℤ, M.dMap 0 a b = (finiteTruncationD t s T a b).map v) :
    ∃ N : FiniteTruncationFilteredMap A A' (𝟭 _) M,
      ∀ n : ℤ, N.hom n ≫ eqToHom (A'.obj_eq n) = eqToHom (A.obj_eq n) ≫
        (shiftFunctor D n ⋙ s.homology₀).map (T.map v) := by
  let f (n : ℤ) := eqToHom (A.obj_eq n) ≫
    (shiftFunctor D n ⋙ s.homology₀).map (T.map v) ≫ eqToHom (A'.obj_eq n).symm
  have hf (n p : ℤ) : (A.abutment n).ι p ≫ f n =
      M.dMap 0 p (n - p) ≫ (A'.abutment n).ι p := by
    dsimp only [f]
    apply (cancel_mono (eqToHom (A'.obj_eq n))).mp
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc, A.map_eq, A'.map_eq, hM]
    exact (toAbutment_natural t s T v n p).symm
  obtain ⟨N, hN⟩ := filteredMap_exists A A' (𝟭 _) M f hf
  refine ⟨N, fun n ↦ ?_⟩
  rw [hN]
  simp only [f, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem raise_lower_bound (t : TStructure C) (X : C) [t.IsGE X 0]
    (h : IsZero (t.homology₀.obj X)) : t.IsGE X 1 := by
  have h0 : IsZero ((t.truncGE 0).obj ((t.truncLE 0).obj X)) :=
    t.heart.ι.map_isZero h
  have : IsIso ((t.truncGEπ 0).app ((t.truncLE 0).obj X)) := inferInstance
  have hz : IsZero ((t.truncLE 0).obj X) :=
    h0.of_iso (asIso ((t.truncGEπ 0).app ((t.truncLE 0).obj X)))
  exact t.isGE₂ _ (t.triangleLEGE_distinguished 0 1 rfl X) 1
    (t.isGE_of_isZero hz 1) (by
      change t.IsGE ((t.truncGE 1).obj X) 1
      infer_instance)

private theorem lower_upper_bound (t : TStructure C) (X : C) [t.IsLE X 0]
    (h : IsZero (t.homology₀.obj X)) : t.IsLE X (-1) := by
  have h0 : IsZero ((t.truncGE 0).obj ((t.truncLE 0).obj X)) :=
    t.heart.ι.map_isZero h
  have : IsIso ((t.truncLEι 0).app X) := inferInstance
  have hz : IsZero ((t.truncGE 0).obj X) :=
    h0.of_iso ((t.truncGE 0).mapIso (asIso ((t.truncLEι 0).app X)).symm)
  exact t.isLE₂ _ (t.triangleLEGE_distinguished (-1) 0 (by omega) X) (-1)
    (by change t.IsLE ((t.truncLE (-1)).obj X) (-1); infer_instance)
    (t.isLE_of_isZero hz (-1))

private theorem support_bounds (t : TStructure C) (ht : t.bounded = ⊤)
    (K : C) (l u : ℤ)
    (h : ∀ b : ℤ, b < l ∨ u < b → IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K)) :
    t.IsGE K l ∧ t.IsLE K u := by
  have hb : t.bounded K := by rw [ht]; trivial
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  constructor
  · by_cases hl : l ≤ a
    · have := ha
      exact t.isGE_of_ge K l a hl
    · have H (n : ℕ) (hn : a + n ≤ l) : t.IsGE K (a + n) := by
        induction n with
        | zero => simpa using ha
        | succ n ih =>
          have := ih (by omega)
          have := t.isGE_shift K (a + n) (a + n) 0 (by omega)
          have := raise_lower_bound t ((shiftFunctor C (a + n)).obj K)
            (h (a + n) (Or.inl (by omega)))
          exact t.isGE_of_shift K (a + (n + 1 : ℕ)) (a + n) 1 (by omega)
      convert H (l - a).toNat (by omega) using 1
      omega
  · by_cases hu : b ≤ u
    · have := hb
      exact t.isLE_of_le K b u hu
    · have H (n : ℕ) (hn : u ≤ b - n) : t.IsLE K (b - n) := by
        induction n with
        | zero => simpa using hb
        | succ n ih =>
          have := ih (by omega)
          have := t.isLE_shift K (b - n) (b - n) 0 (by omega)
          have := lower_upper_bound t ((shiftFunctor C (b - n)).obj K)
            (h (b - n) (Or.inr (by omega)))
          exact t.isLE_of_shift K (b - (n + 1 : ℕ)) (b - n) (-1) (by omega)
      convert H (b - u).toNat (by omega) using 1
      omega

private theorem allPages_zero (s : TStructure D)
    (X : BigradedExactCouple s.heart.FullSubcategory 0) (a b : ℤ)
    (h : IsZero (X.E a b)) (r : ℕ) : IsZero ((X.pageCouple r).E a b) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    exact IsZero.of_epi ((X.pageCouple r).derivedEProjection a b)
      (IsZero.of_mono (kernel.ι ((X.pageCouple r).d a b)) ih)

private theorem homology_zero_of_isGE (t : TStructure C) (X : C) [t.IsGE X 1] :
    IsZero (t.homology₀.obj X) := by
  have hz : IsZero ((t.homology₀.obj X).obj) :=
    (t.truncGE 0).map_isZero (t.isZero_truncLT_obj_of_isGE 1 X)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply t.heart.ι.map_injective
  simp only [Functor.map_id, Functor.map_zero]
  exact hz.eq_zero_of_src _

omit [IsTriangulated C] [IsTriangulated D] in
private theorem preserves_lower (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ]
    (hT : ∀ K : C, t.IsGE K 0 → s.IsGE (T.obj K) 0)
    (K : C) (n : ℤ) [t.IsGE K n] : s.IsGE (T.obj K) n := by
  have := t.isGE_shift K n n 0 (by omega)
  have : s.IsGE ((shiftFunctor C n ⋙ T).obj K) 0 :=
    hT ((shiftFunctor C n).obj K) inferInstance
  have h : s.IsGE ((T ⋙ shiftFunctor D n).obj K) 0 :=
    s.isGE_of_iso ((T.commShiftIso n).app K) 0
  have : s.IsGE ((shiftFunctor D n).obj (T.obj K)) 0 := h
  exact s.isGE_of_shift (T.obj K) n n 0 (by omega)

private theorem canonical_vanishing (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (hT : ∀ K : C, t.IsGE K 0 → s.IsGE (T.obj K) 0)
    (K : C) (l u : ℤ) [t.IsGE K l] [t.IsLE K u] :
    (∀ a b : ℤ, b < l → IsZero ((rawCouple t s T K).D a b)) ∧
      (∀ a b : ℤ, a < 0 ∨ b < l ∨ u < b → IsZero ((rawCouple t s T K).E a b)) := by
  constructor
  · intro a b hb
    have : t.IsGE ((t.truncLT (b + 1)).obj K) l := inferInstance
    exact (T ⋙ shiftFunctor D (a + b) ⋙ s.homology₀).map_isZero
      (t.isZero ((t.truncLT (b + 1)).obj K) b l hb)
  · intro a b hb
    rcases hb with ha | hb | hb
    · have := preserves_lower t s T hT ((t.truncGELT b (b + 1)).obj K) b
      have := s.isGE_shift (T.obj ((t.truncGELT b (b + 1)).obj K))
        b (a + b) (-a) (by omega)
      have := s.isGE_of_ge
        ((shiftFunctor D (a + b)).obj (T.obj ((t.truncGELT b (b + 1)).obj K)))
        1 (-a) (by omega)
      exact homology_zero_of_isGE s _
    · have hz : IsZero ((t.truncLT (b + 1)).obj K) :=
        t.isZero ((t.truncLT (b + 1)).obj K) b l hb
      exact (t.truncGE b ⋙ T ⋙ shiftFunctor D (a + b) ⋙ s.homology₀).map_isZero hz
    · have : t.IsLE ((t.truncGELT b (b + 1)).obj K) u := by
        change t.IsLE ((t.truncGE b).obj ((t.truncLT (b + 1)).obj K)) u
        infer_instance
      exact (T ⋙ shiftFunctor D (a + b) ⋙ s.homology₀).map_isZero
        (t.isZero ((t.truncGELT b (b + 1)).obj K) u b hb)

omit [IsTriangulated C] in
private theorem canonical_abutment_iso (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (hT : ∀ K : C, t.IsGE K 0 → s.IsGE (T.obj K) 0) (K : C) (n : ℤ) :
    IsIso ((shiftFunctor D n ⋙ s.homology₀).map
      (T.map ((t.truncLTι (n + 1)).app K))) := by
  let U := (shiftFunctor D n).mapTriangle.obj
    (T.mapTriangle.obj ((t.triangleLTGE (n + 1)).obj K))
  have hU := (shiftFunctor D n).map_distinguished _
    (T.map_distinguished _ (t.triangleLTGE_distinguished (n + 1) K))
  have := preserves_lower t s T hT ((t.truncGE (n + 1)).obj K) (n + 1)
  have : s.IsGE U.obj₃ 1 := by
    change s.IsGE ((shiftFunctor D n).obj (T.obj ((t.truncGE (n + 1)).obj K))) 1
    exact s.isGE_shift _ (n + 1) n 1 (by omega)
  have : s.IsGE U.obj₃ 0 := s.isGE_of_ge U.obj₃ 0 1 (by omega)
  have : Mono (s.homology₀.map U.mor₁) :=
    (s.homology₀_exact_mono_of_isGE₃ U hU inferInstance).2
  have : Epi (s.homology₀.map U.mor₁) :=
    (s.homology₀_exact U hU).epi_f_iff.mpr
      ((homology_zero_of_isGE s U.obj₃).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi (s.homology₀.map U.mor₁)

private theorem incoming_succ {B : Type*} [Category B] [Abelian B]
    (X : BigradedExactCouple B 0) (r : ℕ) (p q : ℤ) :
    X.incomingAlphaIter (r + 1) p q =
      X.alpha (p + (r + 1 : ℕ)) (q - (r + 1 : ℕ)) ≫
        eqToHom (by congr 1 <;> omega) ≫ X.incomingAlphaIter r p q := by
  apply eq_of_heq
  dsimp [BigradedExactCouple.incomingAlphaIter, BigradedExactCouple.alphaIter]
  simp only [Category.assoc]
  apply heq_comp rfl rfl rfl HEq.rfl
  simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  rw [heq_eqToHom_comp_iff]
  congr! 1 <;> omega

private theorem incoming_cocone_step {B : Type*} [Category B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (H : B)
    (k : ∀ p : ℤ, X.D p (n - p) ⟶ H)
    (hk : ∀ p : ℤ, X.alphaDiagonal n p ≫ k p = k (p + 1))
    (p q q' : ℤ) (h : q = p + 1) (h' : q' = q) :
    HEq (X.alpha q' (n - q) ≫
      eqToHom (congrArg₂ X.D (show q' - 1 = p by omega)
        (show n - q + 1 = n - p by omega)) ≫ k p) (k q) := by
  subst q'
  subst q
  simpa only [BigradedExactCouple.alphaDiagonal, Category.assoc] using (hk p).heq

private theorem incoming_cocone {B : Type*} [Category B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (H : B)
    (k : ∀ p : ℤ, X.D p (n - p) ⟶ H)
    (hk : ∀ p : ℤ, X.alphaDiagonal n p ≫ k p = k (p + 1)) (r : ℕ) :
    X.incomingAlphaIter r 0 n ≫ eqToHom (by congr 1; omega) ≫ k 0 =
      eqToHom (by congr 1; omega) ≫ k r := by
  induction r with
  | zero =>
    simp [BigradedExactCouple.incomingAlphaIter, BigradedExactCouple.alphaIter]
  | succ r ih =>
    rw [incoming_succ, Category.assoc, Category.assoc, ih]
    have hh := hk (r : ℤ)
    dsimp only [BigradedExactCouple.alphaDiagonal] at hh
    apply eq_of_heq
    simp only [eqToHom_trans_assoc, heq_eqToHom_comp_iff]
    exact incoming_cocone_step X n H k hk (r : ℤ) ((r + 1 : ℕ) : ℤ)
      (0 + ((r + 1 : ℕ) : ℤ)) (by omega) (by omega)

private theorem incoming_cocone_int {B : Type*} [Category B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (H : B)
    (k : ∀ p : ℤ, X.D p (n - p) ⟶ H)
    (hk : ∀ p : ℤ, X.alphaDiagonal n p ≫ k p = k (p + 1))
    (p : ℤ) (hp : 0 ≤ p) :
    eqToHom (congrArg₂ X.D
      (show 0 + (p.toNat : ℤ) = p by omega)
      (show n - (p.toNat : ℤ) = n - p by omega)) ≫ k p =
        X.incomingAlphaIter p.toNat 0 n ≫
          eqToHom (congrArg₂ X.D (show (0 : ℤ) = 0 from rfl) (show n = n - 0 by omega)) ≫ k 0 := by
  lift p to ℕ using hp
  simpa only [Int.toNat_natCast] using (incoming_cocone X n H k hk p).symm

private theorem incoming_cocone_reindexed {B : Type*} [Category B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (H : B)
    (k : ∀ p : ℤ, X.D p (n - p) ⟶ H)
    (hk : ∀ p : ℤ, X.alphaDiagonal n p ≫ k p = k (p + 1))
    (j : ∀ q : ℤ, X.D (n - q) q ⟶ H)
    (hj : ∀ p : ℤ, eqToHom (congrArg₂ X.D
      (show p = n - (n - p) by omega) (show n - p = n - p from rfl)) ≫
      j (n - p) = k p) (p : ℤ) (hp : 0 ≤ p) :
    eqToHom (congrArg₂ X.D
      (show 0 + (p.toNat : ℤ) = n - (n - p) by omega)
      (show n - (p.toNat : ℤ) = n - p by omega)) ≫ j (n - p) =
        X.incomingAlphaIter p.toNat 0 n ≫
          eqToHom (congrArg₂ X.D (show (0 : ℤ) = 0 from rfl)
            (show n = n - 0 by omega)) ≫ k 0 := by
  calc
    _ = eqToHom (congrArg₂ X.D (show 0 + (p.toNat : ℤ) = p by omega)
        (show n - (p.toNat : ℤ) = n - p by omega)) ≫
        (eqToHom (congrArg₂ X.D (show p = n - (n - p) by omega)
          (show n - p = n - p from rfl)) ≫ j (n - p)) := by
      simp only [← Category.assoc, eqToHom_trans]
    _ = _ := by
      rw [hj]
      exact incoming_cocone_int X n H k hk p hp

private theorem toAbutment_comm (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated] (K : C) (n p : ℤ) :
    (rawCouple t s T K).alphaDiagonal n p ≫
        (canonicalCouple t s T K).toAbutment n p =
      (canonicalCouple t s T K).toAbutment n (p + 1) := by
  dsimp only [BigradedExactCouple.alphaDiagonal, rawCouple,
    FiniteTruncationCouple.toAbutment, canonicalCouple, Iso.refl_hom]
  simp only [Category.id_comp, rawAlpha, Category.assoc, eqToHom_trans_assoc]
  erw [← eqToHom_naturality (fun mn : ℤ × ℤ ↦
    (shiftFunctor D mn.1 ⋙ s.homology₀).map (T.map ((t.truncLTι mn.2).app K)))
    (show (p + 1 + (n - (p + 1)), n - (p + 1) + 1 + 1) =
      (n, n - p + 1) by ext <;> omega)]
  simp only [← Category.assoc, ← Functor.map_comp]
  erw [t.natTransTruncLTOfLE_ι_app]
  apply eq_of_heq
  simp only [comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
  have h : p + 1 + (n - (p + 1)) = n := by omega
  change HEq
    ((shiftFunctor D (p + 1 + (n - (p + 1))) ⋙ s.homology₀).map
      (T.map ((t.truncLTι (n - (p + 1) + 1)).app K)))
    ((shiftFunctor D n ⋙ s.homology₀).map
      (T.map ((t.truncLTι (n - (p + 1) + 1)).app K)))
  rw [h]

set_option maxHeartbeats 800000 in
-- The finite filtration and convergence structures have many dependent fields.
private theorem canonicalAbutment (t : TStructure C) (s : TStructure D)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (hT : ∀ K : C, t.IsGE K 0 → s.IsGE (T.obj K) 0)
    (K : C) (l u : ℤ) [t.IsGE K l] [t.IsLE K u] :
    Nonempty (FiniteTruncationAbutment (canonicalCouple t s T K) l u) := by
  classical
  let X := rawCouple t s T K
  let S := canonicalCouple t s T K
  obtain ⟨hD, hE⟩ := canonical_vanishing t s T hT K l u
  have hE' (a b : ℤ) (h : a < 0 ∨ b < l) : IsZero (X.E a b) :=
    hE a b (h.imp_right Or.inl)
  obtain ⟨L, _, _, _, _, _, _, _, _, hcomplete, _⟩ :=
    BigradedExactCouple.halfPlaneConvergence X l hD hE'
  let H (n : ℤ) := (shiftFunctor D n ⋙ s.homology₀).obj (T.obj K)
  let k (n p : ℤ) := S.toAbutment n p
  let j (n q : ℤ) : X.D (n - q) q ⟶ H n :=
    eqToHom (by congr 1; omega) ≫ k n (n - q)
  let c (n : ℤ) : X.D 0 n ⟶ H n :=
    eqToHom (by congr 1; omega) ≫ k n 0
  have hc (n : ℤ) : c n = eqToHom (by congr 1; omega) ≫ j n n := by
    apply eq_of_heq
    dsimp only [c, j]
    simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    congr! 1
    omega
  have hiso (n : ℤ) : IsIso (c n) := by
    have hi (m : ℤ) (hm : m = n + 1) :
        IsIso ((shiftFunctor D n ⋙ s.homology₀).map
          (T.map ((t.truncLTι m).app K))) := by
      subst m
      exact canonical_abutment_iso t s T hT K n
    have : IsIso ((shiftFunctor D n ⋙ s.homology₀).map
        (T.map ((t.truncLTι (n - 0 + 1)).app K))) := hi _ (by omega)
    dsimp [c, k, S, canonicalCouple, FiniteTruncationCouple.toAbutment]
    simp only [Category.id_comp]
    change IsIso (eqToHom _ ≫ eqToHom _ ≫
      (shiftFunctor D n ⋙ s.homology₀).map
        (T.map ((t.truncLTι (n - 0 + 1)).app K)))
    infer_instance
  have hj (n p : ℤ) : eqToHom (by congr 1; omega) ≫ j n (n - p) = k n p := by
    apply eq_of_heq
    dsimp only [j]
    simp only [eqToHom_comp_heq_iff]
    congr! 1
    omega
  have hcomm (n p : ℤ) :
      X.alphaDiagonal n p ≫ eqToHom (by congr 1; omega) ≫ j n (n - p) =
        eqToHom (by congr 1; omega) ≫ j n (n - (p + 1)) := by
    rw [hj, hj]
    exact toAbutment_comm t s T K n p
  have hnorm (n p : ℤ) (hp : 0 ≤ p) :
      eqToHom (congrArg₂ X.D
        (show 0 + (p.toNat : ℤ) = n - (n - p) by omega)
        (show n - (p.toNat : ℤ) = n - p by omega)) ≫ j n (n - p) =
        X.incomingAlphaIter p.toNat 0 n ≫ c n := by
    exact incoming_cocone_reindexed X n (H n) (k n)
      (toAbutment_comm t s T K n) (j n) (hj n) p hp
  obtain ⟨FA, FH, _, _, _, _, _, _, _, _, AH, hAH, hmap, hconv⟩ :=
    abutment_image_filtration X l hD hE' L H j c hc hiso hcomm hnorm
  have hmap' (n p : ℤ) : (AH n).ι p ≫ eqToHom (hAH n) = S.toAbutment n p := by
    rw [hmap, hj]
  have htop (n : ℤ) : (X.imageFiltration n (AH n)).step 0 = ⊤ := by
    have : IsIso ((AH n).ι 0) := by
      have hi : IsIso ((AH n).ι 0 ≫ eqToHom (hAH n)) := by
        rw [hmap']
        have : IsIso (k n 0) := by
          have := hiso n
          dsimp only [c] at this
          exact (isIso_comp_left_iff _ _).mp this
        exact this
      exact (isIso_comp_right_iff _ _).mp hi
    change imageSubobject ((AH n).ι 0) = ⊤
    rw [imageSubobject_mono]
    exact Subobject.mk_eq_top_of_isIso _
  have hbot (n : ℤ) : (X.imageFiltration n (AH n)).step (n - l + 1) = ⊥ := by
    change imageSubobject ((AH n).ι (n - l + 1)) = ⊥
    have hz : (AH n).ι (n - l + 1) = 0 :=
      (hD (n - l + 1) (n - (n - l + 1)) (by omega)).eq_zero_of_src _
    rw [hz, imageSubobject_zero]
  choose gr hgr huniq using X.weakConvergence_comparison L AH hconv.2.1.1
  exact ⟨{ d_zero := hD
           page_zero := fun r a b h ↦ allPages_zero s X a b (hE a b h) r
           limits := L
           abutment := AH
           obj_eq := hAH
           map_eq := hmap'
           finite := fun n ↦ ⟨0, n - l + 1, htop n, hbot n⟩
           exhaustive := fun n ↦ (hconv.2.1.2 n).2
           separated := fun n ↦ (hconv.2.1.2 n).1
           regular := hconv.1
           complete := hcomplete
           converges := hconv
           graded := gr
           graded_eq := hgr }⟩

/-- The finite truncation spectral sequence for an exact functor of bounded t-categories.
Its E₂ identification is `S.eIso ≪≫ finiteTruncationE₂Iso`, and the page recurrence is
literally the `BigradedExactCouple.pageCouple` recursion by kernels modulo images.
Source: BBD 1.3.3–1.3.7; Stacks 011R, 011S, 012W; latest blueprint,
`lem-zl-composition-weight-bound.proof.md`, paragraph 1
(blueprint: lem-zl-finite-truncation-spectral-sequence).

Proof, following the eight steps of the DAG node:
1. Starting with boundedness, finite induction removes zero cohomology layers using
   the canonical truncation triangles. This recovers the stated t-bounds; upper truncation
   is zero below l and is K above u.
2. Apply T and heart cohomology to the adjacent truncation triangles. Their long exact
   sequences give exactly alpha, f and g below. Shift comparison gives the displayed E₂.
3. Derive the exact couple repeatedly. Left t-exactness kills its negative first indices;
   the support bound kills its second indices outside [l,u]. Subquotients preserve these
   vanishings, giving the half-plane hypotheses.
4. Half-plane convergence gives the finite image filtration. The triangle τ≤n K → K →
   τ≥n+1 K identifies the diagonal abutment with Hⁿ(TK), since T preserves all lower bounds.
   The maps in that identification are exactly `toAbutment`, giving the claimed images.
5. Truncation functoriality gives maps of the adjacent triangles; their long exact sequences
   give maps of couples. Derived images, kernels and quotients give the maps of pages and
   the compatible maps on the image filtration and its graded objects.
6. A t-exact Q restricts to an exact equivalence of hearts, by the short-exact triangle
   criterion. Its truncation and cohomology comparisons commute with the canonical maps.
7. The maps `finiteTruncationTowerIso` commute with inclusions, projections and connecting
   arrows by naturality of beta and the truncation comparisons. Apply the exact heart
   equivalence and derive the resulting couple isomorphism. It gives precisely the
   differential, image, quotient and graded compatibilities below. On the abutment the
   map is Hⁿ(beta_K followed by T(theta)), after the canonical Q cohomology comparison.
8. For T=Rv the adjacent triangles, shift comparisons and truncation counits are the same
   ones in `exists_truncationHypercohomology`. Hence the initial couples, their recursively
   derived pages and the normalized graded image filtration agree. All triangles used
   are in the underlying triangulated categories, never in a category of fixed pairs.
-/
theorem exists_finiteTruncationSpectralSequence
    (t : TStructure C) (s : TStructure D)
    (_ht : t.bounded = ⊤) (_hs : s.bounded = ⊤)
    (T : C ⥤ D) [T.CommShift ℤ] [T.IsTriangulated]
    (_hT : ∀ K : C, t.IsGE K 0 → s.IsGE (T.obj K) 0) :
    ∃ S : ∀ K : C, FiniteTruncationCouple t s T K,
    ∃ M : ∀ {K K' : C}, (K ⟶ K') →
      FiniteTruncationPageMap s (𝟭 _) (S K).X (S K').X,
    ∃ A : ∀ (K : C) (l u : ℤ),
      (∀ b : ℤ, b < l ∨ u < b → IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K)) →
      FiniteTruncationAbutment (S K) l u,
    (∀ {K K' : C} (v : K ⟶ K') (a b : ℤ),
      (M v).dMap 0 a b ≫ ((S K').dIso a b).hom =
        ((S K).dIso a b).hom ≫ (finiteTruncationD t s T a b).map v ∧
      (M v).eMap 0 a b ≫ ((S K').eIso a b).hom =
        ((S K).eIso a b).hom ≫ (finiteTruncationE t s T a b).map v) ∧
    (∀ (K : C) (r : ℕ) (a b : ℤ),
      (M (𝟙 K)).dMap r a b = 𝟙 _ ∧ (M (𝟙 K)).eMap r a b = 𝟙 _) ∧
    (∀ {K K' K'' : C} (v : K ⟶ K') (w : K' ⟶ K'') (r : ℕ) (a b : ℤ),
      (M (v ≫ w)).dMap r a b = (M v).dMap r a b ≫ (M w).dMap r a b ∧
      (M (v ≫ w)).eMap r a b = (M v).eMap r a b ≫ (M w).eMap r a b) ∧
    (∀ {K K' : C} (v : K ⟶ K') (l u l' u' : ℤ)
      (h : ∀ b : ℤ, b < l ∨ u < b → IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K))
      (h' : ∀ b : ℤ, b < l' ∨ u' < b →
        IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K')),
      ∃ N : FiniteTruncationFilteredMap (A K l u h) (A K' l' u' h') (𝟭 _) (M v),
        ∀ n : ℤ, N.hom n ≫ eqToHom ((A K' l' u' h').obj_eq n) =
          eqToHom ((A K l u h).obj_eq n) ≫
            (shiftFunctor D n ⋙ s.homology₀).map (T.map v)) ∧
    (∀ (P : C ≌ C) (Q : D ≌ D)
      [P.functor.CommShift ℤ] [P.functor.IsTriangulated] [P.functor.IsTExact t t]
      [Q.functor.CommShift ℤ] [Q.functor.IsTriangulated] [Q.functor.IsTExact s s]
      (β : T ⋙ Q.functor ≅ P.functor ⋙ T) [NatTrans.CommShift β.hom ℤ]
      (K : C) (θ : P.functor.obj K ≅ K) (l u : ℤ)
      (h : ∀ b : ℤ, b < l ∨ u < b → IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K)),
      ∃ V : FiniteTruncationPageMap s (finiteTruncationHeartAction s Q.functor)
        (S K).X (S K).X,
      ∃ W : FiniteTruncationFilteredMap (A K l u h) (A K l u h)
        (finiteTruncationHeartAction s Q.functor) V,
      (∀ (r : ℕ) (a b : ℤ), IsIso (V.dMap r a b) ∧ IsIso (V.eMap r a b)) ∧
      (∀ n p : ℤ, IsIso (W.hom n) ∧ IsIso (W.step n p) ∧ IsIso (W.graded n p)) ∧
      (∀ a b : ℤ, IsIso (W.infinity a b)) ∧
      (∀ a b : ℤ,
        (finiteTruncationHeartAction s Q.functor).map ((S K).dIso a b).hom ≫
          (finiteTruncationHeartComparison s Q.functor
            (T.obj ((t.truncLT (b + 1)).obj K)) (a + b)).hom ≫
          (shiftFunctor D (a + b) ⋙ s.homology₀).map
            (finiteTruncationTowerIso t T P Q β K θ b).hom =
          V.dMap 0 a b ≫ ((S K).dIso a b).hom) ∧
      (∀ a b : ℤ,
        (finiteTruncationHeartAction s Q.functor).map ((S K).eIso a b).hom ≫
          (finiteTruncationHeartComparison s Q.functor
            (T.obj ((t.truncGELT b (b + 1)).obj K)) (a + b)).hom ≫
          (shiftFunctor D (a + b) ⋙ s.homology₀).map
            (finiteTruncationLayerIso t T P Q β K θ b).hom =
          V.eMap 0 a b ≫ ((S K).eIso a b).hom) ∧
      (∀ n : ℤ,
        (finiteTruncationHeartAction s Q.functor).map
            (eqToHom ((A K l u h).obj_eq n)) ≫
          (finiteTruncationHeartComparison s Q.functor (T.obj K) n).hom ≫
          (shiftFunctor D n ⋙ s.homology₀).map
            ((β.app K).hom ≫ T.map θ.hom) =
          W.hom n ≫ eqToHom ((A K l u h).obj_eq n))) := by
  classical
  obtain ⟨M, hM, hid, hcomp⟩ := canonicalPages t s T
  have hA (K : C) (l u : ℤ)
      (h : ∀ b : ℤ, b < l ∨ u < b → IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K)) :
      Nonempty (FiniteTruncationAbutment (canonicalCouple t s T K) l u) := by
    obtain ⟨h₁, h₂⟩ := support_bounds t _ht K l u h
    exact canonicalAbutment t s T _hT K l u
  let A (K : C) (l u : ℤ)
      (h : ∀ b : ℤ, b < l ∨ u < b → IsZero ((shiftFunctor C b ⋙ t.homology₀).obj K)) :=
    (hA K l u h).some
  refine ⟨canonicalCouple t s T, M, A, ?_, hid, hcomp, ?_, ?_⟩
  · intro K K' v a b
    constructor
    · erw [Category.comp_id, Category.id_comp]
      exact (hM v a b).1
    · erw [Category.comp_id, Category.id_comp]
      exact (hM v a b).2
  · intro K K' v l u l' u' h h'
    exact naturalFiltered (A K l u h) (A K' l' u' h') v (M v)
      (fun a b ↦ (hM v a b).1)
  · intro P Q _ _ _ _ _ _ β _ K θ l u h
    obtain ⟨V, hV, hVIso⟩ := equivariantPages t s T P Q β K θ
    obtain ⟨W, hW, hWIso⟩ := equivariantFiltered P Q β K θ (A K l u h) V
      (fun a b ↦ (hV a b).1)
    obtain ⟨hsteps, hinf⟩ := filteredMap_isIso
      (finiteTruncationHeartAction s Q.functor) W
      (fun a b ↦ (hVIso 0 a b).1) hWIso
    refine ⟨V, W, hVIso, hsteps, hinf, ?_, ?_, hW⟩
    · intro a b
      erw [Functor.map_id, Category.id_comp, Category.comp_id]
      exact (hV a b).1.symm
    · intro a b
      erw [Functor.map_id, Category.id_comp, Category.comp_id]
      exact (hV a b).2.symm

/-- The standard heart cohomology agrees canonically with ordinary derived cohomology.
Both arrows used here are the canonical truncation unit/counit, followed by the prescribed
cohomology shift comparison. Source: BBD 1.3.6; Stacks 015J
(blueprint: lem-zl-finite-truncation-spectral-sequence). -/
def finiteTruncationDerivedCohomologyIso
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (V : DerivedCategory B) (n : ℤ) :
    ((DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).obj
      ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).obj V)) ≅
        (DerivedCategory.homologyFunctor B n).obj V := by
  let X := (shiftFunctor (DerivedCategory B) n).obj V
  let hπ := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app
    ((DerivedCategory.TStructure.t.truncLT 1).obj X) 0 0 (by omega)
  let hι := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app X 1 0 (by omega)
  exact (asIso ((DerivedCategory.homologyFunctor B 0).map
      ((DerivedCategory.TStructure.t.truncGEπ 0).app
        ((DerivedCategory.TStructure.t.truncLT 1).obj X)))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor B 0).map
      ((DerivedCategory.TStructure.t.truncLTι 1).app X)) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso n 0 n (by omega)).app V

private theorem rightDerived_preserves_nonnegative
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{vA} A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (X : DerivedCategory A)
    (hX : DerivedCategory.TStructure.t.IsGE X 0) :
    DerivedCategory.TStructure.t.IsGE (F.rightDerivedFunctor.obj X) 0 := by
  let K : DerivedCategory.Plus A := ⟨X, ⟨0, hX⟩⟩
  have : K.IsGE 0 := (DerivedCategory.Plus.isGE_ι_obj_iff K 0).mp hX
  apply (DerivedCategory.isGE_iff _ 0).mpr
  intro n hn
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K 0 hn).of_iso
    ((DerivedCategory.homologyFunctor B n).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app K)).symm

private theorem derivedHeart_exact
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (S : ShortComplex DerivedCategory.TStructure.t.heart.FullSubcategory)
    (hS : S.ShortExact) :
    (S.map (DerivedCategory.TStructure.t.heart.ι ⋙
      DerivedCategory.homologyFunctor B 0)).ShortExact := by
  let t := DerivedCategory.TStructure.t (C := B)
  let := t.hasHeartFullSubcategory
  obtain ⟨δ, hδ⟩ := (t.shortExact_iff_exists_distTriang S).mp hS
  let U := Triangle.mk (t.heart.ι.map S.f) (t.heart.ι.map S.g) δ
  have : t.IsGE U.obj₃ 0 := by
    change t.IsGE S.X₃.obj 0
    exact ((t.mem_heart_iff _).mp S.X₃.property).2
  have : t.IsLE U.obj₁ 0 := by
    change t.IsLE S.X₁.obj 0
    exact ((t.mem_heart_iff _).mp S.X₁.property).1
  have hm : Mono ((DerivedCategory.homologyFunctor B 0).map U.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff U hδ (-1) 0 (by omega)).mpr
      ((DerivedCategory.isZero_of_isGE U.obj₃ 0 (-1) (by omega)).eq_zero_of_src _)
  have he : Epi ((DerivedCategory.homologyFunctor B 0).map U.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff U hδ 0 1 (by omega)).mpr
      ((DerivedCategory.isZero_of_isLE U.obj₁ 0 1 (by omega)).eq_zero_of_tgt _)
  exact ShortComplex.ShortExact.mk' (DerivedCategory.HomologySequence.exact₂ U hδ 0) hm he

private instance derivedHeart_limits
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] :
    PreservesFiniteLimits
      (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) := by
  have h : PreservesFiniteLimits
        (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) ∧
      PreservesFiniteColimits
        (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) :=
    (((DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).exact_tfae).out
      0 3).mp derivedHeart_exact
  exact h.1

private instance derivedHeart_colimits
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] :
    PreservesFiniteColimits
      (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) := by
  have h : PreservesFiniteLimits
        (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) ∧
      PreservesFiniteColimits
        (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) :=
    (((DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).exact_tfae).out
      0 3).mp derivedHeart_exact
  exact h.2

private def derivedBaseCohomologyIso
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (V : DerivedCategory B) :
    (DerivedCategory.homologyFunctor B 0).obj
        ((DerivedCategory.TStructure.t.truncGELT 0 1).obj V) ≅
      (DerivedCategory.homologyFunctor B 0).obj V :=
  have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app
    ((DerivedCategory.TStructure.t.truncLT 1).obj V) 0 0 (by omega)
  have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app V 1 0 (by omega)
  (asIso ((DerivedCategory.homologyFunctor B 0).map
    ((DerivedCategory.TStructure.t.truncGEπ 0).app
      ((DerivedCategory.TStructure.t.truncLT 1).obj V)))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor B 0).map
      ((DerivedCategory.TStructure.t.truncLTι 1).app V))

private theorem derivedBaseCohomologyIso_natural
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {U V : DerivedCategory B} (f : U ⟶ V) :
    (DerivedCategory.homologyFunctor B 0).map
        ((DerivedCategory.TStructure.t.truncGELT 0 1).map f) ≫
        (derivedBaseCohomologyIso V).hom =
      (derivedBaseCohomologyIso U).hom ≫ (DerivedCategory.homologyFunctor B 0).map f := by
  let t := DerivedCategory.TStructure.t (C := B)
  let H := DerivedCategory.homologyFunctor B 0
  have hi (W : DerivedCategory B) :
      IsIso (H.map ((t.truncGEπ 0).app ((t.truncLT 1).obj W))) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ 0 0 (by omega)
  have hp : H.map ((t.truncGEπ 0).app ((t.truncLT 1).obj U)) ≫
      H.map ((t.truncGELT 0 1).map f) = H.map ((t.truncLT 1).map f) ≫
        H.map ((t.truncGEπ 0).app ((t.truncLT 1).obj V)) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map ((t.truncGEπ 0).naturality ((t.truncLT 1).map f)).symm
  have hx := inverse_square _ _ _ _ hp
  dsimp only [derivedBaseCohomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  erw [← Category.assoc, ← hx, Category.assoc, ← H.map_comp,
    (t.truncLTι 1).naturality, H.map_comp, Category.assoc]
  try rfl

private theorem derivedCohomologyIso_hom
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (V : DerivedCategory B) (n : ℤ) :
    (finiteTruncationDerivedCohomologyIso V n).hom =
      (derivedBaseCohomologyIso ((shiftFunctor (DerivedCategory B) n).obj V)).hom ≫
        ((DerivedCategory.homologyFunctor B 0).shiftIso n 0 n (by omega)).hom.app V := by
  simp only [finiteTruncationDerivedCohomologyIso, derivedBaseCohomologyIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  try rfl

private theorem derivedCohomologyIso_natural
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {U V : DerivedCategory B} (f : U ⟶ V) (n : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map f) ≫
        (finiteTruncationDerivedCohomologyIso V n).hom =
      (finiteTruncationDerivedCohomologyIso U n).hom ≫
        (DerivedCategory.homologyFunctor B n).map f := by
  let H := DerivedCategory.homologyFunctor B 0
  let t := DerivedCategory.TStructure.t (C := B)
  rw [derivedCohomologyIso_hom, derivedCohomologyIso_hom]
  change H.map ((t.truncGELT 0 1).map ((shiftFunctor (DerivedCategory B) n).map f)) ≫
      ((derivedBaseCohomologyIso ((shiftFunctor (DerivedCategory B) n).obj V)).hom ≫
        (H.shiftIso n 0 n (by omega)).hom.app V) =
    ((derivedBaseCohomologyIso ((shiftFunctor (DerivedCategory B) n).obj U)).hom ≫
        (H.shiftIso n 0 n (by omega)).hom.app U) ≫ (DerivedCategory.homologyFunctor B n).map f
  erw [← Category.assoc, derivedBaseCohomologyIso_natural, Category.assoc,
    (H.shiftIso n 0 n (by omega)).hom.naturality, Category.assoc]
  simp only [derivedBaseCohomologyIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Category.assoc]
  try rfl

private theorem derivedCohomologyIso_connecting
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {U V : DerivedCategory B} (δ : U ⟶ (shiftFunctor (DerivedCategory B) (1 : ℤ)).obj V)
    (n n' : ℤ) (h : 1 + n = n') :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map δ ≫
          DerivedCategory.TStructure.t.homology₀.map
            ((shiftFunctorAdd' (DerivedCategory B) 1 n n' h).inv.app V)) ≫
        (finiteTruncationDerivedCohomologyIso V n').hom =
      (finiteTruncationDerivedCohomologyIso U n).hom ≫
        (DerivedCategory.homologyFunctor B n).map δ ≫
        ((DerivedCategory.homologyFunctor B 0).shiftIso 1 n n' h).hom.app V := by
  let H := DerivedCategory.homologyFunctor B 0
  let t := DerivedCategory.TStructure.t (C := B)
  simp only [Functor.map_comp]
  rw [derivedCohomologyIso_hom, derivedCohomologyIso_hom]
  change (H.map ((t.truncGELT 0 1).map ((shiftFunctor (DerivedCategory B) n).map δ)) ≫
      H.map ((t.truncGELT 0 1).map ((shiftFunctorAdd' (DerivedCategory B) 1 n n' h).inv.app V))) ≫
      ((derivedBaseCohomologyIso ((shiftFunctor (DerivedCategory B) n').obj V)).hom ≫
        (H.shiftIso n' 0 n' (by omega)).hom.app V) =
    ((derivedBaseCohomologyIso ((shiftFunctor (DerivedCategory B) n).obj U)).hom ≫
        (H.shiftIso n 0 n (by omega)).hom.app U) ≫
        (DerivedCategory.homologyFunctor B n).map δ ≫ (H.shiftIso 1 n n' h).hom.app V
  have h₁ := derivedBaseCohomologyIso_natural
    ((shiftFunctorAdd' (DerivedCategory B) 1 n n' h).inv.app V)
  have h₂ := derivedBaseCohomologyIso_natural
    ((shiftFunctor (DerivedCategory B) n).map δ)
  have hc := H.shiftIso_hom_app_comp n 1 n' h 0 n n' (by omega) h V
  have hn := (H.shiftIso n 0 n (by omega)).hom.naturality δ
  dsimp only [H] at hc hn
  simp only [DerivedCategory.shift_homologyFunctor] at hc hn
  erw [Category.assoc, reassoc_of% h₁,
    ← hc, reassoc_of% h₂, reassoc_of% hn]
  simp only [Category.assoc]
  try rfl

private theorem derived_truncation_lift_isIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    IsIso (DerivedCategory.TStructure.t.liftTruncLT
      (DerivedCategory.Q.map (K.obj.ιTruncLE b)) b (b + 1) rfl) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let m := t.liftTruncLT (DerivedCategory.Q.map (K.obj.ιTruncLE b)) b (b + 1) rfl
  have hc : m ≫ (t.truncLTι (b + 1)).app (DerivedCategory.Q.obj K.obj) =
      DerivedCategory.Q.map (K.obj.ιTruncLE b) := t.liftTruncLT_ι _ _ _ _
  have : t.IsLE ((t.truncLT (b + 1)).obj (DerivedCategory.Q.obj K.obj)) b :=
    t.isLE_truncLT_obj _ _ _ (by omega)
  apply (DerivedCategory.isIso_iff A m).mpr
  intro n
  by_cases hn : n ≤ b
  · have : IsIso ((DerivedCategory.homologyFunctor A n).map
        ((t.truncLTι (b + 1)).app (DerivedCategory.Q.obj K.obj))) :=
      DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
    have := K.obj.quasiIsoAt_ιTruncLE b n hn
    have hi : IsIso ((DerivedCategory.homologyFunctor A n).map
        (DerivedCategory.Q.map (K.obj.ιTruncLE b))) :=
      (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A n)
        (K.obj.ιTruncLE b)).mpr (by
        change IsIso (HomologicalComplex.homologyMap (K.obj.ιTruncLE b) n)
        exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
          (K.obj.quasiIsoAt_ιTruncLE b n hn))
    have hcomp : IsIso ((DerivedCategory.homologyFunctor A n).map m ≫
        (DerivedCategory.homologyFunctor A n).map
          ((t.truncLTι (b + 1)).app (DerivedCategory.Q.obj K.obj))) := by
      rw [← Functor.map_comp, hc]
      exact hi
    exact (isIso_comp_right_iff _ _).mp hcomp
  · exact (DerivedCategory.isZero_of_isLE _ b n (by omega)).isIso
      (DerivedCategory.isZero_of_isLE _ b n (by omega)) _

private def derivedTruncationIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.truncLT (b + 1)).obj (DerivedCategory.Q.obj K.obj) ≅
      DerivedCategory.Q.obj (TruncationCouple.truncation K b).obj :=
  have := derived_truncation_lift_isIso K b
  (asIso (DerivedCategory.TStructure.t.liftTruncLT
    (DerivedCategory.Q.map (K.obj.ιTruncLE b)) b (b + 1) rfl)).symm

private theorem derivedTruncationIso_counit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (derivedTruncationIso K b).hom ≫ DerivedCategory.Q.map (K.obj.ιTruncLE b) =
      (DerivedCategory.TStructure.t.truncLTι (b + 1)).app
        (DerivedCategory.Q.obj K.obj) := by
  have := derived_truncation_lift_isIso K b
  let m := DerivedCategory.TStructure.t.liftTruncLT
    (DerivedCategory.Q.map (K.obj.ιTruncLE b)) b (b + 1) rfl
  have hc : m ≫ (DerivedCategory.TStructure.t.truncLTι (b + 1)).app
      (DerivedCategory.Q.obj K.obj) = DerivedCategory.Q.map (K.obj.ιTruncLE b) :=
    DerivedCategory.TStructure.t.liftTruncLT_ι _ _ _ _
  change inv m ≫ DerivedCategory.Q.map (K.obj.ιTruncLE b) = _
  calc
    _ = inv m ≫ (m ≫ (DerivedCategory.TStructure.t.truncLTι (b + 1)).app
        (DerivedCategory.Q.obj K.obj)) := congrArg (fun f ↦ inv m ≫ f) hc.symm
    _ = _ := by rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

private def derivedLowerTruncationIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.truncLT b).obj (DerivedCategory.Q.obj K.obj) ≅
      DerivedCategory.Q.obj (TruncationCouple.truncation K (b - 1)).obj :=
  eqToIso (congrArg (fun c : ℤ ↦ (DerivedCategory.TStructure.t.truncLT c).obj
    (DerivedCategory.Q.obj K.obj)) (by omega : b = b - 1 + 1)) ≪≫
    derivedTruncationIso K (b - 1)

private theorem derivedLowerTruncationIso_counit
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (derivedLowerTruncationIso K b).hom ≫ DerivedCategory.Q.map (K.obj.ιTruncLE (b - 1)) =
      (DerivedCategory.TStructure.t.truncLTι b).app (DerivedCategory.Q.obj K.obj) := by
  dsimp only [derivedLowerTruncationIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, derivedTruncationIso_counit]
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff]
  erw [show b - 1 + 1 = b by omega]

private theorem derivedTruncationIso_transition
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.natTransTruncLTOfLE b (b + 1) (by omega)).app
        (DerivedCategory.Q.obj K.obj) ≫ (derivedTruncationIso K b).hom =
      (derivedLowerTruncationIso K b).hom ≫
        DerivedCategory.Q.map (TruncationCouple.transition K b) := by
  let t := DerivedCategory.TStructure.t (C := A)
  have : t.IsLE ((t.truncLT b).obj (DerivedCategory.Q.obj K.obj)) b :=
    t.isLE_truncLT_obj _ _ _ (by omega)
  apply (cancel_mono (derivedTruncationIso K b).inv).mp
  have : t.IsLE ((t.truncLT b).obj (DerivedCategory.Q.obj K.obj)) (b + 1 - 1) :=
    t.isLE_truncLT_obj _ _ _ (by omega)
  apply t.to_truncLT_obj_ext
  have hi : (derivedTruncationIso K b).inv ≫
      (t.truncLTι (b + 1)).app (DerivedCategory.Q.obj K.obj) =
        DerivedCategory.Q.map (K.obj.ιTruncLE b) := by
    rw [← derivedTruncationIso_counit K b, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc, t.natTransTruncLTOfLE_ι_app, hi,
    ← DerivedCategory.Q.map_comp, TruncationCouple.transition_comp_ιTruncLE,
    derivedLowerTruncationIso_counit]

private theorem derivedLowerTruncationIso_succ
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (derivedLowerTruncationIso K (b + 1)).hom =
      (derivedTruncationIso K b).hom ≫ DerivedCategory.Q.map
        (eqToHom (congrArg (fun c : ℤ ↦ K.obj.truncLE c)
          (show b = (b + 1) - 1 by omega))) := by
  dsimp only [derivedLowerTruncationIso, Iso.trans_hom, eqToIso.hom]
  erw [eqToHom_map]
  exact (eqToHom_naturality (fun c : ℤ ↦ (derivedTruncationIso K c).hom)
    (show b = (b + 1) - 1 by omega)).symm

private instance derived_cohomologyComplex_isGE
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    DerivedCategory.TStructure.t.IsGE
      (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K b).obj) b := by
  change (DerivedCategory.Q.obj
    ((CochainComplex.singleFunctor A b).obj (K.obj.homology b))).IsGE b
  infer_instance

private def derivedLayerMap
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj (DerivedCategory.Q.obj K.obj) ⟶
      DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K b).obj :=
  DerivedCategory.TStructure.t.descTruncGE
    ((derivedTruncationIso K b).hom ≫ DerivedCategory.Q.map (TruncationCouple.projection K b)) b

private theorem derivedLayerMap_projection
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ b).app
        ((DerivedCategory.TStructure.t.truncLT (b + 1)).obj (DerivedCategory.Q.obj K.obj)) ≫
        derivedLayerMap K b = (derivedTruncationIso K b).hom ≫
          DerivedCategory.Q.map (TruncationCouple.projection K b) :=
  DerivedCategory.TStructure.t.π_descTruncGE _ _

private theorem derivedLayerMap_connecting
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.truncGELTδLT b (b + 1)).app
        (DerivedCategory.Q.obj K.obj) ≫
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (derivedLowerTruncationIso K b).hom =
      derivedLayerMap K b ≫ (TruncationCouple.triangle K b).mor₃ := by
  let t := DerivedCategory.TStructure.t (C := A)
  have hU := t.triangleLTLTGELT_distinguished b (b + 1) (by omega)
    (DerivedCategory.Q.obj K.obj)
  have hV : TruncationCouple.triangle K b ∈ distTriang (DerivedCategory A) :=
    (TruncationCouple.existsUnique_boundary K b).choose_spec.1
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
    ((t.triangleLTLTGELT b (b + 1) (by omega)).obj (DerivedCategory.Q.obj K.obj))
    (TruncationCouple.triangle K b) hU hV
    (derivedLowerTruncationIso K b).hom (derivedTruncationIso K b).hom
    (derivedTruncationIso_transition K b)
  have hc : c = derivedLayerMap K b := by
    have : t.IsGE (TruncationCouple.triangle K b).obj₃ b := by
      change t.IsGE (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K b).obj) b
      infer_instance
    apply t.from_truncGE_obj_ext
    exact hc₂.trans (derivedLayerMap_projection K b).symm
  dsimp only [TStructure.triangleLTLTGELT, Triangle.functorMk, Triangle.mk] at hc₃
  simpa only [hc] using hc₃

private def derivedTruncationTriangleMap
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.triangleLTLTGELT b (b + 1) (by omega)).obj
        (DerivedCategory.Q.obj K.obj) ⟶ TruncationCouple.triangle K b where
  hom₁ := (derivedLowerTruncationIso K b).hom
  hom₂ := (derivedTruncationIso K b).hom
  hom₃ := derivedLayerMap K b
  comm₁ := derivedTruncationIso_transition K b
  comm₂ := derivedLayerMap_projection K b
  comm₃ := derivedLayerMap_connecting K b

private theorem derivedLayerMap_isIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) : IsIso (derivedLayerMap K b) :=
  isIso₃_of_isIso₁₂ (derivedTruncationTriangleMap K b)
    (DerivedCategory.TStructure.t.triangleLTLTGELT_distinguished b (b + 1)
      (by omega) (DerivedCategory.Q.obj K.obj))
    (TruncationCouple.existsUnique_boundary K b).choose_spec.1
    (by change IsIso (derivedLowerTruncationIso K b).hom; infer_instance)
    (by change IsIso (derivedTruncationIso K b).hom; infer_instance)

private def derivedLayerIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (K : CochainComplex.Plus A) (b : ℤ) :
    (DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj (DerivedCategory.Q.obj K.obj) ≅
      DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K b).obj :=
  have := derivedLayerMap_isIso K b
  asIso (derivedLayerMap K b)

private theorem derivedApplied_delta
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{vA} A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (b n n' : ℤ) (h : n + 1 = n') :
    (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (derivedLayerMap K b)) ≫
        DerivedCategory.HomologySequence.δ (TruncationCouple.derivedTriangle F K b) n n' h =
      DerivedCategory.HomologySequence.δ
        (F.rightDerivedFunctor.mapTriangle.obj
          ((DerivedCategory.TStructure.t.triangleLTLTGELT b (b + 1) (by omega)).obj
            (DerivedCategory.Q.obj K.obj))) n n' h ≫
        (DerivedCategory.homologyFunctor B n').map
          (F.rightDerivedFunctor.map (derivedLowerTruncationIso K b).hom) := by
  exact (DerivedCategory.homologyFunctor B 0).homologySequenceδ_naturality _ _
    (F.rightDerivedFunctor.mapTriangle.map (derivedTruncationTriangleMap K b)) n n' h

section DerivedComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [IsGrothendieckAbelian.{vA} A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  (K : CochainComplex.Plus A)

private def derivedDComparison (n b : ℤ) :
    ((DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).obj
      ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).obj
        (F.rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLT (b + 1)).obj
            (DerivedCategory.Q.obj K.obj))))) ≅
      F.rightDerivedCohomologyWithResolution (TruncationCouple.truncation K b)
        (CochainComplex.grothendieckKInjectiveResolutionChoice
          (TruncationCouple.truncation K b).obj) n :=
  finiteTruncationDerivedCohomologyIso _ n ≪≫
    (DerivedCategory.homologyFunctor B n).mapIso
      (F.rightDerivedFunctor.mapIso (derivedTruncationIso K b)) ≪≫
    TruncationCouple.bridgeIso F (TruncationCouple.truncation K b) n

private def derivedEComparison (n b : ℤ) :
    ((DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).obj
      ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).obj
        (F.rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj
            (DerivedCategory.Q.obj K.obj))))) ≅
      F.rightDerivedCohomologyWithResolution (TruncationCouple.cohomologyComplex K b)
        (CochainComplex.grothendieckKInjectiveResolutionChoice
          (TruncationCouple.cohomologyComplex K b).obj) n :=
  finiteTruncationDerivedCohomologyIso _ n ≪≫
    (DerivedCategory.homologyFunctor B n).mapIso
      (F.rightDerivedFunctor.mapIso (derivedLayerIso K b)) ≪≫
    TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K b) n

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derived_comparison_square
    {U V U' V' : DerivedCategory B} (f : U ⟶ V) (f' : U' ⟶ V')
    (κU : U ⟶ U') (κV : V ⟶ V') (h : f ≫ κV = κU ≫ f') (n : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map f) ≫
        (finiteTruncationDerivedCohomologyIso V n).hom ≫
        (DerivedCategory.homologyFunctor B n).map κV =
      (finiteTruncationDerivedCohomologyIso U n).hom ≫
        (DerivedCategory.homologyFunctor B n).map κU ≫
        (DerivedCategory.homologyFunctor B n).map f' := by
  erw [← Category.assoc, derivedCohomologyIso_natural, Category.assoc,
    ← Functor.map_comp, h, Functor.map_comp]

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derivedDComparison_inclusion (n b : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map
          (F.rightDerivedFunctor.map
            ((DerivedCategory.TStructure.t.natTransTruncLTOfLE (b + 1) (b + 1 + 1)
              (by omega)).app (DerivedCategory.Q.obj K.obj)))) ≫
        (derivedDComparison F K n (b + 1)).hom =
      (derivedDComparison F K n b).hom ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K b) n).inv ≫
        (DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map
            (eqToHom (congrArg (fun c : ℤ ↦ K.obj.truncLE c)
              (show b = (b + 1) - 1 by omega)) ≫
                TruncationCouple.transition K (b + 1)))) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b + 1)) n).hom := by
  have hc := derivedTruncationIso_transition K (b + 1)
  rw [derivedLowerTruncationIso_succ] at hc
  have hd := congrArg F.rightDerivedFunctor.map hc
  simp only [Functor.map_comp, Category.assoc] at hd
  simpa only [derivedDComparison, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp] using
    congrArg (fun f ↦ f ≫ (TruncationCouple.bridgeIso F
      (TruncationCouple.truncation K (b + 1)) n).hom)
      (derived_comparison_square _ _ _ _ hd n)

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derivedEComparison_projection (n b : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map
          (F.rightDerivedFunctor.map ((DerivedCategory.TStructure.t.truncGEπ b).app
            ((DerivedCategory.TStructure.t.truncLT (b + 1)).obj
              (DerivedCategory.Q.obj K.obj))))) ≫
        (derivedEComparison F K n b).hom =
      (derivedDComparison F K n b).hom ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K b) n).inv ≫
        (DerivedCategory.homologyFunctor B n).map (TruncationCouple.derivedTriangle F K b).mor₂ ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K b) n).hom := by
  have hd := congrArg F.rightDerivedFunctor.map (derivedLayerMap_projection K b)
  simp only [Functor.map_comp] at hd
  simpa only [derivedDComparison, derivedEComparison, derivedLayerIso, asIso_hom,
    TruncationCouple.derivedTriangle, TruncationCouple.triangle, Functor.mapTriangle,
    Triangle.mk, Functor.id_obj, Functor.comp_obj, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp] using
    congrArg (fun f ↦ f ≫ (TruncationCouple.bridgeIso F
      (TruncationCouple.cohomologyComplex K b) n).hom)
      (derived_comparison_square _ _ _ _ hd n)

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derivedComparison_alpha (a b : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        (rawAlpha DerivedCategory.TStructure.t DerivedCategory.TStructure.t
          F.rightDerivedFunctor (DerivedCategory.Q.obj K.obj) a b) ≫
        (derivedDComparison F K ((a - 1) + (b + 1)) (b + 1)).hom =
      (derivedDComparison F K (a + b) b).hom ≫ TruncationCouple.alpha F K a b := by
  dsimp only [rawAlpha, TruncationCouple.alpha]
  erw [Functor.map_comp, Category.assoc, eqToHom_map,
    ← eqToHom_naturality (fun n : ℤ ↦ (derivedDComparison F K n (b + 1)).hom)
      (show a + b = (a - 1) + (b + 1) by omega), ← Category.assoc,
    derivedDComparison_inclusion, Category.assoc]
  simp only [derivedDComparison, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  try rfl

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derivedComparison_g (a b : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        (rawG DerivedCategory.TStructure.t DerivedCategory.TStructure.t
          F.rightDerivedFunctor (DerivedCategory.Q.obj K.obj) a b) ≫
        (derivedEComparison F K (a + b) b).hom =
      (derivedDComparison F K (a + b) b).hom ≫ TruncationCouple.g F K a b :=
  derivedEComparison_projection F K (a + b) b

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derivedDComparison_lower (n b : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        (eqToHom (congrArg (fun c : ℤ ↦
          (shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).obj
            (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncLT c).obj
              (DerivedCategory.Q.obj K.obj)))) (show b = b - 1 + 1 by omega))) ≫
        (derivedDComparison F K n (b - 1)).hom =
      (finiteTruncationDerivedCohomologyIso
        (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncLT b).obj
          (DerivedCategory.Q.obj K.obj))) n).hom ≫
        (DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctor.map (derivedLowerTruncationIso K b).hom) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b - 1)) n).hom := by
  let c := eqToHom (congrArg (fun m : ℤ ↦
    (DerivedCategory.TStructure.t.truncLT m).obj (DerivedCategory.Q.obj K.obj))
      (show b = b - 1 + 1 by omega))
  let Φ := DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0
  have hm : Φ.map (eqToHom (congrArg (fun m : ℤ ↦
      (shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncLT m).obj
          (DerivedCategory.Q.obj K.obj)))) (show b = b - 1 + 1 by omega))) =
      Φ.map ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map
        (F.rightDerivedFunctor.map c)) := by
    simp only [c, eqToHom_map]
  rw [hm]
  have h := derivedCohomologyIso_natural (F.rightDerivedFunctor.map c) n
  dsimp only [derivedDComparison, Iso.trans_hom, Functor.mapIso_hom]
  erw [← Category.assoc, h]
  have hc : (DerivedCategory.homologyFunctor B n).map (F.rightDerivedFunctor.map c) ≫
      (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (derivedTruncationIso K (b - 1)).hom) =
      (DerivedCategory.homologyFunctor B n).map
        (F.rightDerivedFunctor.map (derivedLowerTruncationIso K b).hom) := by
    rw [← Functor.map_comp, ← F.rightDerivedFunctor.map_comp]
    rfl
  simpa only [Category.assoc] using congrArg (fun f ↦
    (finiteTruncationDerivedCohomologyIso
      (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncLT b).obj
        (DerivedCategory.Q.obj K.obj))) n).hom ≫ f ≫
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b - 1)) n).hom) hc

private theorem derivedComparison_boundary (n n' b : ℤ) (h : 1 + n = n') :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((shiftFunctor (DerivedCategory B) n ⋙ DerivedCategory.TStructure.t.homology₀).map
          (F.rightDerivedFunctor.map ((DerivedCategory.TStructure.t.truncGELTδLT b (b + 1)).app
            (DerivedCategory.Q.obj K.obj)) ≫
              (F.rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app _) ≫
          DerivedCategory.TStructure.t.homology₀.map
            ((shiftFunctorAdd' (DerivedCategory B) 1 n n' h).inv.app _)) ≫
        (finiteTruncationDerivedCohomologyIso
          (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncLT b).obj
            (DerivedCategory.Q.obj K.obj))) n').hom ≫
        (DerivedCategory.homologyFunctor B n').map
          (F.rightDerivedFunctor.map (derivedLowerTruncationIso K b).hom) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b - 1)) n').hom =
      (finiteTruncationDerivedCohomologyIso
        (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj
          (DerivedCategory.Q.obj K.obj))) n).hom ≫
        (DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctor.map (derivedLayerMap K b)) ≫
        DerivedCategory.HomologySequence.δ (TruncationCouple.derivedTriangle F K b)
          n n' (by omega) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b - 1)) n').hom := by
  erw [← Category.assoc _ _
    ((DerivedCategory.homologyFunctor B n').map
      (F.rightDerivedFunctor.map (derivedLowerTruncationIso K b).hom) ≫ _),
    derivedCohomologyIso_connecting, Category.assoc]
  have hh := derivedApplied_delta F K b n n' (by omega)
  dsimp only [DerivedCategory.HomologySequence.δ, Functor.shiftMap,
    Functor.mapTriangle, TStructure.triangleLTLTGELT, Triangle.functorMk, Triangle.mk] at hh
  simp only [DerivedCategory.shift_homologyFunctor] at hh
  simpa only [Category.assoc, DerivedCategory.HomologySequence.δ, Functor.shiftMap,
    DerivedCategory.shift_homologyFunctor] using congrArg (fun f ↦
    (finiteTruncationDerivedCohomologyIso
      (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj
        (DerivedCategory.Q.obj K.obj))) n).hom ≫ f ≫
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b - 1)) n').hom) hh.symm

private theorem derivedComparison_f (a b : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        (finiteTruncationConnecting DerivedCategory.TStructure.t DerivedCategory.TStructure.t
          F.rightDerivedFunctor (DerivedCategory.Q.obj K.obj) a b) ≫
        (derivedDComparison F K ((a + 2) + (b - 1)) (b - 1)).hom =
      (derivedEComparison F K (a + b) b).hom ≫ TruncationCouple.f F K a b := by
  let t := DerivedCategory.TStructure.t (C := A)
  let s := DerivedCategory.TStructure.t (C := B)
  have hc := connecting_eq t s F.rightDerivedFunctor (DerivedCategory.Q.obj K.obj) a b
  rw [hc]
  erw [Functor.map_comp, Category.assoc]
  erw [derivedDComparison_lower F K ((a + 2) + (b - 1)) b]
  erw [derivedComparison_boundary F K (a + b) ((a + 2) + (b - 1)) b (by omega)]
  dsimp only [derivedEComparison, derivedLayerIso, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, TruncationCouple.f]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply eq_of_heq
  simp only [← Category.assoc, heq_comp_eqToHom_iff]
  have hh (m : ℤ) (hm : a + b + 1 = m) :
      HEq
        ((finiteTruncationDerivedCohomologyIso
          (F.rightDerivedFunctor.obj ((t.truncGELT b (b + 1)).obj
            (DerivedCategory.Q.obj K.obj))) (a + b)).hom ≫
          (DerivedCategory.homologyFunctor B (a + b)).map
            (F.rightDerivedFunctor.map (derivedLayerMap K b)) ≫
          DerivedCategory.HomologySequence.δ (TruncationCouple.derivedTriangle F K b)
            (a + b) m hm ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (b - 1)) m).hom)
        ((finiteTruncationDerivedCohomologyIso
          (F.rightDerivedFunctor.obj ((t.truncGELT b (b + 1)).obj
            (DerivedCategory.Q.obj K.obj))) (a + b)).hom ≫
          (DerivedCategory.homologyFunctor B (a + b)).map
            (F.rightDerivedFunctor.map (derivedLayerMap K b)) ≫
          DerivedCategory.HomologySequence.δ (TruncationCouple.derivedTriangle F K b)
            (a + b) (a + b + 1) ≫
          (TruncationCouple.bridgeIso F
            (TruncationCouple.truncation K (b - 1)) (a + b + 1)).hom) := by
    subst m
    try rfl
  simpa only [Category.assoc] using hh ((a + 2) + (b - 1)) (by omega)

omit [IsGrothendieckAbelian.{vB} B] in
private theorem derivedComparison_abutment (n p : ℤ) :
    (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
        ((canonicalCouple DerivedCategory.TStructure.t DerivedCategory.TStructure.t
          F.rightDerivedFunctor (DerivedCategory.Q.obj K.obj)).toAbutment n p) ≫
        (finiteTruncationDerivedCohomologyIso
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)) n).hom =
      (derivedDComparison F K (p + (n - p)) (n - p)).hom ≫
        eqToHom (congrArg (fun m : ℤ ↦ F.rightDerivedCohomologyWithResolution
          (TruncationCouple.truncation K (n - p))
          (CochainComplex.grothendieckKInjectiveResolutionChoice
            (TruncationCouple.truncation K (n - p)).obj) m)
          (show p + (n - p) = n by omega)) ≫
        (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (n - p)) n).inv ≫
        (DerivedCategory.homologyFunctor B n).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE (n - p)))) := by
  let Φ := DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0
  dsimp only [FiniteTruncationCouple.toAbutment, canonicalCouple]
  simp only [Iso.refl_hom, Category.id_comp, Functor.map_comp, Category.assoc]
  erw [eqToHom_naturality_assoc (fun m : ℤ ↦
    (derivedDComparison F K m (n - p)).hom) (show p + (n - p) = n by omega),
    ← eqToHom_map Φ (congrArg (fun m : ℤ ↦
      (shiftFunctor (DerivedCategory B) m ⋙ DerivedCategory.TStructure.t.homology₀).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.TStructure.t.truncLT (n - p + 1)).obj
          (DerivedCategory.Q.obj K.obj)))) (show p + (n - p) = n by omega))]
  try simp only [Category.assoc]
  congr 1
  dsimp only [derivedDComparison, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [derivedCohomologyIso_natural,
    ← (DerivedCategory.homologyFunctor B n).map_comp,
    ← F.rightDerivedFunctor.map_comp, derivedTruncationIso_counit]

end DerivedComparison

/-- Agreement with the recorded derived-functor construction on bounded objects.
The comparison is characterized by the truncation counit and the projection to the layer,
then by the published K-injective bridge. It applies to every exact couple with the raw
terms and maps used by `exists_truncationHypercohomology`, hence in particular its witness.
The last equation identifies the entire canonical abutment cocone, so its images and the
normalized graded comparisons agree as well. No global boundedness of D(A) or D(B) is assumed.
Source: BBD 1.3.3–1.3.7; Stacks 015J, 05TC; blueprint proof Step 8
(blueprint: lem-zl-finite-truncation-spectral-sequence).

Proof: Use the same canonical adjacent triangles as in Steps 1–4 of the preceding theorem
on the bounded object Q(K). The universal property of upper truncation gives κ, normalized
by its counit. The canonical comparison of the adjacent triangles gives λ, normalized by
their second arrows. Apply RF and cohomology, the canonical heart comparison and bridgeIso.
The resulting D and E isomorphisms commute with alpha, f and g since both triangles are
canonical, including their connecting arrows. The exact-functor/couple-morphism construction
of Steps 5–7 gives the iterated image, kernel and quotient comparisons in M. The counit
normalization gives the displayed equality of abutment cocones. Taking images gives the
same filtration as thm-sp-truncation-e2, and passing to the normalized quotients gives its
graded comparison. These arguments use ordinary canonical truncations in D(A).
-/
theorem finiteTruncationSpectralSequence_derived_agreement
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{vA} A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (l u : ℤ)
    (_hK : ∀ b : ℤ, b < l ∨ u < b → IsZero (K.obj.homology b)) :
    ∃ S : FiniteTruncationCouple DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t F.rightDerivedFunctor (DerivedCategory.Q.obj K.obj),
    Nonempty (FiniteTruncationAbutment S l u) ∧
    ∀ (X : BigradedExactCouple B 0)
      (hD : X.D = TruncationCouple.D F K) (hE : X.E = TruncationCouple.E F K),
      (∀ a b : ℤ, X.alpha a b = eqToHom (by rw [hD]) ≫
        TruncationCouple.alpha F K a b ≫ eqToHom (by rw [hD])) →
      (∀ a b : ℤ, X.f a b = eqToHom (by rw [hE]) ≫
        TruncationCouple.f F K a b ≫ eqToHom (by rw [hD])) →
      (∀ a b : ℤ, X.initialG a b = eqToHom (by rw [hD]) ≫
        TruncationCouple.g F K a b ≫ eqToHom (by rw [hE])) →
      ∃ κ : ∀ b : ℤ,
        (DerivedCategory.TStructure.t.truncLT (b + 1)).obj (DerivedCategory.Q.obj K.obj) ≅
          DerivedCategory.Q.obj (TruncationCouple.truncation K b).obj,
      ∃ layer : ∀ b : ℤ,
        (DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj
          (DerivedCategory.Q.obj K.obj) ≅
            DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K b).obj,
      (∀ b : ℤ, (κ b).hom ≫ DerivedCategory.Q.map (K.obj.ιTruncLE b) =
        (DerivedCategory.TStructure.t.truncLTι (b + 1)).app
          (DerivedCategory.Q.obj K.obj)) ∧
      (∀ b : ℤ,
        (DerivedCategory.TStructure.t.truncGEπ b).app
            ((DerivedCategory.TStructure.t.truncLT (b + 1)).obj
              (DerivedCategory.Q.obj K.obj)) ≫ (layer b).hom =
          (κ b).hom ≫ DerivedCategory.Q.map (TruncationCouple.projection K b)) ∧
      ∃ M : FiniteTruncationPageMap DerivedCategory.TStructure.t
        (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0) S.X X,
      (∀ (r : ℕ) (a b : ℤ), IsIso (M.dMap r a b) ∧ IsIso (M.eMap r a b)) ∧
      (∀ a b : ℤ,
        M.dMap 0 a b ≫ eqToHom (by change X.D a b = _; rw [hD]; rfl) =
          (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
              (S.dIso a b).hom ≫
            (finiteTruncationDerivedCohomologyIso
              (F.rightDerivedFunctor.obj
                ((DerivedCategory.TStructure.t.truncLT (b + 1)).obj
                  (DerivedCategory.Q.obj K.obj))) (a + b)).hom ≫
            (DerivedCategory.homologyFunctor B (a + b)).map
              (F.rightDerivedFunctor.map (κ b).hom) ≫
            (TruncationCouple.bridgeIso F (TruncationCouple.truncation K b) (a + b)).hom) ∧
      (∀ a b : ℤ,
        M.eMap 0 a b ≫ eqToHom (by change X.E a b = _; rw [hE]; rfl) =
          (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
              (S.eIso a b).hom ≫
            (finiteTruncationDerivedCohomologyIso
              (F.rightDerivedFunctor.obj
                ((DerivedCategory.TStructure.t.truncGELT b (b + 1)).obj
                  (DerivedCategory.Q.obj K.obj))) (a + b)).hom ≫
            (DerivedCategory.homologyFunctor B (a + b)).map
              (F.rightDerivedFunctor.map (layer b).hom) ≫
            (TruncationCouple.bridgeIso F
              (TruncationCouple.cohomologyComplex K b) (a + b)).hom) ∧
      (∀ n p : ℤ,
        (DerivedCategory.TStructure.t.heart.ι ⋙ DerivedCategory.homologyFunctor B 0).map
            (S.toAbutment n p) ≫
          (finiteTruncationDerivedCohomologyIso
            (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.obj)) n).hom =
          M.dMap 0 p (n - p) ≫ eqToHom (by
            change X.D p (n - p) = _
            rw [hD]
            unfold TruncationCouple.D
            congr 1
            omega) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (n - p)) n).inv ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE (n - p))))) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let s := DerivedCategory.TStructure.t (C := B)
  let T := F.rightDerivedFunctor
  let Z := DerivedCategory.Q.obj K.obj
  let Φ := s.heart.ι ⋙ DerivedCategory.homologyFunctor B 0
  have hGE : t.IsGE Z l := (DerivedCategory.isGE_iff Z l).mpr (fun n hn ↦
    (_hK n (Or.inl hn)).of_iso ((DerivedCategory.homologyFunctorFactors A n).app K.obj))
  have hLE : t.IsLE Z u := (DerivedCategory.isLE_iff Z u).mpr (fun n hn ↦
    (_hK n (Or.inr hn)).of_iso ((DerivedCategory.homologyFunctorFactors A n).app K.obj))
  refine ⟨canonicalCouple t s T Z,
    canonicalAbutment t s T (rightDerived_preserves_nonnegative F) Z l u, ?_⟩
  intro X hD hE hα hf hg
  have hDa (a b : ℤ) : TruncationCouple.D F K a b = X.D a b :=
    (congrFun (congrFun hD a) b).symm
  have hEa (a b : ℤ) : TruncationCouple.E F K a b = X.E a b :=
    (congrFun (congrFun hE a) b).symm
  let d (a b : ℤ) : Φ.obj ((rawCouple t s T Z).D a b) ⟶ X.D a b :=
    (derivedDComparison F K (a + b) b).hom ≫ eqToHom (hDa a b)
  let e (a b : ℤ) : Φ.obj ((rawCouple t s T Z).E a b) ⟶ X.E a b :=
    (derivedEComparison F K (a + b) b).hom ≫ eqToHom (hEa a b)
  have hd (a b : ℤ) : IsIso (d a b) := by dsimp only [d]; infer_instance
  have he (a b : ℤ) : IsIso (e a b) := by dsimp only [e]; infer_instance
  have ha (a b : ℤ) : Φ.map ((rawCouple t s T Z).alpha a b) ≫
      d (a - 1) (b + 1) = d a b ≫ X.alpha a b :=
    cast_square _ _ _ _ (derivedComparison_alpha F K a b)
      (hDa a b) (hDa (a - 1) (b + 1)) (X.alpha a b) (hα a b)
  have hff (a b : ℤ) : Φ.map ((rawCouple t s T Z).f a b) ≫
      d (a + 2) (b - 1) = e a b ≫ X.f a b :=
    cast_square _ _ _ _ (derivedComparison_f F K a b)
      (hEa a b) (hDa (a + 2) (b - 1)) (X.f a b) (hf a b)
  have hgg (a b : ℤ) : Φ.map ((rawCouple t s T Z).initialG a b) ≫ e a b =
      d a b ≫ X.initialG a b := by
    rw [raw_initialG]
    exact cast_square _ _ _ _ (derivedComparison_g F K a b)
      (hDa a b) (hEa a b) (X.initialG a b) (hg a b)
  obtain ⟨M, hM, hMIso⟩ := pages_of_initial_iso s Φ (rawCouple t s T Z) X
    d e hd he ha hff (initialG_square s Φ (rawCouple t s T Z) X d e hgg)
  refine ⟨derivedTruncationIso K, derivedLayerIso K,
    derivedTruncationIso_counit K, derivedLayerMap_projection K, M, hMIso, ?_, ?_, ?_⟩
  · intro a b
    rw [(hM a b).1]
    dsimp only [d, derivedDComparison, canonicalCouple, Iso.refl_hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Functor.map_id, Category.id_comp, Iso.trans_hom, Functor.mapIso_hom]
  · intro a b
    rw [(hM a b).2]
    dsimp only [e, derivedEComparison, canonicalCouple, Iso.refl_hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Functor.map_id, Category.id_comp, Iso.trans_hom, Functor.mapIso_hom]
  · intro n p
    rw [(hM p (n - p)).1]
    dsimp only [d]
    simp only [Category.assoc, eqToHom_trans_assoc]
    exact derivedComparison_abutment F K n p

end CategoryTheory.Triangulated
