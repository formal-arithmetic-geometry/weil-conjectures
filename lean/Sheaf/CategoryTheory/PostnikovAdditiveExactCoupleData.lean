/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.CategoryTheory.PostnikovFiniteCutoffAbutment
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
public import WeilConjectures.CategoryTheory.HalfPlaneConvergence
public import WeilConjectures.CategoryTheory.CanonicalFiltration

/-! # Witness interfaces for additive Postnikov exact couples

(blueprint: def-per-postnikov-additive-witness-data)

Source: Stacks Project, Homology, Tags 011Q, 011R, 011S and 0AMJ; Derived Categories,
Tag 08J5, with the project's E2 convention
(blueprint: lem-per-postnikov-additive-exact-couple).

The auxiliary structures bundle the witnesses of the existence theorem. They make no choices
of objects from an unproved existence statement. The index `r : ℕ` means page `r + 2`.
The parameter `ρ` translates the first index, including the unshifted case `ρ = 0`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w uB vB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The cohomology object in its original degree, functorially on the derived category.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-additive-exact-couple). -/
noncomputable def postnikovLayer (q : ℤ) : DerivedCategory A ⥤ DerivedCategory A :=
  homologyFunctor A q ⋙ singleFunctor A q

/-- The canonical single-degree truncation layer is the single-term cohomology object.
The comparison is normalized on H^q after the canonical truncation quotient. The
inclusion, quotient, boundary and distinguished triangle are reused from Mathlib and
`PostnikovFiniteCutoffAbutment`, rather than supplied as additional triangle choices.
Source: Stacks Tag 08J5 (blueprint: lem-per-postnikov-additive-exact-couple). -/
structure PostnikovTriangleData (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] where
  layerIso (q : ℤ) :
    (TStructure.t (C := A)).truncGELT q (q + 1) ≅ postnikovLayer q
  layer_normalized (q : ℤ) (L : DerivedCategory A) :
    (homologyFunctor A q).map
        ((((TStructure.t (C := A)).triangleLTLTGELT q (q + 1) (by omega)).obj L).mor₂ ≫
          (layerIso q).hom.app L) ≫
        (singleFunctorCompHomologyFunctorIso A q).hom.app
          ((homologyFunctor A q).obj L) =
      (homologyFunctor A q).map (((TStructure.t (C := A)).truncLEι q).app L)

/-- Exact couples on the canonical Postnikov objects, including all translations of the
first index. Comparison isomorphisms record the objects without identifying choices of
categorical kernels or truncations by equality. The three squares specify the actual maps.
Source: Stacks Tags 011Q, 08J5 (blueprint: lem-per-postnikov-additive-exact-couple). -/
structure PostnikovCoupleData (T : DerivedCategory A ⥤ B) where
  tower : PostnikovTriangleData A
  couple (ρ : ℤ) (L : DerivedCategory A) : BigradedExactCouple B 0
  dIso (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
    (couple ρ L).D p q ≅ (postnikovD T ρ p q).obj L
  eIso (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
    (couple ρ L).E p q ≅ (postnikovE T ρ p q).obj L
  alpha_eq (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
    (couple ρ L).alpha p q ≫ (dIso ρ L (p - 1) (q + 1)).hom =
      (dIso ρ L p q).hom ≫ postnikovAlpha T ρ p q L
  g_eq (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
    (couple ρ L).initialG p q ≫ (eIso ρ L p q).hom =
      (dIso ρ L p q).hom ≫ postnikovG T ρ p q L
  f_eq (ρ : ℤ) (L : DerivedCategory A) (p q : ℤ) :
    (couple ρ L).f p q ≫ (dIso ρ L (p + 2) (q - 1)).hom =
      (eIso ρ L p q).hom ≫ postnikovF T ρ p q L
  initialPageIso (ρ p q : ℤ) : postnikovE T ρ p q ≅
    homologyFunctor A q ⋙ singleFunctor A 0 ⋙
      shiftFunctor (DerivedCategory A) (p - ρ) ⋙ T
  initialPageIso_eq (ρ p q : ℤ) (L : DerivedCategory A) :
    (initialPageIso ρ p q).hom.app L =
      T.map (((tower.layerIso q).hom.app L)⟦p + q - ρ⟧') ≫
      T.map (((singleFunctors A).shiftIso (p + q - ρ) (ρ - p) q
        (by omega)).hom.app ((homologyFunctor A q).obj L) ≫
        (((singleFunctors A).shiftIso (p - ρ) (ρ - p) 0
          (by omega)).inv.app ((homologyFunctor A q).obj L)))

/-- Additive functors on every iterated D- and E-component. Their maps are couple morphisms,
and their successor maps are induced by the canonical image and homology constructions.
Source: Stacks Tags 011R, 011S (blueprint: lem-per-postnikov-additive-exact-couple). -/
structure PostnikovPageData {T : DerivedCategory A ⥤ B} (C : PostnikovCoupleData T) where
  D (ρ : ℤ) (r : ℕ) (p q : ℤ) : DerivedCategory A ⥤ B
  E (ρ : ℤ) (r : ℕ) (p q : ℤ) : DerivedCategory A ⥤ B
  additiveD (ρ : ℤ) (r : ℕ) (p q : ℤ) : (D ρ r p q).Additive
  additiveE (ρ : ℤ) (r : ℕ) (p q : ℤ) : (E ρ r p q).Additive
  dIso (ρ : ℤ) (r : ℕ) (p q : ℤ) (L : DerivedCategory A) :
    (D ρ r p q).obj L ≅ ((C.couple ρ L).pageCouple r).D p q
  eIso (ρ : ℤ) (r : ℕ) (p q : ℤ) (L : DerivedCategory A) :
    (E ρ r p q).obj L ≅ ((C.couple ρ L).pageCouple r).E p q
  map (ρ : ℤ) (r : ℕ) {L M : DerivedCategory A} (u : L ⟶ M) :
    BigradedExactCouple.CoupleMorphism
      ((C.couple ρ L).pageCouple r) ((C.couple ρ M).pageCouple r)
  mapD (ρ : ℤ) (r : ℕ) {L M : DerivedCategory A} (u : L ⟶ M) (p q : ℤ) :
    (map ρ r u).tD p q =
      (dIso ρ r p q L).inv ≫ (D ρ r p q).map u ≫ (dIso ρ r p q M).hom
  mapE (ρ : ℤ) (r : ℕ) {L M : DerivedCategory A} (u : L ⟶ M) (p q : ℤ) :
    (map ρ r u).tE p q =
      (eIso ρ r p q L).inv ≫ (E ρ r p q).map u ≫ (eIso ρ r p q M).hom
  initialD (ρ : ℤ) {L M : DerivedCategory A} (u : L ⟶ M) (p q : ℤ) :
    (map ρ 0 u).tD p q ≫ (C.dIso ρ M p q).hom =
      (C.dIso ρ L p q).hom ≫ (postnikovD T ρ p q).map u
  initialE (ρ : ℤ) {L M : DerivedCategory A} (u : L ⟶ M) (p q : ℤ) :
    (map ρ 0 u).tE p q ≫ (C.eIso ρ M p q).hom =
      (C.eIso ρ L p q).hom ≫ (postnikovE T ρ p q).map u
  image_square (ρ : ℤ) (r : ℕ) {L M : DerivedCategory A} (u : L ⟶ M) (p q : ℤ) :
    (map ρ (r + 1) u).tD p q ≫
        ((C.couple ρ M).pageCouple r).derivedDInclusion p q =
      ((C.couple ρ L).pageCouple r).derivedDInclusion p q ≫ (map ρ r u).tD p q
  homology_square (ρ : ℤ) (r : ℕ) {L M : DerivedCategory A} (u : L ⟶ M) (p q : ℤ) :
    ∃ z : kernel (((C.couple ρ L).pageCouple r).d p q) ⟶
        kernel (((C.couple ρ M).pageCouple r).d p q),
      z ≫ kernel.ι (((C.couple ρ M).pageCouple r).d p q) =
        kernel.ι (((C.couple ρ L).pageCouple r).d p q) ≫ (map ρ r u).tE p q ∧
      ((C.couple ρ L).pageCouple r).derivedEProjection p q ≫ (map ρ (r + 1) u).tE p q =
        z ≫ ((C.couple ρ M).pageCouple r).derivedEProjection p q

/-- Objects for which both finite cycle and boundary subobjects at `(p,q)` stabilize.
This imposes no existence of infinite intersections or unions in the ambient category.
Source: Stacks Tag 012U (blueprint: lem-per-postnikov-additive-exact-couple). -/
def postnikovStable {T : DerivedCategory A ⥤ B} (C : PostnikovCoupleData T)
    (ρ p q : ℤ) : ObjectProperty (DerivedCategory A) :=
  fun L ↦ ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
    (C.couple ρ L).cycleBoundaryTower.Z s p q =
      (C.couple ρ L).cycleBoundaryTower.Z r p q ∧
    (C.couple ρ L).cycleBoundaryTower.B s p q =
      (C.couple ρ L).cycleBoundaryTower.B r p q

/-- The half-plane hypothesis, allowing each object its own lower cutoff.
Source: blueprint thm-sp-half-plane-convergence
(blueprint: lem-per-postnikov-additive-exact-couple). -/
def postnikovHalfPlane {T : DerivedCategory A ⥤ B} (C : PostnikovCoupleData T)
    (ρ : ℤ) : ObjectProperty (DerivedCategory A) :=
  fun L ↦ ∃ a : ℤ,
    (∀ p q : ℤ, q < a → IsZero ((C.couple ρ L).D p q)) ∧
    (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero ((C.couple ρ L).E p q))

/-- Stabilized entries are additive functors. Each sufficiently late page comparison is
natural and agrees with the next-page homology projection, independently of the cutoff.
Source: Stacks Tags 011S, 012U (blueprint: lem-per-postnikov-additive-exact-couple). -/
structure PostnikovStableData {T : DerivedCategory A ⥤ B} {C : PostnikovCoupleData T}
    (P : PostnikovPageData C) where
  E (ρ p q : ℤ) : (postnikovStable C ρ p q).FullSubcategory ⥤ B
  additive (ρ p q : ℤ) : (E ρ p q).Additive
  cutoff (ρ p q : ℤ) (L : (postnikovStable C ρ p q).FullSubcategory) : ℕ
  iso (ρ p q : ℤ) (L : (postnikovStable C ρ p q).FullSubcategory)
    (r : ℕ) (h : cutoff ρ p q L ≤ r) :
    ((C.couple ρ L.obj).pageCouple r).E p q ≅ (E ρ p q).obj L
  naturality (ρ p q : ℤ) (L M : (postnikovStable C ρ p q).FullSubcategory)
    (u : L ⟶ M) (r : ℕ) (hL : cutoff ρ p q L ≤ r) (hM : cutoff ρ p q M ≤ r) :
    (P.map ρ r u.hom).tE p q ≫ (iso ρ p q M r hM).hom =
      (iso ρ p q L r hL).hom ≫ (E ρ p q).map u
  transition (ρ p q : ℤ) (L : (postnikovStable C ρ p q).FullSubcategory)
    (r : ℕ) (h : cutoff ρ p q L ≤ r) (h' : cutoff ρ p q L ≤ r + 1) :
    ((C.couple ρ L.obj).pageCouple r).derivedEProjection p q ≫
        (iso ρ p q L (r + 1) h').hom =
      kernel.ι (((C.couple ρ L.obj).pageCouple r).d p q) ≫ (iso ρ p q L r h).hom

/-- Additive image filtrations of the canonical half-plane abutment. The maps on steps
and graded pieces are specified by the mono and quotient squares. Consequently their
functor laws express precisely identities, composition and addition of the induced maps.
Source: Stacks Tags 012F, 012U (blueprint: lem-per-postnikov-additive-exact-couple). -/
structure PostnikovAbutmentData {T : DerivedCategory A ⥤ B} {C : PostnikovCoupleData T}
    (P : PostnikovPageData C) where
  limits (ρ : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    BigradedExactCouple.LimitSubobjects (C.couple ρ L.obj)
  colimit (ρ : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) (n : ℤ) :
    BigradedExactCouple.AlphaColimit (C.couple ρ L.obj) n
  abutmentIso (ρ : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) (n : ℤ) :
    (colimit ρ L n).obj ≅ (postnikovD T ρ 0 n).obj L.obj
  normalized (ρ : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) (n : ℤ) :
    (colimit ρ L n).ι 0 ≫ (abutmentIso ρ L n).hom =
      eqToHom (by congr 1; omega) ≫ (C.dIso ρ L.obj 0 n).hom
  converges (ρ : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (C.couple ρ L.obj).ConvergesTo (limits ρ L) (colimit ρ L)
  abutmentMap (ρ : ℤ) {L M : (postnikovHalfPlane C ρ).FullSubcategory} (u : L ⟶ M)
    (n : ℤ) : (colimit ρ L n).obj ⟶ (colimit ρ M n).obj
  abutmentMap_eq (ρ : ℤ) {L M : (postnikovHalfPlane C ρ).FullSubcategory} (u : L ⟶ M)
    (n : ℤ) : abutmentMap ρ u n =
      (abutmentIso ρ L n).hom ≫ (postnikovD T ρ 0 n).map u.hom ≫
        (abutmentIso ρ M n).inv
  cocone_square (ρ : ℤ) {L M : (postnikovHalfPlane C ρ).FullSubcategory} (u : L ⟶ M)
    (n p : ℤ) :
    (colimit ρ L n).ι p ≫ abutmentMap ρ u n =
      (P.map ρ 0 u.hom).tD p (n - p) ≫ (colimit ρ M n).ι p
  step (ρ n p : ℤ) : (postnikovHalfPlane C ρ).FullSubcategory ⥤ B
  graded (ρ n p : ℤ) : (postnikovHalfPlane C ρ).FullSubcategory ⥤ B
  step_additive (ρ n p : ℤ) : (step ρ n p).Additive
  graded_additive (ρ n p : ℤ) : (graded ρ n p).Additive
  stepIso (ρ n p : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (step ρ n p).obj L ≅
      (((C.couple ρ L.obj).imageFiltration n (colimit ρ L n)).step p : B)
  gradedIso (ρ n p : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (graded ρ n p).obj L ≅
      ((C.couple ρ L.obj).imageFiltration n (colimit ρ L n)).gradedPiece p
  inclusion (ρ n p : ℤ) : step ρ n p ⟶
    (postnikovHalfPlane C ρ).ι ⋙ postnikovD T ρ 0 n
  inclusion_eq (ρ n p : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (inclusion ρ n p).app L = (stepIso ρ n p L).hom ≫
      (((C.couple ρ L.obj).imageFiltration n (colimit ρ L n)).step p).arrow ≫
        (abutmentIso ρ L n).hom
  quotient (ρ n p : ℤ) : step ρ n p ⟶ graded ρ n p
  quotient_eq (ρ n p : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (quotient ρ n p).app L ≫ (gradedIso ρ n p L).hom =
      (stepIso ρ n p L).hom ≫ cokernel.π (Subobject.ofLE _ _
        (((C.couple ρ L.obj).imageFiltration n (colimit ρ L n)).antitone_step
          (by omega : p ≤ p + 1)))
  infinity (ρ p q : ℤ) : (postnikovHalfPlane C ρ).FullSubcategory ⥤ B
  infinity_additive (ρ p q : ℤ) : (infinity ρ p q).Additive
  infinityIso (ρ p q : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (infinity ρ p q).obj L ≅ (C.couple ρ L.obj).pageInfinity (limits ρ L) p q
  comparison (ρ p q : ℤ) : infinity ρ p q ≅ graded ρ (p + q) p
  comparison_eq (ρ p q : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) :
    (C.couple ρ L.obj).toPageInfinity (limits ρ L) p q ≫
        (infinityIso ρ p q L).inv ≫ (comparison ρ p q).hom.app L ≫
          (gradedIso ρ (p + q) p L).hom =
      (C.couple ρ L.obj).toGradedPiece (colimit ρ L) p q
  infinity_natural (ρ p q : ℤ) {L M : (postnikovHalfPlane C ρ).FullSubcategory}
    (u : L ⟶ M) :
    ∃ z : ((limits ρ L).Z p q : B) ⟶ ((limits ρ M).Z p q : B),
      z ≫ ((limits ρ M).Z p q).arrow =
        ((limits ρ L).Z p q).arrow ≫ (P.map ρ 0 u.hom).tE p q ∧
      cokernel.π (Subobject.ofLE _ _
          (BigradedExactCouple.limitBoundary_le_cycle _ (limits ρ L) p q)) ≫
          (infinityIso ρ p q L).inv ≫ (infinity ρ p q).map u ≫
            (infinityIso ρ p q M).hom =
        z ≫ cokernel.π (Subobject.ofLE _ _
          (BigradedExactCouple.limitBoundary_le_cycle _ (limits ρ M) p q))
  stable_cutoff (ρ p q : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory) : ℕ
  stableIso (ρ p q : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory)
    (r : ℕ) (h : stable_cutoff ρ p q L ≤ r) :
    (P.E ρ r p q).obj L.obj ≅ (infinity ρ p q).obj L
  stable_natural (ρ p q : ℤ) {L M : (postnikovHalfPlane C ρ).FullSubcategory}
    (u : L ⟶ M) (r : ℕ) (hL : stable_cutoff ρ p q L ≤ r)
    (hM : stable_cutoff ρ p q M ≤ r) :
    (P.E ρ r p q).map u.hom ≫ (stableIso ρ p q M r hM).hom =
      (stableIso ρ p q L r hL).hom ≫ (infinity ρ p q).map u
  stable_projection (ρ p q : ℤ) (L : (postnikovHalfPlane C ρ).FullSubcategory)
    (r : ℕ) (h : stable_cutoff ρ p q L ≤ r) :
    ∃ z : ((limits ρ L).Z p q : B) ≅
        ((C.couple ρ L.obj).cycleBoundaryTower.Z r p q : B),
      z.hom ≫ ((C.couple ρ L.obj).cycleBoundaryTower.Z r p q).arrow =
        ((limits ρ L).Z p q).arrow ∧
      z.hom ≫ (C.couple ρ L.obj).cycleBoundaryTower.projection r p q ≫
          (P.eIso ρ r p q L.obj).inv ≫ (stableIso ρ p q L r h).hom ≫
            (infinityIso ρ p q L).hom =
        cokernel.π (Subobject.ofLE _ _
          (BigradedExactCouple.limitBoundary_le_cycle _ (limits ρ L) p q))

/-- The Mathlib spectral sequence on the iterated pages. The page comparison and the
specified differential identify it with the exact-couple iteration, including its morphisms.
Source: Stacks Tag 011S (blueprint: lem-per-postnikov-additive-exact-couple). -/
structure PostnikovSpectralData {T : DerivedCategory A ⥤ B} {C : PostnikovCoupleData T}
    (P : PostnikovPageData C) where
  sequence (ρ : ℤ) : DerivedCategory A ⥤
    SpectralSequence B (fun r : ℤ ↦ ComplexShape.up' (r, 1 - r)) 2
  iso (ρ : ℤ) (L : DerivedCategory A) (r : ℕ) (p q : ℤ) :
    (((sequence ρ).obj L).page ((r : ℤ) + 2)).X (p, q) ≅
      ((C.couple ρ L).pageCouple r).E p q
  naturality (ρ : ℤ) {L M : DerivedCategory A} (u : L ⟶ M) (r : ℕ) (p q : ℤ) :
    (((sequence ρ).map u).hom ((r : ℤ) + 2)).f (p, q) ≫ (iso ρ M r p q).hom =
      (iso ρ L r p q).hom ≫ (P.map ρ r u).tE p q
  differential (ρ : ℤ) (L : DerivedCategory A) (r : ℕ) (p q : ℤ) :
    (((sequence ρ).obj L).page ((r : ℤ) + 2)).d
        (p, q) (p + 2 + r, q - 1 - r) ≫
          (iso ρ L r (p + 2 + r) (q - 1 - r)).hom =
      (iso ρ L r p q).hom ≫ ((C.couple ρ L).pageCouple r).d p q
  homology (ρ : ℤ) (L : DerivedCategory A) (r : ℕ) (p q : ℤ) :
    ∃ z : (((sequence ρ).obj L).page ((r : ℤ) + 2)).cycles (p, q) ≅
        kernel (((C.couple ρ L).pageCouple r).d p q),
      z.hom ≫ kernel.ι (((C.couple ρ L).pageCouple r).d p q) =
        (((sequence ρ).obj L).page ((r : ℤ) + 2)).iCycles (p, q) ≫
          (iso ρ L r p q).hom ∧
      z.hom ≫ ((C.couple ρ L).pageCouple r).derivedEProjection p q =
        (((sequence ρ).obj L).page ((r : ℤ) + 2)).homologyπ (p, q) ≫
          (((sequence ρ).obj L).iso ((r : ℤ) + 2) ((r + 1 : ℕ) + (2 : ℤ))
            (p, q) (by omega)).hom ≫ (iso ρ L (r + 1) p q).hom

/-- Transport along any natural isomorphism of additive abutment functors preserves
both the filtration and its graded and stable-page comparison. The step and graded
functors themselves represent the transported subobjects and quotients; no new map
is chosen after transport.
Source: Stacks Tags 0121, 012U (blueprint: lem-per-postnikov-additive-exact-couple). -/
def PostnikovAbutmentData.Transport {T : DerivedCategory A ⥤ B}
    {C : PostnikovCoupleData T} {P : PostnikovPageData C}
    (H : PostnikovAbutmentData P) : Prop :=
  ∀ (ρ n : ℤ) (F : (postnikovHalfPlane C ρ).FullSubcategory ⥤ B) (_ : F.Additive)
    (η : (postnikovHalfPlane C ρ).ι ⋙ postnikovD T ρ 0 n ≅ F),
    ∃ (ι : ∀ p : ℤ, H.step ρ n p ⟶ F)
      (G : ∀ L : (postnikovHalfPlane C ρ).FullSubcategory,
        DecreasingFiltration (F.obj L))
      (e : ∀ (L : (postnikovHalfPlane C ρ).FullSubcategory) (p : ℤ),
        (H.graded ρ n p).obj L ≅ (G L).gr p),
      (∀ p L, (ι p).app L = (H.inclusion ρ n p).app L ≫ η.hom.app L) ∧
      (∀ p L, (G L).F p = imageSubobject ((ι p).app L)) ∧
      (∀ (L : (postnikovHalfPlane C ρ).FullSubcategory) (p : ℤ),
        ∃ z : (H.step ρ n p).obj L ≅ ((G L).F p : B),
          z.hom ≫ ((G L).F p).arrow = (ι p).app L ∧
          (H.quotient ρ n p).app L ≫ (e L p).hom =
            z.hom ≫ cokernel.π (Subobject.ofLE _ _ ((G L).F_succ_le p))) ∧
      (∀ (L M : (postnikovHalfPlane C ρ).FullSubcategory) (u : L ⟶ M) (p : ℤ),
        (H.step ρ n p).map u ≫ (ι p).app M = (ι p).app L ≫ F.map u) ∧
      (∀ (L M : (postnikovHalfPlane C ρ).FullSubcategory) (u v : L ⟶ M) (p : ℤ),
        F.map (u + v) = F.map u + F.map v ∧
        (H.step ρ n p).map (u + v) = (H.step ρ n p).map u + (H.step ρ n p).map v ∧
        (H.graded ρ n p).map (u + v) =
          (H.graded ρ n p).map u + (H.graded ρ n p).map v)

end DerivedCategory
