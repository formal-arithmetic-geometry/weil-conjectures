/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import Sheaf.CategoryTheory.CartanEilenbergMappedTotal
import Sheaf.CategoryTheory.FilteredComplexSpectralSequence
import Sheaf.CategoryTheory.BoundedBelowCechConeComparison
import Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.FiniteCechAugmentationModules
import Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined
import Sheaf.TraceFormula.DerivedCechDiagramFunctorialModules
import Sheaf.TraceFormula.DerivedSectionsFinitePushforwardModules
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Natural finite-cover Čech hypercohomology descent

Source: Stacks Project, Étale Cohomology, Tag 09Z2; Derived Categories, Tags 0141 and 015J;
Homology, Tags 012Z and 0132 (blueprint: lem-trf-finite-base-cech-hypercohomology).

The auxiliary interfaces spell out resolved augmented diagrams and their finite-column
filtration. All coefficient categories, pullbacks, sections, total complexes and pages
are the existing constructions. Integer internal indices retain negative cohomology.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Canonical restriction on derived module-valued sections: the derived adjunction unit
followed by Leray. Source: Stacks Tag 09Z2, natural restriction maps
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj K) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (ModuleCat.{u + 1} Λ) f).hom.app _

/-- The canonical composition comparison of exact derived inverse images.
Source: Stacks Tag 09Z2, identification of iterated restrictions
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechPullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : k = f ≫ g) :
    (upperStar (ModuleCat.{u + 1} Λ) k).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) f g k w) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The actual `(q+1)`-fold scheme fibre product and its structure map.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable abbrev finiteCechProjection {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (q : SimplexCategory) :=
  (Arrow.mk p).augmentedCechNerve.hom.app (op q)

/-- Canonical restriction between two Čech columns, including coefficient transport.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechColumnMap {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {n m : SimplexCategory} (f : n ⟶ m) :=
  finiteCechRestriction Λ ((Arrow.mk p).cechNerve.map f.op)
      ((upperStar (ModuleCat.{u + 1} Λ) (finiteCechProjection p n)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
      ((Arrow.mk p).cechNerve.obj (op m))).map
        ((finiteCechPullbackComp Λ ((Arrow.mk p).cechNerve.map f.op)
          (finiteCechProjection p n) (finiteCechProjection p m)
          (by
            have w := (Arrow.mk p).augmentedCechNerve.hom.naturality f.op
            change (Arrow.mk p).cechNerve.map f.op ≫ finiteCechProjection p n =
              finiteCechProjection p m ≫ 𝟙 Y at w
            exact (w.trans (Category.comp_id _)).symm)).inv.app K)

/-- The resolved alternating-coface bicomplex, extended by zero in negative Čech degrees.
Its total differential is `δ + (-1)^q d` by the existing total-complex sign convention.
Source: Stacks Tags 012Z and 09Z2
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechBicomplex
    (D : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ)) :
    HomologicalComplex₂ (ModuleCat.{u + 1} Λ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((AlgebraicTopology.alternatingCofaceMapComplex _).obj D.right).extend
    ComplexShape.embeddingUpNat

/-- Total of the resolved Čech diagram, with integer internal degrees.
Source: Stacks Tags 012Z and 09Z2
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechTotal
    (D : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ)) :=
  (finiteCechBicomplex Λ D).total (ComplexShape.up ℤ)

/-- A map of actual augmented resolved diagrams induces the existing total map.
Source: Stacks Tags 012Z and 09Z2
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechTotalMap
    {D E : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ)}
    (f : D ⟶ E) : finiteCechTotal Λ D ⟶ finiteCechTotal Λ E :=
  HomologicalComplex₂.total.map
    (HomologicalComplex.extendMap
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map f.right)
      ComplexShape.embeddingUpNat) (ComplexShape.up ℤ)

/-- A compatible bounded-below cochain representation of the augmented derived Čech diagram.
The comparisons specify every simplex map and augmentation, rather than unrelated columns.
Source: Stacks Tag 09Z2 and Derived Categories Tag 0141
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
structure FiniteCechResolvedModel {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) where
  diagram : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
  pointIso : DerivedCategory.Q.obj diagram.left ≅
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K
  columnIso : ∀ q : SimplexCategory, DerivedCategory.Q.obj (diagram.right.obj q) ≅
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
      ((Arrow.mk p).cechNerve.obj (op q))).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (finiteCechProjection p q)).mapDerivedCategory.obj K)
  belowPoint : diagram.left.IsStrictlyGE a
  belowColumns : ∀ q : SimplexCategory, (diagram.right.obj q).IsStrictlyGE a
  columnMap : ∀ {n m : SimplexCategory} (f : n ⟶ m),
    DerivedCategory.Q.map (diagram.right.map f) ≫ (columnIso m).hom =
      (columnIso n).hom ≫ finiteCechColumnMap Λ p K f
  augmentationMap : ∀ q : SimplexCategory,
    DerivedCategory.Q.map (diagram.hom.app q) ≫ (columnIso q).hom =
      pointIso.hom ≫ finiteCechRestriction Λ (finiteCechProjection p q) K
  augmentation : diagram.left ⟶ finiteCechTotal Λ diagram
  augmentationComponent : ∀ j : ℤ, augmentation.f j =
    (diagram.hom.app ⦋0⦌).f j ≫
      (HomologicalComplex.extendXIso
        ((AlgebraicTopology.alternatingCofaceMapComplex _).obj diagram.right)
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv.f j ≫
      (finiteCechBicomplex Λ diagram).ιTotal (ComplexShape.up ℤ) 0 j j (zero_add j)
  augmentationQuasiIso : QuasiIso augmentation

/-- Column filtration, its exact couple, finite abutment filtration and stationary pages.
All indices `j` are integers, with lower bound `a`, not natural numbers.
Source: Stacks Tags 012K, 0130, 0132 and 09Z2
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
def FiniteCechSpectralConvergence {Z Y : Scheme.{u}} {p : Z ⟶ Y}
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a : ℤ}
    (M : FiniteCechResolvedModel Λ p K a) : Prop :=
  ∃ (F : DecreasingFiltration (finiteCechTotal Λ M.diagram))
    (E : CohomologicalSpectralSequence (ModuleCat.{u + 1} Λ) 1)
    (e₁ : ∀ q j : ℤ, (E.page 1).X (q, j) ≅ (F.gradedPiece q).homology (q + j))
    (G : ∀ n : ℤ, DecreasingFiltration ((finiteCechTotal Λ M.diagram).homology n))
    (X : BigradedExactCouple (ModuleCat.{u + 1} Λ) 0) (L : X.LimitSubobjects)
    (H : ∀ n : ℤ, X.AlphaColimit n)
    (eH : ∀ n : ℤ, (H n).obj ≅ (finiteCechTotal Λ M.diagram).homology n)
    (eD : ∀ P Q : ℤ,
      X.D P Q ≅ (F.step (-Q) : CochainComplex (ModuleCat.{u + 1} Λ) ℤ).homology (P + Q))
    (eC : ∀ (s : ℕ) (q j : ℤ),
      (X.pageCouple s).E (2 * q + j) (-q) ≅ (E.page (s + 1) (by omega)).X (q, j)),
    (∀ b n : ℤ, F.complexStep b n = (Finset.Icc (max 0 b) (n - a)).sup
      (fun q ↦ imageSubobject ((finiteCechBicomplex Λ M.diagram).ιTotalOrZero
        (ComplexShape.up ℤ) q (n - q) n))) ∧
    (∀ q : ℕ, ∀ j : ℤ, Nonempty ((E.page 1).X ((q : ℤ), j) ≅
      (M.diagram.right.obj ⦋q⦌).homology j)) ∧
    (∀ (q j r : ℤ) (hr : 1 ≤ r), q < 0 ∨ j < a → IsZero ((E.page r hr).X (q, j))) ∧
    (∀ n b : ℤ, (G n).step b =
      imageSubobject (HomologicalComplex.homologyMap (F.step b).arrow n)) ∧
    (∀ n : ℤ, (G n).IsFinite) ∧
    (∀ n P : ℤ, (H n).ι P ≫ (eH n).hom =
      (eD P (n - P)).hom ≫ eqToHom (by
        rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
        HomologicalComplex.homologyMap (F.step (P - n)).arrow n) ∧
    (∀ P Q : ℤ, X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
      (eD P Q).hom ≫ HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + 1)))
          (F.antitone_step (by omega))) (P + Q) ≫
        eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
    (∀ P Q : ℤ, X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
        (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ (-Q) (P + 2 * Q)).hom ≫
        eqToHom (by rw [show -Q + (P + 2 * Q) = P + Q by omega]; rfl) =
      (eD P Q).hom ≫ HomologicalComplex.homologyMap
        (F.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
    (∀ (s : ℕ) (q j : ℤ), (eC s q j).hom ≫
        (E.page (s + 1) (by omega)).d (q, j) (q + (s + 1), j - (s + 1) + 1) =
      (X.pageCouple s).d (2 * q + j) (-q) ≫ eqToHom (by congr 1 <;> omega) ≫
        (eC s (q + (s + 1)) (j - (s + 1) + 1)).hom) ∧
    X.ConvergesTo L H ∧
    (∀ q j : ℤ, Nonempty
      (X.pageInfinity L (2 * q + j) (-q) ≅ (G (q + j)).gradedPiece q)) ∧
    (∀ q j : ℤ, ∃ (N : ℤ) (hN : 1 ≤ N), ∀ (s : ℤ) (hs : N ≤ s),
      (E.page s (by omega)).d (q, j) (q + s, j - s + 1) = 0 ∧
      (E.page s (by omega)).d (q - s, j + s - 1) (q, j) = 0 ∧
      Nonempty ((E.page s (by omega)).X (q, j) ≅ (E.page N hN).X (q, j)) ∧
      Nonempty ((E.page s (by omega)).X (q, j) ≅ (G (q + j)).gradedPiece q))

/-- A roof of actual augmented cochain diagrams, whose backward arrow is a quasi-isomorphism
at the augmentation, every column and the total. Intermediate diagrams share the lower bound.
Source: Stacks Derived Categories Tag 0141 and Homology Tag 0132
(blueprint: lem-trf-finite-base-cech-hypercohomology). -/
structure FiniteCechResolvedRoof
    (D E : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ))
    (a : ℤ) where
  middle : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
  target : CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u + 1} Λ) ℤ)
  forward : D ⟶ target
  backward : middle ⟶ target
  last : middle ⟶ E
  belowMiddle : middle.left.IsStrictlyGE a ∧
    ∀ q : SimplexCategory, (middle.right.obj q).IsStrictlyGE a
  belowTarget : target.left.IsStrictlyGE a ∧
    ∀ q : SimplexCategory, (target.right.obj q).IsStrictlyGE a
  pointIso : DerivedCategory.Q.obj middle.left ≅ DerivedCategory.Q.obj target.left
  pointIso_hom : pointIso.hom = DerivedCategory.Q.map backward.left
  columnIso : ∀ q : SimplexCategory, DerivedCategory.Q.obj (middle.right.obj q) ≅
    DerivedCategory.Q.obj (target.right.obj q)
  columnIso_hom : ∀ q : SimplexCategory,
    (columnIso q).hom = DerivedCategory.Q.map (backward.right.app q)
  totalIso : DerivedCategory.Q.obj (finiteCechTotal Λ middle) ≅
    DerivedCategory.Q.obj (finiteCechTotal Λ target)
  totalIso_hom : totalIso.hom = DerivedCategory.Q.map (finiteCechTotalMap Λ backward)

/-- The canonical base-change map of Čech schemes (no cohomological isomorphism is assumed).
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechBaseMap {Z Y Y' : Scheme.{u}} (p : Z ⟶ Y) (h : Y' ⟶ Y) :=
  Arrow.mapAugmentedCechNerve
    (Arrow.homMk (pullback.snd h p) h (pullback.condition.symm) :
      Arrow.mk (pullback.fst h p) ⟶ Arrow.mk p)

/-- The coefficient comparison in a base-changed column, from the two composition comparisons.
Source: Stacks Tag 09Z2 (blueprint: lem-trf-finite-base-cech-hypercohomology). -/
noncomputable def finiteCechBaseCoefficientIso {Z Y Y' : Scheme.{u}}
    (p : Z ⟶ Y) (h : Y' ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (q : SimplexCategory) :=
  ((finiteCechPullbackComp Λ ((finiteCechBaseMap p h).left.app (op q))
    (finiteCechProjection p q) (finiteCechProjection (pullback.fst h p) q ≫ h)
    (by
      have w := congrArg (fun t ↦ t.app (op q)) (finiteCechBaseMap p h).w
      change (finiteCechBaseMap p h).left.app (op q) ≫ finiteCechProjection p q =
        finiteCechProjection (pullback.fst h p) q ≫ h at w
      exact w.symm)).app K).symm ≪≫
    (finiteCechPullbackComp Λ (finiteCechProjection (pullback.fst h p) q) h
      (finiteCechProjection (pullback.fst h p) q ≫ h) rfl).app K

/-- Finite surjective Čech hypercohomology descent with its convergent column spectral
sequence and canonical base restriction square.

Source: Stacks Project, Étale Cohomology Tag 09Z2, extended to bounded-below complexes;
Derived Categories Tags 0141 and 015J; Homology Tags 012K, 012Z, 0130 and 0132
(blueprint: lem-trf-finite-base-cech-hypercohomology).

Proof (postponed in stage 2).
1. Choose a strictly supported representative F of K in degrees at least a, using the
   standard t-structure. Put C_q = p_{q*} p_q⁻¹ F, augmented by F. Exact inverse image
   preserves the bound. The module Čech augmentation lemma gives exact horizontal rows
   before replacement. Apply the Cartan--Eilenberg augmentation criterion to these rows:
   F → Tot C is a quasi-isomorphism with differential δ + (-1)^q d.
2. In the Grothendieck abelian module-sheaf category choose one functorial bounded-below
   injective resolution I and its natural comparison. Apply it to every coface,
   codegeneracy and augmentation, obtaining J_q = I(C_q), also J_{-1} = I(F).
   The common lower bound is preserved. Take alternating sums of the resolved cofaces;
   do not assume I additive or the resolved horizontal rows exact.
3. The vertical cones of C_q → J_q are acyclic and supported in degrees at least a-1.
   The first double-complex spectral sequence makes their total acyclic. On horizontal
   degree q, (b,c) ↦ (b,(-1)^q c) identifies this total with the cone of Tot C → Tot J,
   including the minus sign on the shifted C horizontal differential. Thus that total
   map is a quasi-isomorphism. This reindexes vertical degrees without changing the sign.
4. Each diagonal has only 0 ≤ q ≤ n-a. Hence Tot J is a bounded-below injective complex
   and therefore K-injective. Its augmentation computes RΓ(Y,K). Additivity of sections
   identifies sections of the finite-diagonal total with the total of sections.
   Module-valued finite-pushforward Leray identifies each resolved column with
   RΓ(Z_q,p_q⁻¹ F). These are the point and column comparisons of the resolved model.
5. Filter by q. The initial graded differential is vertical. Reindex j by j-a to apply
   the first-quadrant spectral-sequence theorem, then translate back. The first page
   is H^j(Z_q,p_q* K), the abutment is H^{q+j}(Y,K), and the image filtration is finite
   in each degree. Exact-couple convergence supplies the stationary pages and finite
   graded pieces. All integer j ≥ a, including negative ones, remain present.
6. For arbitrary h form the canonical mate h⁻¹ C_q → C'_q. The section formula and
   g_q r' = r g_{q+1} prove compatibility with cofaces, repeated-coordinate maps,
   and augmentation. At degree -1 this is the identity on h⁻¹ F. Apply functorial
   resolutions to obtain the actual diagram roof ΓI(C) → ΓI'(h⁻¹I(C)) ← ΓI'(h⁻¹C)
   → ΓI'(C'), with a columnwise quasi-isomorphic backward arrow and the same bound.
7. Apply the bounded-below Čech cone comparison to the backward map to get its total
   quasi-isomorphism. The unit/counit compatibility in finite-pushforward Leray
   identifies every column roof with restriction along g_q, with the displayed
   composition comparison for coefficients. At augmentation it is restriction along h.
   The actual diagram maps commute with augmentation before localization; inverting
   the backward total map gives the displayed square. No column restriction is asserted
   invertible. Naturality in coefficients follows by the same functorial resolution
   construction and its comparison maps. -/
theorem exists_finite_base_cech_hypercohomology {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) [IsFinite p] [Surjective p] (a : ℤ)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [K.IsGE a] :
    ∃ M : FiniteCechResolvedModel Λ p K a,
      FiniteCechSpectralConvergence Λ M ∧
      (∀ (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
        (_ : L.IsGE a) (v : K ⟶ L),
        ∃ (N : FiniteCechResolvedModel Λ p L a)
          (R : FiniteCechResolvedRoof Λ M.diagram N.diagram a),
          (DerivedCategory.Q.map R.forward.left ≫ R.pointIso.inv ≫
              DerivedCategory.Q.map R.last.left) ≫ N.pointIso.hom =
            M.pointIso.hom ≫ (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map v ∧
          (∀ q : SimplexCategory,
            (DerivedCategory.Q.map (R.forward.right.app q) ≫ (R.columnIso q).inv ≫
                DerivedCategory.Q.map (R.last.right.app q)) ≫ (N.columnIso q).hom =
              (M.columnIso q).hom ≫
                (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
                  ((Arrow.mk p).cechNerve.obj (op q))).map
                    ((upperStar (ModuleCat.{u + 1} Λ)
                      (finiteCechProjection p q)).mapDerivedCategory.map v)) ∧
          M.pointIso.inv ≫ DerivedCategory.Q.map M.augmentation ≫
              DerivedCategory.Q.map (finiteCechTotalMap Λ R.forward) ≫ R.totalIso.inv ≫
              DerivedCategory.Q.map (finiteCechTotalMap Λ R.last) =
            (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map v ≫ N.pointIso.inv ≫
              DerivedCategory.Q.map N.augmentation) ∧
      ∀ (Y' : Scheme.{u}) (h : Y' ⟶ Y),
      ∃ (M' : FiniteCechResolvedModel Λ (pullback.fst h p)
          ((upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory.obj K) a)
        (R : FiniteCechResolvedRoof Λ M.diagram M'.diagram a),
        (DerivedCategory.Q.map R.forward.left ≫ R.pointIso.inv ≫
            DerivedCategory.Q.map R.last.left) ≫ M'.pointIso.hom =
          M.pointIso.hom ≫ finiteCechRestriction Λ h K ∧
        (∀ q : SimplexCategory,
          (DerivedCategory.Q.map (R.forward.right.app q) ≫ (R.columnIso q).inv ≫
              DerivedCategory.Q.map (R.last.right.app q)) ≫ (M'.columnIso q).hom =
            (M.columnIso q).hom ≫
              finiteCechRestriction Λ ((finiteCechBaseMap p h).left.app (op q))
                ((upperStar (ModuleCat.{u + 1} Λ)
                  (finiteCechProjection p q)).mapDerivedCategory.obj K) ≫
              (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
                ((Arrow.mk (pullback.fst h p)).cechNerve.obj (op q))).map
                  (finiteCechBaseCoefficientIso Λ p h K q).hom) ∧
        M.pointIso.inv ≫ DerivedCategory.Q.map M.augmentation ≫
            DerivedCategory.Q.map (finiteCechTotalMap Λ R.forward) ≫ R.totalIso.inv ≫
            DerivedCategory.Q.map (finiteCechTotalMap Λ R.last) =
          finiteCechRestriction Λ h K ≫ M'.pointIso.inv ≫
            DerivedCategory.Q.map M'.augmentation := by
  sorry

end AlgebraicGeometry.Etale
