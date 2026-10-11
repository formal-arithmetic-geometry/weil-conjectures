/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.CategoryTheory.TruncationCouple
import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# Hypercohomology filtrations for an étale base-change square

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1315;
Stacks Project, Tags 0DDE and 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

The three functors are Rf_*, g^{-1}Rf_*, and Rf'_*g'^{-1}. The generic construction
below applies cohomology to their images of the canonical truncation triangles.
The index of `pageCouple` is the actual page minus two.
-/

set_option synthInstance.maxSize 2048

universe u v₁ u₁ v₂ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
  (K : CochainComplex.Plus A)
/-- The D-terms after applying the chosen triangulated functor to truncations.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyD (p q : ℤ) : B :=
  (DerivedCategory.homologyFunctor B (p + q)).obj
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj))

/-- The E₂-terms after applying the functor to the shifted cohomology complexes.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyE (p q : ℤ) : B :=
  (DerivedCategory.homologyFunctor B (p + q)).obj
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K q).obj))

/-- The truncation inclusion, of bidegree (-1,+1).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyAlpha (p q : ℤ) :
    hypercohomologyD F K p q ⟶ hypercohomologyD F K (p - 1) (q + 1) :=
  (DerivedCategory.homologyFunctor B (p + q)).map
    (F.map (DerivedCategory.Q.map
      (eqToHom (congrArg (fun n : ℤ ↦ K.obj.truncLE n)
        (by omega : q = (q + 1) - 1)) ≫ TruncationCouple.transition K (q + 1)))) ≫
    eqToHom (by unfold hypercohomologyD; congr 2; omega)

/-- The projection from a truncation to its top cohomology, of bidegree (0,0).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyG (p q : ℤ) :
    hypercohomologyD F K p q ⟶ hypercohomologyE F K (p + (0 : ℕ)) (q - (0 : ℕ)) :=
  (DerivedCategory.homologyFunctor B (p + q)).map
    (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
    eqToHom (by simp only [hypercohomologyE, Nat.cast_zero, add_zero, sub_zero])

/-- The cohomological boundary of the image triangle, of bidegree (+2,-1).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyBoundary (p q : ℤ) :
    hypercohomologyE F K p q ⟶ hypercohomologyD F K (p + 2) (q - 1) :=
  DerivedCategory.HomologySequence.δ
    (F.mapTriangle.obj (TruncationCouple.triangle K q)) (p + q) (p + q + 1) ≫
    eqToHom (by unfold hypercohomologyD; congr 2; omega)

/-- The three cohomology maps form an exact couple.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: The canonical truncation triangle is distinguished (def-sp-truncation-couple). The
triangulated functor carries it to a distinguished triangle. Its cohomology long exact sequence
gives the three zero composites and image-kernel equalities at every bidegree; reindex by the
displayed shifts (def-sp-exact-couple). -/
theorem hypercohomology_maps_exact :
    (∀ p q : ℤ, hypercohomologyBoundary F K p q ≫
      hypercohomologyAlpha F K (p + 2) (q - 1) = 0) ∧
    (∀ p q : ℤ, hypercohomologyG F K p q ≫ 
      hypercohomologyBoundary F K (p + (0 : ℕ)) (q - (0 : ℕ)) = 0) ∧
    (∀ p q : ℤ, hypercohomologyAlpha F K p q ≫
      hypercohomologyG F K (p - 1) (q + 1) = 0) ∧
    (∀ p q : ℤ, imageSubobject (hypercohomologyBoundary F K p q) =
      kernelSubobject (hypercohomologyAlpha F K (p + 2) (q - 1))) ∧
    (∀ p q : ℤ, imageSubobject (hypercohomologyG F K p q) =
      kernelSubobject (hypercohomologyBoundary F K (p + (0 : ℕ)) (q - (0 : ℕ)))) ∧
    (∀ p q : ℤ, imageSubobject (hypercohomologyAlpha F K p q) =
      kernelSubobject (hypercohomologyG F K (p - 1) (q + 1))) := by
  sorry

/-- The exact truncation couple, with explicit data and separately named exactness proofs.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyCouple : BigradedExactCouple B 0 where
  D := hypercohomologyD F K
  E := hypercohomologyE F K
  alpha := hypercohomologyAlpha F K
  f := hypercohomologyBoundary F K
  g p q := hypercohomologyG F K p q
  alpha_f_zero := (hypercohomology_maps_exact F K).1
  f_g_zero := (hypercohomology_maps_exact F K).2.1
  g_alpha_zero := (hypercohomology_maps_exact F K).2.2.1
  exact_alpha := (hypercohomology_maps_exact F K).2.2.2.1
  exact_f := (hypercohomology_maps_exact F K).2.2.2.2.1
  exact_g := (hypercohomology_maps_exact F K).2.2.2.2.2

/-- The canonical map from a truncation to the abutment in total degree n.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyAbutmentMap (n q : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj
        (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj)) ⟶
      (DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj)) :=
  (DerivedCategory.homologyFunctor B n).map
    (F.map (DerivedCategory.Q.map (K.obj.ιTruncLE q)))

/-- The images of the truncation maps decrease with p.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: For i ≤ j, n-j ≤ n-i. The canonical inclusion of the lower truncation into the higher
truncation commutes with their inclusions into K. Apply F and H^n to this factorization. The image
of a composite is contained in the image of its second factor, which gives the required
antitonicity (def-sp-image-filtration). -/
theorem hypercohomology_images_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ imageSubobject (hypercohomologyAbutmentMap F K n (n - p))) := by
  sorry

/-- The image filtration FᵖHⁿ = im(Hⁿ(Fτ≤(n-p)K) → Hⁿ(FK)).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyFiltration (n : ℤ) :
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj))) where
  step p := imageSubobject (hypercohomologyAbutmentMap F K n (n - p))
  antitone_step := hypercohomology_images_antitone F K n

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

/-- The functor Rf_*.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable abbrev hypercohomologyFirstFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor

/-- The functor g⁻¹Rf_*.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable abbrev hypercohomologyBaseChangeFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor ⋙
    (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory

/-- The functor Rf'_*(g')⁻¹.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable abbrev hypercohomologySecondFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategory ⋙
    (lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctor

/-- The three hypercohomology filtrations, on Y and twice on Y', in total degree n.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyFiltrations (n : ℤ) :
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor _ n).obj
        ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ×
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor _ n).obj
        ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj))) ×
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor _ n).obj
        ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj))) :=
  ⟨hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n,
    hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n,
    hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n⟩

/-- The three spectral sequences have the stated E₂ terms, finite filtrations, and unconditional
  convergence, the first couple is the truncation couple of def-sp-truncation-couple for f_*
  through `TruncationCouple.bridgeIso`, and the middle one is the exact inverse image of the
  first.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: Choose the strictly bounded-below representative as in
  def-sbc-standard-tstructure-derived-category. Apply thm-sp-truncation-e2 to f_* and to f'_* on
  the termwise inverse image complex. The bridgeIso of def-sp-truncation-couple identifies these
  couples with hypercohomologyCouple: both sides are cohomology of the same maps of truncation
  triangles, and bridgeIso is natural in the complex. Exact inverse image commutes with
  truncation kernels and cohomology
  (prop-weil-pbc-inverse-image-exact, lem-weil-pbc-exact-functor-bounded-below).
  Naturality, including the shift compatibility at the boundary arrow, identifies the middle
  couple with the inverse image of the first. Apply lem-sp-exact-functor-couple to compare all
  pages and differentials. Its image preservation identifies the middle filtration with g⁻¹F. The
  half-plane bounds transfer under exact inverse image; def-sp-convergence and
  thm-sp-truncation-e2 give the diagonal colimits, finite image filtrations, support a≤q≤n, and
  convergence for all three couples. -/
theorem hypercohomologyFiltrations_spec
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p =
        ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).page r p
        q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n (T
                n)).step p) =
            (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p)) ∧
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K
        n).step p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p).arrow =
          0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
        K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            n).obj
            ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologyBaseChangeFunctor f g) K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).imageFiltration n
                (T n)).step p) =
            (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p)) ∧
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step
        p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor f' g')
        K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            n).obj
            ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
                (T n)).step p) =
            (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p)) ∧
    (∀ p q : ℤ, hypercohomologyAlpha (hypercohomologyFirstFunctor f) K p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K (q + 1)) (p - 1 + (q + 1))).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.alpha (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ p q : ℤ, hypercohomologyBoundary (hypercohomologyFirstFunctor f) K p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K (q - 1)) (p + 2 + (q - 1))).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom ≫
        TruncationCouple.f (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ p q : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).initialG p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.g (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).E p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q))) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).E p q ≅
        (upperStar AddCommGrpCat.{u + 1} g).obj
          (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q)))) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).E p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f').rightDerived p).obj
          ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)))) ∧
    (∀ i : ℤ, i < a → IsZero
      ((((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj).X i)) ∧
    (∀ q : ℤ, ∃ c :
        ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (K.obj.truncLE q) ≅
        CochainComplex.truncLE
          (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K.obj) q,
      c.hom ≫
        CochainComplex.ιTruncLE
          (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K.obj) q =
        ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).map
          (K.obj.ιTruncLE q)) ∧
    (∀ q : ℤ, Nonempty
      ((((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj).homology q ≅ (upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q))) ∧
    (∃ δ : ∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).obj ((hypercohomologyCouple
      (hypercohomologyFirstFunctor f) K).D p q) ≅ (hypercohomologyCouple
      (hypercohomologyBaseChangeFunctor f g) K).D p q,
      ∃ φ : ∀ (r : ℕ) (p q : ℤ),
        (upperStar AddCommGrpCat.{u + 1} g).obj (((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).pageCouple r).E p q) ≅
          ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E p q,
        (∀ p q : ℤ, δ p q =
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso (p + q)).app
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K q).obj))) ∧
        (∀ p q : ℤ, φ 0 p q =
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso (p + q)).app
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.cohomologyComplex K q).obj))) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).alpha p q) ≫
          (δ (p - 1) (q + 1)).hom = (δ p q).hom ≫ (hypercohomologyCouple
            (hypercohomologyBaseChangeFunctor f g) K).alpha p q) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).f p q) ≫
          (δ (p + 2) (q - 1)).hom = (φ 0 p q).hom ≫ (hypercohomologyCouple
            (hypercohomologyBaseChangeFunctor f g) K).f p q) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).initialG p q) ≫
          (φ 0 p q).hom = (δ p q).hom ≫ (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f
            g) K).initialG p q) ∧
        (∀ (r : ℕ) (p q : ℤ),
          (upperStar AddCommGrpCat.{u + 1} g).map (((hypercohomologyCouple
            (hypercohomologyFirstFunctor f) K).pageCouple r).d p q) ≫
            (φ r (p + 2 + r) (q - 1 - r)).hom =
          (φ r p q).hom ≫ ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
            K).pageCouple r).d p q)) ∧
    (∀ n : ℤ, ∃ c : (upperStar AddCommGrpCat.{u + 1} g).obj
        ((DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ≅
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
      c = (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso n).app
        ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ∧
      ∀ p : ℤ, imageSubobject ((upperStar AddCommGrpCat.{u + 1} g).map
          ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow ≫ c.hom) =
        (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p) := by
  sorry

end AlgebraicGeometry.Etale
