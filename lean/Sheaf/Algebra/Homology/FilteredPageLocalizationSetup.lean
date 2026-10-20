/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Localization of finite filtered pages

Source: Stacks Project, Homology, Tags 012K, 012M, 012O, 012P and 012W, and
Derived Categories, Tags 05S1 and 05S2
(blueprint: def-kun-filtered-page-localization-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The localization D_f(R) of the finite filtered homotopy category at graded
quasi-isomorphisms. Source: Stacks, Tag 05S2.
(blueprint: def-kun-filtered-page-localization-data). -/
abbrev finiteFilteredModuleDerivedCategory (R : Type u) [CommRing R] :=
  (CochainComplex.finiteFilteredModuleQuasiIso R).Localization

/-- The canonical localization functor from H_f(R) to D_f(R).
Source: Stacks, Tag 05S2.
(blueprint: def-kun-filtered-page-localization-data). -/
abbrev finiteFilteredModuleLocalizationFunctor (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleHomotopy R ⥤
      finiteFilteredModuleDerivedCategory R :=
  (CochainComplex.finiteFilteredModuleQuasiIso R).Q

/-- The actual quotient descent of the inclusion F^p into F^(p-r+1).
Source: Stacks, Tag 012K, quotient-image formula.
(blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredPageTransition (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (p r : ℤ) (hr : 1 ≤ r) :
    U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
      U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) := by
  let F := U.obj.filtration
  let ha : p - r + 1 ≤ p := by omega
  let hb : p + 1 ≤ p + r := by omega
  let hs : p ≤ p + r := (Int.le_add_one (show p ≤ p from le_rfl)).trans hb
  let ht : p - r + 1 ≤ p + 1 := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
  let i : (F.step p : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      (F.step (p - r + 1) : CochainComplex (ModuleCat.{u} R) ℤ) :=
    Subobject.ofLE _ _ (F.antitone_step ha)
  let k : (F.step (p + r) : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      (F.step p : CochainComplex (ModuleCat.{u} R) ℤ) :=
    Subobject.ofLE _ _ (F.antitone_step hs)
  let hz : k ≫ i ≫ F.complexQuotientπ (p - r + 1) (p + 1) ht = 0 := by
    dsimp [k, i, DecreasingFiltration.complexQuotientπ]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    rw [← Subobject.ofLE_comp_ofLE (F.step (p + r)) (F.step (p + 1))
      (F.step (p - r + 1)) (F.antitone_step hb) (F.antitone_step ht)]
    simp only [Category.assoc, cokernel.condition, comp_zero]
  exact cokernel.desc k (i ≫ F.complexQuotientπ (p - r + 1) (p + 1) ht) hz

/-- The quotient projection characterizes the transition. Source: Stacks, Tag 012K.
Proof: unfold the cokernel descent and apply cokernel.π_desc. This is Step 1 of the node.
(blueprint: def-kun-filtered-page-localization-data). -/
theorem finiteFilteredPageTransition_projection (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (p r : ℤ) (hr : 1 ≤ r) :
    U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫
        finiteFilteredPageTransition R U p r hr =
      Subobject.ofLE (U.obj.filtration.step p)
          (U.obj.filtration.step (p - r + 1))
          (U.obj.filtration.antitone_step (by omega)) ≫
        U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) := by
  exact cokernel.π_desc _ _ _

-- Avoid unused injectivity lemmas for these large dependent witness records.
set_option genInjectivity false in
/-- The normalized page witness, retained as one record to avoid repeated expansion
of nested choices. Its components and all their normalization laws are those of
`boundedFilteredComplex_pageFunctor_normalized`.
Source: Stacks, Tags 012K, 012M, 012O and 012W.
(blueprint: def-kun-filtered-page-localization-data). -/
structure FiniteFilteredPageModel (R : Type u) [CommRing R] where
  S : ObjectProperty.FullSubcategory
          (fun U : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ U.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence (ModuleCat.{u} R) 1
  e₁ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        ((S.obj U).page 1).X (p, q) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q)
  eI : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          image (HomologicalComplex.homologyMap (finiteFilteredPageTransition R U p r hr) (p + q))
  hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (_hr : 1 ≤ r),
        U.obj.filtration.complexBoundaries p (p + q) r ≤
          U.obj.filtration.complexCycles p (p + q) r
  eZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (hBZ U p q r hr))
  successor_spec : (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
          (p q r : ℤ) (hr : 1 ≤ r),
        (∃ (hZ : U.obj.filtration.complexCycles p (p + q) (r + 1) ≤
              U.obj.filtration.complexCycles p (p + q) r)
            (f : (U.obj.filtration.complexCycles p (p + q) (r + 1) : (ModuleCat.{u} R)) ⟶
              ((S.obj U).page r hr).cycles (p, q)),
          Epi f ∧ f ≫ ((S.obj U).page r hr).iCycles (p, q) =
            Subobject.ofLE _ _ hZ ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫
              (eZ U p q r hr).inv) ∧
        ∀ e : ((S.obj U).page r hr).homology (p, q) ≅
            ((S.obj U).page (r + 1) (by omega)).X (p, q),
          (∀ (hZ : U.obj.filtration.complexCycles p (p + q) (r + 1) ≤
                U.obj.filtration.complexCycles p (p + q) r)
              (f : (U.obj.filtration.complexCycles p (p + q) (r + 1) : (ModuleCat.{u} R)) ⟶
                ((S.obj U).page r hr).cycles (p, q)),
            f ≫ ((S.obj U).page r hr).iCycles (p, q) =
                Subobject.ofLE _ _ hZ ≫
                  cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫
                    (eZ U p q r hr).inv →
              f ≫ ((S.obj U).page r hr).homologyπ (p, q) ≫ e.hom ≫
                  (eZ U p q (r + 1) (by omega)).hom =
                cokernel.π (Subobject.ofLE _ _ (hBZ U p q (r + 1) (by omega)))) ↔
            e = (S.obj U).iso r (r + 1) (p, q) rfl hr)
  map_spec : (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
          (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
        ∃ (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
            (V.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ))
          (a : U.obj.filtration.complexQuotient p (p + r) (by omega) ⟶
            V.obj.filtration.complexQuotient p (p + r) (by omega))
          (b : U.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega) ⟶
            V.obj.filtration.complexQuotient (p - r + 1) (p + 1) (by omega))
          (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p),
          (∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
            (U.obj.filtration.step i).arrow ≫ t.hom.hom) ∧
          U.obj.filtration.complexQuotientπ p (p + r) (by omega) ≫ a =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + r) (by omega) ∧
          U.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ≫ b =
            s (p - r + 1) ≫
              V.obj.filtration.complexQuotientπ (p - r + 1) (p + 1) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
            s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          ((S.map t).hom 1).f (p, q) ≫ (e₁ V p q).hom =
            (e₁ U p q).hom ≫ HomologicalComplex.homologyMap g (p + q) ∧
          ((S.map t).hom r hr).f (p, q) ≫ (eI V p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap
                (finiteFilteredPageTransition R V p r hr) (p + q)) =
            (eI U p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap
                (finiteFilteredPageTransition R U p r hr) (p + q)) ≫
                HomologicalComplex.homologyMap b (p + q))
  representative_spec : ∀ U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite),
    (∀ (p q r : ℤ) (hr : 1 ≤ r),
          ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : (ModuleCat.{u} R)) ⟶
              (U.obj.filtration.complexCycles p (p + q) r : (ModuleCat.{u} R)))
            (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) r : (ModuleCat.{u} R)) ⟶
              (U.obj.filtration.complexQuotient p (p + r) (by omega)).cycles (p + q)),
            z ≫ (U.obj.filtration.complexCycles p (p + q) r).arrow =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
            g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).iCycles (p + q) =
              (U.obj.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
                (U.obj.filtration.complexQuotientπ p (p + r) (by omega)).f (p + q) ∧
            z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫
                (eZ U p q r hr).inv ≫
                (eI U p q r hr).hom ≫
                image.ι (HomologicalComplex.homologyMap
                  (finiteFilteredPageTransition R U p r hr) (p + q)) =
              g ≫ (U.obj.filtration.complexQuotient p (p + r) (by omega)).homologyπ
                (p + q) ≫ HomologicalComplex.homologyMap
                  (finiteFilteredPageTransition R U p r hr) (p + q))
  stabilize_spec : ∀ U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite),
    (∀ p q : ℤ, ∃ (R : ℤ) (hR : 1 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          U.obj.filtration.complexCycles p (p + q) r =
            U.obj.filtration.complexCycles p (p + q) R ∧
          U.obj.filtration.complexBoundaries p (p + q) r =
            U.obj.filtration.complexBoundaries p (p + q) R ∧
          ((S.obj U).page r (by omega)).d (p, q) (p + r, q - r + 1) = 0 ∧
          ((S.obj U).page r (by omega)).d (p - r, q + r - 1) (p, q) = 0 ∧
          Nonempty (((S.obj U).page r (by omega)).X (p, q) ≅
            ((S.obj U).page R hR).X (p, q)))
  successor_naturality : ∀ (U V : ObjectProperty.FullSubcategory
        (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
        (t : U ⟶ V) (p q r : ℤ) (hr : 1 ≤ r),
      ((S.obj U).iso r (r + 1) (p, q) rfl hr).hom ≫
          ((S.map t).hom (r + 1) (by omega)).f (p, q) =
        HomologicalComplex.homologyMap ((S.map t).hom r hr) (p, q) ≫
          ((S.obj V).iso r (r + 1) (p, q) rfl hr).hom
  first_image_spec : ∀ (U : ObjectProperty.FullSubcategory
        (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite))
        (p q : ℤ),
      (eI U p q 1 (by omega)).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (finiteFilteredPageTransition R U p 1 (by omega)) (p + q)) =
        (e₁ U p q).hom ≫
          HomologicalComplex.homologyMap
            (finiteFilteredPageTransition R U p 1 (by omega)) (p + q)
  differential_spec : ∀ U : ObjectProperty.FullSubcategory
        (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite),
      (∀ p q : ℤ,
        ∃ (i : U.obj.filtration.gradedPiece (p + 1) ⟶
            U.obj.filtration.complexQuotient p (p + 2) (by omega))
          (j : U.obj.filtration.complexQuotient p (p + 2) (by omega) ⟶
            U.obj.filtration.gradedPiece p)
          (hij : i ≫ j = 0) (hS : (ShortComplex.mk i j hij).ShortExact),
          U.obj.filtration.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
            Subobject.ofLE (U.obj.filtration.step (p + 1))
              (U.obj.filtration.step p) (U.obj.filtration.antitone_step (by omega)) ≫
                U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ∧
          U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ≫ j =
            U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
          ((S.obj U).page 1).d (p, q) (p + 1, q) ≫ (e₁ U (p + 1) q).hom =
            (e₁ U p q).hom ≫
              hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega))
  abutment_spec : ∀ U : ObjectProperty.FullSubcategory
        (fun W : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ↦ W.filtration.IsFinite),
      (∃ (G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n))
        (X : BigradedExactCouple (ModuleCat.{u} R) 0) (L : X.LimitSubobjects)
        (A : ∀ n : ℤ, X.AlphaColimit n)
        (aH : ∀ n : ℤ, (A n).obj ≅ U.obj.obj.homology n)
        (eD : ∀ P Q : ℤ, X.D P Q ≅
          (U.obj.filtration.step (-Q) : CochainComplex (ModuleCat.{u} R) ℤ).homology (P + Q))
        (eC : ∀ (s : ℕ) (p q : ℤ),
          (X.pageCouple s).E (2 * p + q) (-p) ≅
            ((S.obj U).page (s + 1) (by omega)).X (p, q)),
        (∀ n p : ℤ, (G n).step p =
          imageSubobject (HomologicalComplex.homologyMap
            (U.obj.filtration.step p).arrow n)) ∧
        (∀ n : ℤ, (G n).IsFinite ∧ (G n).IsSeparated) ∧
        (∀ n P : ℤ,
          (A n).ι P ≫ (aH n).hom =
            (eD P (n - P)).hom ≫ eqToHom (by
              rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
              HomologicalComplex.homologyMap
                (U.obj.filtration.step (P - n)).arrow n) ∧
        (∀ P Q : ℤ,
          X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
            (eD P Q).hom ≫ HomologicalComplex.homologyMap
              (Subobject.ofLE (U.obj.filtration.step (-Q))
                (U.obj.filtration.step (-(Q + 1)))
                (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
              eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) ∧
        (∀ P Q : ℤ,
          X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
              (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ U (-Q) (P + 2 * Q)).hom ≫
              eqToHom (by
                rw [show -Q + (P + 2 * Q) = P + Q by omega]
                rfl) =
            (eD P Q).hom ≫ HomologicalComplex.homologyMap
              (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q)) ∧
        (∀ (s : ℕ) (p q : ℤ),
          (eC s p q).hom ≫
              ((S.obj U).page (s + 1) (by omega)).d (p, q)
                (p + (s + 1), q - (s + 1) + 1) =
            (X.pageCouple s).d (2 * p + q) (-p) ≫
              eqToHom (by congr 1 <;> omega) ≫
                (eC s (p + (s + 1)) (q - (s + 1) + 1)).hom) ∧
        X.ConvergesTo L A ∧
        (∀ p q : ℤ, Nonempty
          (X.pageInfinity L (2 * p + q) (-p) ≅ (G (p + q)).gradedPiece p)))

/-- The existing normalized page construction supplies all fields of the bundled model.
Source: Stacks, Tags 012K, 012M, 012O and 012W.
(blueprint: def-kun-filtered-page-localization-data).
Proof. Unpack the normalized page-functor theorem. Retain its functor and three
comparisons, successor normalization, map normalization, cycle-representative
normalization, eventual stabilization, successor naturality, the first-page image
equation, the first differential and the abutment. These are the corresponding fields
of its single normalized witness. -/
theorem finiteFilteredPageModel_nonempty (R : Type u) [CommRing R] :
    Nonempty (FiniteFilteredPageModel R) := by
  obtain ⟨S, e₁, eI, hBZ, eZ, hs⟩ := boundedFilteredComplex_pageFunctor_normalized
    (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦ finiteFilteredPageTransition_projection R U p r hr)
  exact ⟨⟨S, e₁, eI, hBZ, eZ, hs.1, hs.2.2.2.1,
    fun U ↦ (hs.2.2.2.2 U).2.1, fun U ↦ (hs.2.2.2.2 U).2.2.2, hs.2.1, hs.2.2.1,
    fun U ↦ (hs.2.2.2.2 U).1, fun U ↦ (hs.2.2.2.2 U).2.2.1⟩⟩

/-- A normalized page model selected from the proved existence theorem.
The irreducibility keeps its functor and dependent comparisons shared.
Source: Stacks, Tags 012K, 012M, 012O and 012W.
(blueprint: def-kun-filtered-page-localization-data). -/
@[irreducible] noncomputable def finiteFilteredPageModel (R : Type u) [CommRing R] :
    FiniteFilteredPageModel R :=
  (finiteFilteredPageModel_nonempty R).some

/-- The page functor chosen together with its normalized successor maps, first-page
and image comparisons from lem-kun-filtered-page-functor-normalized.
Source: Stacks, Tags 012M and 012O.
(blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredPageFunctor (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤
      CohomologicalSpectralSequence (ModuleCat.{u} R) 1 :=
  (finiteFilteredPageModel R).S

/-- The first-page comparison chosen with the normalized functor.
Source: Stacks, Tag 012M (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredPageFirstIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
    (((finiteFilteredPageFunctor R).obj U).page 1).X (a, b) ≅
      (U.obj.filtration.gradedPiece a).homology (a + b) :=
  (finiteFilteredPageModel R).e₁ U a b

/-- The core image comparison, chosen in the same normalized witness as the functor.
Source: Stacks, Tag 012K (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredPageImageIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
      image (HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht)
        (a + b)) :=
  (finiteFilteredPageModel R).eI U a b t ht

/-- Cohomology of the underlying complex.
Source: Stacks, Tag 012P (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredModuleCohomology (R : Type u) [CommRing R] (n : ℤ) :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ ModuleCat.{u} R where
  obj U := U.obj.obj.homology n
  map f := HomologicalComplex.homologyMap f.hom.hom n
  map_id U := HomologicalComplex.homologyMap_id U.obj.obj n
  map_comp f g := HomologicalComplex.homologyMap_comp f.hom.hom g.hom.hom n

/-- The image step I^a_n inside ordinary cohomology.
Source: Stacks, Tag 012P (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredCohomologyImage (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) :
    Subobject (U.obj.obj.homology n) :=
  imageSubobject (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)

/-- Consecutive image steps are decreasing. Source: Stacks, Tag 012P,
filtration-cohomology equation (blueprint: def-kun-filtered-page-localization-data).
Proof (Step 5): the inclusion F^(a+1) -> U factors through F^a -> U. Apply cohomology;
the image of a composite is contained in the image of the second arrow. -/
theorem finiteFilteredCohomologyImage_succ_le (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) :
    finiteFilteredCohomologyImage R U (a + 1) n ≤ finiteFilteredCohomologyImage R U a n := by
  unfold finiteFilteredCohomologyImage
  simpa only [← HomologicalComplex.homologyMap_comp, Subobject.ofLE_arrow] using
    imageSubobject_comp_le
      (HomologicalComplex.homologyMap
        (Subobject.ofLE _ _ (U.obj.filtration.F_succ_le a)) n)
      (HomologicalComplex.homologyMap (U.obj.filtration.step a).arrow n)

/-- The actual decreasing image filtration on cohomology, constructed from its inclusions.
Source: Stacks, Tag 012P (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredCohomologyFiltration (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (n : ℤ) :
    DecreasingFiltration (U.obj.obj.homology n) where
  F a := finiteFilteredCohomologyImage R U a n
  F_succ_le a := finiteFilteredCohomologyImage_succ_le R U a n

/-- The cohomology functor with its full image filtration; maps use the canonical image map.
Source: Stacks, Tags 012O and 012P (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredCohomology (R : Type u) [CommRing R] (n : ℤ) :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ FilteredObject (ModuleCat.{u} R) where
  obj U := ⟨U.obj.obj.homology n, finiteFilteredCohomologyFiltration R U n⟩
  map {U V} f :=
    { hom := HomologicalComplex.homologyMap f.hom.hom n
      preserves := fun a ↦ by
        let sq : Arrow.mk (HomologicalComplex.homologyMap
            (U.obj.filtration.step a).arrow n) ⟶
            Arrow.mk (HomologicalComplex.homologyMap (V.obj.filtration.step a).arrow n) :=
          Arrow.homMk (HomologicalComplex.homologyMap
            (FilteredObject.restrictionSteps f.hom a) n)
            (HomologicalComplex.homologyMap f.hom.hom n) (by
              dsimp only [Arrow.mk_hom]
              rw [← HomologicalComplex.homologyMap_comp,
                ← HomologicalComplex.homologyMap_comp]
              congr 1
              exact Classical.choose_spec (f.hom.preserves a))
        exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩ }
  map_id U := by
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_id U.obj.obj n
  map_comp f g := by
    change FilteredObject.Hom.mk _ _ = FilteredObject.Hom.mk _ _
    congr 1
    exact HomologicalComplex.homologyMap_comp f.hom.hom g.hom.hom n

/-- Forget the filtration of a module.
Source: Stacks, Tag 012P (blueprint: def-kun-filtered-page-localization-data). -/
def finiteFilteredCohomologyForget (R : Type u) [CommRing R] :
    FilteredObject (ModuleCat.{u} R) ⥤ ModuleCat.{u} R where
  obj U := U.obj
  map f := f.hom

/-- Forget the filtration of a complex.
Source: Stacks, Tag 05S3 (blueprint: def-kun-filtered-page-localization-data). -/
def finiteFilteredComplexForget (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj U := U.obj.obj
  map f := f.hom.hom

/-- The functor from filtered complexes to D_f(R).
Source: Stacks, Tag 05S2 (blueprint: def-kun-filtered-page-localization-data). -/
def finiteFilteredDerivedQuotient (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤ finiteFilteredModuleDerivedCategory R :=
  CochainComplex.finiteFilteredModuleHomotopyQuotient R ⋙
    finiteFilteredModuleLocalizationFunctor R

/-- The standard chosen derived category of modules; no extra size hypothesis is required.
Source: Stacks, Tag 05RU (blueprint: def-kun-filtered-page-localization-data). -/
abbrev finiteFilteredOrdinaryDerivedCategory (R : Type u) [CommRing R] :=
  @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)

/-- The ordinary derived localization for the standard chosen category.
Source: Stacks, Tag 05RU (blueprint: def-kun-filtered-page-localization-data). -/
abbrev finiteFilteredOrdinaryQ (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ finiteFilteredOrdinaryDerivedCategory R :=
  @DerivedCategory.Q (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)

/-- Ordinary derived cohomology in the standard chosen category.
Source: Stacks, Tag 05RU (blueprint: def-kun-filtered-page-localization-data). -/
abbrev finiteFilteredOrdinaryH (R : Type u) [CommRing R] (n : ℤ) :
    finiteFilteredOrdinaryDerivedCategory R ⥤ ModuleCat.{u} R :=
  @DerivedCategory.homologyFunctor (ModuleCat.{u} R) _ _
    (HasDerivedCategory.standard _) n

/-- The standard comparison between derived and cochain cohomology.
Source: Stacks, Tag 05RU (blueprint: def-kun-filtered-page-localization-data). -/
abbrev finiteFilteredOrdinaryHComparison (R : Type u) [CommRing R] (n : ℤ) :
    finiteFilteredOrdinaryQ R ⋙ finiteFilteredOrdinaryH R n ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n :=
  @DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) _ _
    (HasDerivedCategory.standard _) n

/-- The ambient quotient U/F^(a+1), formed from the inclusion into U.
Source: Stacks, Tag 012K (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredAmbientQuotient (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  cokernel (U.obj.filtration.step (a + 1)).arrow

/-- The actual chain map F^a U to U/F^(a+1), as opposed to the graded projection.
Source: Stacks, Tag 012K (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredAmbientMap (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ) :
    (U.obj.filtration.step a : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
      finiteFilteredAmbientQuotient R U a :=
  (U.obj.filtration.step a).arrow ≫ cokernel.π (U.obj.filtration.step (a + 1)).arrow

/-- The stationary image in H^n(U/F^(a+1)).
Source: Stacks, Tags 012K and 012W (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredQuotientImage (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a n : ℤ) : ModuleCat.{u} R :=
  image (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) n)

/-- The canonical map from the target quotient window to the ambient quotient.
Source: Stacks, Tag 012K (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredWindowToAmbient (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a t : ℤ) (ht : 1 ≤ t) :
    U.obj.filtration.complexQuotient (a - t + 1) (a + 1) (by omega) ⟶
      finiteFilteredAmbientQuotient R U a :=
  cokernel.desc _ ((U.obj.filtration.step (a - t + 1)).arrow ≫
    cokernel.π (U.obj.filtration.step (a + 1)).arrow) (by
      rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition])

/-- The map on ambient quotient complexes induced by a filtered chain map.
Source: Stacks, Tag 012O (blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredAmbientQuotientMap (R : Type u) [CommRing R]
    {U V : CochainComplex.FiniteFilteredModuleComplex R} (f : U ⟶ V) (a : ℤ) :
    finiteFilteredAmbientQuotient R U a ⟶ finiteFilteredAmbientQuotient R V a :=
  cokernel.map _ _ (FilteredObject.restrictionSteps f.hom (a + 1)) f.hom.hom
    (Classical.choose_spec (f.hom.preserves (a + 1))).symm

/-- Transport a descended functor map to its specified cochain representatives.
This is conjugation by the descent comparison, so it also handles localized morphisms
without chain-map representatives. Source: Stacks, Tag 04VK
(blueprint: def-kun-filtered-page-localization-data). -/
noncomputable def finiteFilteredDescendedMap (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C]
    (F : CochainComplex.FiniteFilteredModuleComplex R ⥤ C)
    (Fbar : finiteFilteredModuleDerivedCategory R ⥤ C)
    (e : finiteFilteredDerivedQuotient R ⋙ Fbar ≅ F)
    {U V : CochainComplex.FiniteFilteredModuleComplex R}
    (α : (finiteFilteredDerivedQuotient R).obj U ⟶
      (finiteFilteredDerivedQuotient R).obj V) : F.obj U ⟶ F.obj V :=
  e.inv.app U ≫ Fbar.map α ≫ e.hom.app V

/-- A stationary comparison is fixed by the core image square and by both representative
normalizations. The last two equations express x ↦ [x] mod I^(a+1) and its inverse, on
H^n(F^a U); composing with the epic cycles-to-cohomology map gives the literal cycle
formulation. Source: Stacks, Tags 012K, 012P and 012W
(blueprint: def-kun-filtered-page-localization-data). -/
structure FilteredPageStationaryComparison (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) where
  pageToImage : (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
    finiteFilteredQuotientImage R U a (a + b)
  core_normalization :
    pageToImage.hom ≫
        image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) =
      (finiteFilteredPageImageIso R U a b t ht).hom ≫
        image.ι (HomologicalComplex.homologyMap
          (finiteFilteredPageTransition R U a t ht) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredWindowToAmbient R U a t ht) (a + b)
  imageToGraded : finiteFilteredQuotientImage R U a (a + b) ≅
    (finiteFilteredCohomologyFiltration R U (a + b)).gradedPiece a
  representative_forward :
    factorThruImage (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a)
        (a + b)) ≫ imageToGraded.hom =
      factorThruImageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a))
  representative_inverse :
    factorThruImageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step a).arrow (a + b)) ≫
        cokernel.π (Subobject.ofLE _ _
          ((finiteFilteredCohomologyFiltration R U (a + b)).F_succ_le a)) ≫
        imageToGraded.inv =
      factorThruImage (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a)
        (a + b))

/-- Full descent and stationary-comparison data, with every map specified by its chain
representatives and the localization universal property. The fields use the existing
filtered-object category, so their step and graded maps are its canonical restrictions and
cokernel maps. Source: Stacks, Tags 012K, 012M, 012O, 012P, 012W, 05S2, 05S3 and 04VK
(blueprint: def-kun-filtered-page-localization-data). -/
structure FilteredPageLocalizationData (R : Type u) [CommRing R] where
  Sbar : finiteFilteredModuleDerivedCategory R ⥤
    CohomologicalSpectralSequence (ModuleCat.{u} R) 1
  eS : finiteFilteredDerivedQuotient R ⋙ Sbar ≅ finiteFilteredPageFunctor R
  Hbar : ℤ → finiteFilteredModuleDerivedCategory R ⥤ FilteredObject (ModuleCat.{u} R)
  eH : ∀ n : ℤ,
    finiteFilteredDerivedQuotient R ⋙ Hbar n ≅ finiteFilteredCohomology R n
  omega : finiteFilteredModuleDerivedCategory R ⥤ finiteFilteredOrdinaryDerivedCategory R
  eOmega : finiteFilteredDerivedQuotient R ⋙ omega ≅
    finiteFilteredComplexForget R ⋙ finiteFilteredOrdinaryQ R
  ordinaryCohomology : ∀ n : ℤ,
    Hbar n ⋙ finiteFilteredCohomologyForget R ≅ omega ⋙ finiteFilteredOrdinaryH R n
  ordinary_normalization : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (n : ℤ),
    (ordinaryCohomology n).hom.app ((finiteFilteredDerivedQuotient R).obj U) ≫
        (finiteFilteredOrdinaryH R n).map (eOmega.hom.app U) ≫
        (finiteFilteredOrdinaryHComparison R n).hom.app U.obj.obj =
      ((eH n).hom.app U).hom
  gradedDerived : ℤ → finiteFilteredModuleDerivedCategory R ⥤
    finiteFilteredOrdinaryDerivedCategory R
  gradedComparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ),
    (gradedDerived a).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
      (finiteFilteredOrdinaryQ R).obj (U.obj.filtration.gradedPiece a)
  graded_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a : ℤ),
    (gradedDerived a).map ((finiteFilteredDerivedQuotient R).map f) ≫
        (gradedComparison V a).hom =
      (gradedComparison U a).hom ≫
        (finiteFilteredOrdinaryQ R).map (FilteredObject.gradedMapSteps f.hom a)
  page_one : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V) (a b : ℤ),
    ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) Sbar eS α).hom 1).f
        (a, b) ≫ (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        (finiteFilteredOrdinaryHComparison R (a + b)).inv.app
          (U.obj.filtration.gradedPiece a) ≫
        (finiteFilteredOrdinaryH R (a + b)).map
          ((gradedComparison U a).inv ≫ (gradedDerived a).map α ≫
            (gradedComparison V a).hom) ≫
        (finiteFilteredOrdinaryHComparison R (a + b)).hom.app
          (V.obj.filtration.gradedPiece a)
  page_one_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a b : ℤ),
    (((finiteFilteredPageFunctor R).map f).hom 1).f (a, b) ≫
        (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps f.hom a) (a + b)
  homotopy_invariance : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f g : U ⟶ V), CochainComplex.finiteFilteredModuleHomotopyRel R f g →
    (finiteFilteredPageFunctor R).map f = (finiteFilteredPageFunctor R).map g ∧
    ∀ n : ℤ,
      HomologicalComplex.homologyMap f.hom.hom n =
        HomologicalComplex.homologyMap g.hom.hom n ∧
      (finiteFilteredCohomology R n).map f = (finiteFilteredCohomology R n).map g ∧
      ∀ a : ℤ,
        FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a =
          FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map g) a ∧
        FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map f) a =
          FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map g) a
  quasiIso_representatives : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V), CochainComplex.finiteFilteredModuleQuasiIso R
        ((CochainComplex.finiteFilteredModuleHomotopyQuotient R).map f) →
    QuasiIso f.hom.hom ∧
    (∀ a : ℤ, QuasiIso (FilteredObject.restrictionSteps f.hom a)) ∧
    ∀ n : ℤ,
      IsIso (HomologicalComplex.homologyMap f.hom.hom n) ∧
      IsIso ((finiteFilteredCohomology R n).map f) ∧
      ∀ a : ℤ,
        IsIso (FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a) ∧
        IsIso (FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map f) a)
  quasiIso_pages : ∀ {K L : CochainComplex.FiniteFilteredModuleHomotopy R}
      (w : K ⟶ L), CochainComplex.finiteFilteredModuleQuasiIso R w →
    IsIso (Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)) ∧
    ∀ (t : ℤ) (ht : 1 ≤ t),
      IsIso ((Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)).hom t ht)
  imageDerived : ℤ → ℤ → finiteFilteredModuleDerivedCategory R ⥤ ModuleCat.{u} R
  imageComparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ),
    (imageDerived a b).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
      finiteFilteredQuotientImage R U a (a + b)
  image_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a b : ℤ),
    (imageComparison U a b).inv ≫
        (imageDerived a b).map ((finiteFilteredDerivedQuotient R).map f) ≫
        (imageComparison V a b).hom ≫
        image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R V a) (a + b)) =
      image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientQuotientMap R f a) (a + b)
  bound : CochainComplex.FiniteFilteredModuleComplex R → ℤ → ℤ → ℤ
  stationary_window : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ), bound U a b ≤ t →
    U.obj.filtration.step (a + t) = ⊥ ∧ U.obj.filtration.step (a - t + 1) = ⊤
  comparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t), bound U a b ≤ t →
    FilteredPageStationaryComparison R U a b t ht
  stationary_naturality : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t) (hV : bound V a b ≤ t),
    ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) Sbar eS α).hom t ht).f
        (a, b) ≫ (comparison V a b t ht hV).pageToImage.hom =
      (comparison U a b t ht hU).pageToImage.hom ≫
        (imageComparison U a b).inv ≫ (imageDerived a b).map α ≫
          (imageComparison V a b).hom
  stationary_graded_naturality : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t) (hV : bound V a b ≤ t),
    (imageComparison U a b).inv ≫ (imageDerived a b).map α ≫
        (imageComparison V a b).hom ≫ (comparison V a b t ht hV).imageToGraded.hom =
      (comparison U a b t ht hU).imageToGraded.hom ≫
        FilteredObject.gradedMapSteps
          (finiteFilteredDescendedMap R (finiteFilteredCohomology R (a + b))
            (Hbar (a + b)) (eH (a + b)) α) a
  successor_agreement : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t),
    (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
        (comparison U a b t ht hU).pageToImage.hom =
      (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
        (comparison U a b (t + 1) (by omega) (by omega)).pageToImage.hom
  successor_graded_agreement : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t),
    (comparison U a b t ht hU).imageToGraded =
      (comparison U a b (t + 1) (by omega) (by omega)).imageToGraded

-- Avoid unused injectivity lemmas for these large dependent witness records.
set_option genInjectivity false in
/-- The descent part of filtered-page localization, before stationary comparisons.
Source: Stacks Project, Tags 05S2 and 05S3.
(blueprint: def-kun-filtered-page-localization-data). -/
structure FilteredPageDescentData (R : Type u) [CommRing R] where
  Sbar : finiteFilteredModuleDerivedCategory R ⥤
    CohomologicalSpectralSequence (ModuleCat.{u} R) 1
  eS : finiteFilteredDerivedQuotient R ⋙ Sbar ≅ finiteFilteredPageFunctor R
  Hbar : ℤ → finiteFilteredModuleDerivedCategory R ⥤ FilteredObject (ModuleCat.{u} R)
  eH : ∀ n : ℤ,
    finiteFilteredDerivedQuotient R ⋙ Hbar n ≅ finiteFilteredCohomology R n
  omega : finiteFilteredModuleDerivedCategory R ⥤ finiteFilteredOrdinaryDerivedCategory R
  eOmega : finiteFilteredDerivedQuotient R ⋙ omega ≅
    finiteFilteredComplexForget R ⋙ finiteFilteredOrdinaryQ R
  ordinaryCohomology : ∀ n : ℤ,
    Hbar n ⋙ finiteFilteredCohomologyForget R ≅ omega ⋙ finiteFilteredOrdinaryH R n
  ordinary_normalization : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (n : ℤ),
    (ordinaryCohomology n).hom.app ((finiteFilteredDerivedQuotient R).obj U) ≫
        (finiteFilteredOrdinaryH R n).map (eOmega.hom.app U) ≫
        (finiteFilteredOrdinaryHComparison R n).hom.app U.obj.obj =
      ((eH n).hom.app U).hom
  gradedDerived : ℤ → finiteFilteredModuleDerivedCategory R ⥤
    finiteFilteredOrdinaryDerivedCategory R
  gradedComparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (a : ℤ),
    (gradedDerived a).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
      (finiteFilteredOrdinaryQ R).obj (U.obj.filtration.gradedPiece a)
  graded_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a : ℤ),
    (gradedDerived a).map ((finiteFilteredDerivedQuotient R).map f) ≫
        (gradedComparison V a).hom =
      (gradedComparison U a).hom ≫
        (finiteFilteredOrdinaryQ R).map (FilteredObject.gradedMapSteps f.hom a)
  page_one : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V) (a b : ℤ),
    ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) Sbar eS α).hom 1).f
        (a, b) ≫ (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        (finiteFilteredOrdinaryHComparison R (a + b)).inv.app
          (U.obj.filtration.gradedPiece a) ≫
        (finiteFilteredOrdinaryH R (a + b)).map
          ((gradedComparison U a).inv ≫ (gradedDerived a).map α ≫
            (gradedComparison V a).hom) ≫
        (finiteFilteredOrdinaryHComparison R (a + b)).hom.app
          (V.obj.filtration.gradedPiece a)
  page_one_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a b : ℤ),
    (((finiteFilteredPageFunctor R).map f).hom 1).f (a, b) ≫
        (finiteFilteredPageFirstIso R V a b).hom =
      (finiteFilteredPageFirstIso R U a b).hom ≫
        HomologicalComplex.homologyMap (FilteredObject.gradedMapSteps f.hom a) (a + b)
  homotopy_invariance : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f g : U ⟶ V), CochainComplex.finiteFilteredModuleHomotopyRel R f g →
    (finiteFilteredPageFunctor R).map f = (finiteFilteredPageFunctor R).map g ∧
    ∀ n : ℤ,
      HomologicalComplex.homologyMap f.hom.hom n =
        HomologicalComplex.homologyMap g.hom.hom n ∧
      (finiteFilteredCohomology R n).map f = (finiteFilteredCohomology R n).map g ∧
      ∀ a : ℤ,
        FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a =
          FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map g) a ∧
        FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map f) a =
          FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map g) a
  quasiIso_representatives : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V), CochainComplex.finiteFilteredModuleQuasiIso R
        ((CochainComplex.finiteFilteredModuleHomotopyQuotient R).map f) →
    QuasiIso f.hom.hom ∧
    (∀ a : ℤ, QuasiIso (FilteredObject.restrictionSteps f.hom a)) ∧
    ∀ n : ℤ,
      IsIso (HomologicalComplex.homologyMap f.hom.hom n) ∧
      IsIso ((finiteFilteredCohomology R n).map f) ∧
      ∀ a : ℤ,
        IsIso (FilteredObject.restrictionSteps ((finiteFilteredCohomology R n).map f) a) ∧
        IsIso (FilteredObject.gradedMapSteps ((finiteFilteredCohomology R n).map f) a)
  quasiIso_pages : ∀ {K L : CochainComplex.FiniteFilteredModuleHomotopy R}
      (w : K ⟶ L), CochainComplex.finiteFilteredModuleQuasiIso R w →
    IsIso (Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)) ∧
    ∀ (t : ℤ) (ht : 1 ≤ t),
      IsIso ((Sbar.map ((finiteFilteredModuleLocalizationFunctor R).map w)).hom t ht)

-- Avoid unused injectivity lemmas for these large dependent witness records.
set_option genInjectivity false in
/-- The normalized stationary comparison part, relative to fixed descended functors.
Source: Stacks Project, Tags 012K, 012P and 012W.
(blueprint: def-kun-filtered-page-localization-data). -/
structure FilteredPageStationaryData (R : Type u) [CommRing R]
    (d : FilteredPageDescentData R) where
  imageDerived : ℤ → ℤ → finiteFilteredModuleDerivedCategory R ⥤ ModuleCat.{u} R
  imageComparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ),
    (imageDerived a b).obj ((finiteFilteredDerivedQuotient R).obj U) ≅
      finiteFilteredQuotientImage R U a (a + b)
  image_chain : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (f : U ⟶ V) (a b : ℤ),
    (imageComparison U a b).inv ≫
        (imageDerived a b).map ((finiteFilteredDerivedQuotient R).map f) ≫
        (imageComparison V a b).hom ≫
        image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R V a) (a + b)) =
      image.ι (HomologicalComplex.homologyMap (finiteFilteredAmbientMap R U a) (a + b)) ≫
        HomologicalComplex.homologyMap (finiteFilteredAmbientQuotientMap R f a) (a + b)
  bound : CochainComplex.FiniteFilteredModuleComplex R → ℤ → ℤ → ℤ
  stationary_window : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ), bound U a b ≤ t →
    U.obj.filtration.step (a + t) = ⊥ ∧ U.obj.filtration.step (a - t + 1) = ⊤
  comparison : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t), bound U a b ≤ t →
    FilteredPageStationaryComparison R U a b t ht
  stationary_naturality : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t) (hV : bound V a b ≤ t),
    ((finiteFilteredDescendedMap R (finiteFilteredPageFunctor R) d.Sbar d.eS α).hom t ht).f
        (a, b) ≫ (comparison V a b t ht hV).pageToImage.hom =
      (comparison U a b t ht hU).pageToImage.hom ≫
        (imageComparison U a b).inv ≫ (imageDerived a b).map α ≫
          (imageComparison V a b).hom
  stationary_graded_naturality : ∀ {U V : CochainComplex.FiniteFilteredModuleComplex R}
      (α : (finiteFilteredDerivedQuotient R).obj U ⟶
        (finiteFilteredDerivedQuotient R).obj V)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t) (hV : bound V a b ≤ t),
    (imageComparison U a b).inv ≫ (imageDerived a b).map α ≫
        (imageComparison V a b).hom ≫ (comparison V a b t ht hV).imageToGraded.hom =
      (comparison U a b t ht hU).imageToGraded.hom ≫
        FilteredObject.gradedMapSteps
          (finiteFilteredDescendedMap R (finiteFilteredCohomology R (a + b))
            (d.Hbar (a + b)) (d.eH (a + b)) α) a
  successor_agreement : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t),
    (((finiteFilteredPageFunctor R).obj U).page t ht).iCycles (a, b) ≫
        (comparison U a b t ht hU).pageToImage.hom =
      (((finiteFilteredPageFunctor R).obj U).page t ht).homologyπ (a, b) ≫
        (((finiteFilteredPageFunctor R).obj U).iso t (t + 1) (a, b) rfl ht).hom ≫
        (comparison U a b (t + 1) (by omega) (by omega)).pageToImage.hom
  successor_graded_agreement : ∀ (U : CochainComplex.FiniteFilteredModuleComplex R)
      (a b t : ℤ) (ht : 1 ≤ t) (hU : bound U a b ≤ t),
    (comparison U a b t ht hU).imageToGraded =
      (comparison U a b (t + 1) (by omega) (by omega)).imageToGraded

end CategoryTheory
