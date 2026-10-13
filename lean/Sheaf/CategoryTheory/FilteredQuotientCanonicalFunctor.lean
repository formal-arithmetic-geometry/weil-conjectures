/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential
import Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover
import Sheaf.CategoryTheory.FilteredComplexSuccessorBoundariesImage

/-!
# Functorial canonical quotient pages

Source: Stacks Project, Tag 012K, Lemmas 12.24.2 and 12.24.4.
(blueprint: lem-sp-filtered-quotient-canonical-functor).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

/-- Construct a functor on the concrete quotient pages with their representative differentials.
Source: Stacks Project, Tag 012K, Lemmas 12.24.2 and 12.24.4.
(blueprint: lem-sp-filtered-quotient-canonical-functor).

Proof. At each positive r use the cokernels Z_r/B_r and the given D differential.
The representative equation uniquely specifies D, so it is the differential induced
by the original complex. The kernel computation identifies the graded image of
successor cycles with ker d_r; the incoming image is the successor boundaries.
Their quotient gives the canonical homology comparison to Z_(r+1)/B_(r+1).
Choose this comparison by its equation on successor representatives, rather than
an arbitrary isomorphism. These comparisons assemble the spectral sequence.
A filtered map restricts to each step: its preservation property supplies the
restriction and the monic step inclusion makes it unique. Cokernel descent gives
its graded map. The cycle pullback and image formulas give its cycle restriction;
the boundary formula shows it descends to Z_r/B_r. Precomposing with an epic
representative cover proves commutation with D, since the original chain map
commutes with d. Applying the same argument to successor cycles proves commutation
with the canonical homology comparisons, giving a spectral-sequence morphism.
Uniqueness after the monic cycle inclusion and epic quotient projection proves
identity and composition. Thus these maps form the required functor. Any s,g,kz,k
in the displayed squares agrees with these maps by those same cancellation
arguments, which proves the asserted naturality. The page comparisons are identity
isomorphisms up to proof irrelevance of the specified boundary inclusions. -/
theorem filteredQuotient_canonical_functor
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (D : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (r : ℤ) (hr : 1 ≤ r),
      FilteredComplexPageDifferential U.obj.obj U.obj.filtration r) :
    ∃ (S : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (eZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).X (p, q) ≅ cokernel (Subobject.ofLE _ _ (hBZ U p q r hr))),
      (∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
        (p q p' q' r : ℤ) (hr : 1 ≤ r),
        ((S.obj U).page r hr).d (p, q) (p', q') ≫ (eZ U p' q' r hr).hom =
          (eZ U p q r hr).hom ≫ (D U r hr).d (p, q) (p', q')) ∧
      (∀ (U V : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (t : U ⟶ V)
        (p q r : ℤ) (hr : 1 ≤ r)
      (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
        (V.obj.filtration.step a : CochainComplex C ℤ))
      (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
      (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
        (V.obj.filtration.complexCycles p (p + q) r : C))
      (k : cokernel (Subobject.ofLE _ _ (hBZ U p q r hr)) ⟶
        cokernel (Subobject.ofLE _ _ (hBZ V p q r hr)))
      (hs : ∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
        (U.obj.filtration.step i).arrow ≫ t.hom.hom)
      (hg : U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
        s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega))
      (hkz : kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
        (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q))
      (hk : cokernel.π (Subobject.ofLE _ _ (hBZ U p q r hr)) ≫ k =
        kz ≫ cokernel.π (Subobject.ofLE _ _ (hBZ V p q r hr))),
        ((S.map t).hom r hr).f (p, q) ≫ (eZ V p q r hr).hom =
          (eZ U p q r hr).hom ≫ k) := by sorry

end CategoryTheory
