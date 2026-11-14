/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity

/-! # Filtered continuity for a constructible condensed module sheaf

Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(2).

The comparison is `colimit.desc` of the cocone obtained by localization, shifting, and
additive Hom from `M[0]`. Thus its legs are postcomposition with the shifted colimit legs.
Naturality in the first argument and diagrams is built into additive coyoneda and the
colimit construction; compatibility with shifts uses the same construction for every integer.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance localInst_CondensedSheafExtContinuity_1
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

local instance localInst_CondensedSheafExtContinuity_2
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) : HasColimit N := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I C := inferInstance
  have (n : ℤ) : HasColimit (N ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval N⟩⟩⟩

set_option maxHeartbeats 800000 in
-- Elaborating the derived-module cocone needs extra typeclass and definitional equality work.
/-- Derived Hom from a constructible condensed `E`-module sheaf commutes with a small
filtered colimit of complexes with a common termwise lower bound, in every integer shift
(Hemo--Richarz--Scholbach, Lemma 5.3(2)). -/
theorem isIso_constructible_condensed_sheaf_hom_colimit
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj M))).mapCocone
          (colimit.cocone N))) := by
  obtain ⟨r, hr⟩ := exists_condensedConstructible_extension_tower T ℓ E M hM
  let D := N ⋙ DerivedCategory.Q
  let c := DerivedCategory.Q.mapCocone (colimit.cocone N)
  have hP : condensedConstructiblePiece T ℓ E ≤ homColimitProperty D c :=
    condensed_local_piece_hom_continuity T ℓ E N hN
  have h : ∀ r : ℕ, (condensedConstructiblePiece T ℓ E).extensionProductIter r ≤
      homColimitProperty D c := by
    intro r
    induction r with
    | zero => exact hP
    | succ r ih =>
      rw [ObjectProperty.extensionProductIter_succ]
      rintro K ⟨A, B, f, g, k, hdist, hA, hB⟩
      exact homColimitProperty_extensions D c _ hdist (hP _ hA) (ih _ hB)
  exact h r _ hr n

end AlgebraicGeometry.ProEtale
