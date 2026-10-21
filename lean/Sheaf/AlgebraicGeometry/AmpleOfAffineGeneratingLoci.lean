/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus

/-!
# Ampleness from affine nonvanishing loci

Source: Stacks Project, Properties, Definition 28.27.1 (Tag 01PS), and Morphisms,
Lemma 29.40.4 (Tag 01VT) (blueprint: lem-pc-ample-affine-loci-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem positiveTensorPower_iso_tensorPow (X : Scheme.{u}) (L : X.Modules) :
    ∀ (d : ℕ) (hd : 0 < d),
      Nonempty (SheafOfModules.positiveTensorPower X.sheaf L d hd ≅ L.tensorPow d) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  intro d
  induction d using Nat.twoStepInduction with
  | zero => intro hd; omega
  | one =>
    intro hd
    exact ⟨(MonoidalCategoryStruct.rightUnitor L).symm⟩
  | more d _ ih' =>
    intro hd
    obtain ⟨e⟩ := ih' (by omega)
    exact ⟨MonoidalCategory.tensorIso e (Iso.refl L) ≪≫ BraidedCategory.braiding _ _⟩

/-- On a proper scheme over a field, an invertible module is ample if every point lies in an
affine nonvanishing locus of a section of some positive tensor power.

Source: Stacks Project, Properties, Definition 28.27.1 (Tag 01PS), and Morphisms,
Lemma 29.40.4 (Tag 01VT) (blueprint: lem-pc-ample-affine-loci-criterion).

Properness gives finite type and quasi-compactness, so the affine generating loci give
absolute ampleness by Tag 01PS. Tag 01VT then gives an immersion into projective space
for some positive tensor power. Projective space is separated, so properness makes this
immersion closed. The coordinate sections give a finite subsystem with a closed immersion;
the complete-linear-system lemma extends this to all global sections. Thus the positive
tensor power is very ample and the original module is ample. -/
theorem isAmple_of_affine_generatingLoci {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (L : X.Modules) (hproper : IsProper f)
    (hL : L.IsInvertible)
    (h : ∀ x : X, ∃ (n : ℕ) (s : Γ(L.tensorPow n, ⊤)),
      0 < n ∧ x ∈ Scheme.Modules.generatingLocus s ∧
        IsAffineOpen (Scheme.Modules.generatingLocus s)) : IsAmple f L := by
  classical
  have : IsProper f := hproper
  have : L.IsInvertible := hL
  have hcompact : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have habs : Scheme.Modules.IsAmple X L := by
    refine ⟨hcompact, fun x ↦ ?_⟩
    obtain ⟨n, s, hn, hx, ha⟩ := h x
    refine ⟨n, hn, s, Scheme.Modules.generatingLocus s, hx, ha, fun y ↦ ?_⟩
    exact (Scheme.Modules.mem_nonvanishingLocus_iff_generatesAt (L.tensorPow n) s y).symm
  obtain ⟨d, hd, n, i, hi, hif, ⟨e⟩⟩ :=
    Scheme.Modules.IsAmple.exists_immersion_affine_base K X f L habs
  have : IsImmersion i := hi
  have : IsProper (i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K)) :=
    hif.symm ▸ hproper
  have : IsProper i :=
    IsProper.of_comp i (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of K)) ↘ Spec (.of K))
  have hclosed : IsClosedImmersion i :=
    IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range
  obtain ⟨epow⟩ := positiveTensorPower_iso_tensorPow X L d hd
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction i
  let epb := (adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction i)).app
    (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of K)) 1)
  exact ⟨hL, d, hd, ULift.{u} (Fin (n + 1)), i, inferInstance, hclosed, hif,
    ⟨epb.symm ≪≫ e.symm ≪≫ epow⟩⟩

end AlgebraicGeometry
