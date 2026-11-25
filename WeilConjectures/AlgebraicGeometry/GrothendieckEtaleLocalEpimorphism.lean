/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImageSheaf
import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleLocalImageDetection

/-! # Local lifting families for general Grothendieck coefficients

## Implementation details

The categorical formulation is an explicit coefficient generalization of the argument for sheaves.

## References

* [Stacks Project, Tags 00WL, 01H0]
-/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

omit [CompactSpace X] [QuasiSeparatedSpace X] in
private lemma localImage_eq_top_of_isSheaf
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (hs : Presheaf.IsSheaf X.smallEtaleTopology (qcqsLocalImagePresheaf p))
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    localImage p W = ⊤ := by
  let L : Sheaf X.smallEtaleTopology A := ⟨qcqsLocalImagePresheaf p, hs⟩
  let i : L ⟶ G := ⟨qcqsLocalImageι p⟩
  let q : F ⟶ L := ⟨toQcqsLocalImage p⟩
  have hi : q ≫ i = p := by
    apply Sheaf.hom_ext
    exact toQcqsLocalImage_ι p
  have : Epi i := epi_of_epi_fac hi
  have (Z : X.Etaleᵒᵖ) : Mono (i.hom.app Z) :=
    inferInstanceAs (Mono (qcqsLocalImage p Z.unop).arrow)
  have : Mono i.hom := NatTrans.mono_of_mono_app _
  have : Mono ((sheafToPresheaf X.smallEtaleTopology A).map i) := ‹Mono i.hom›
  have : Mono i := (sheafToPresheaf X.smallEtaleTopology A).mono_of_mono_map inferInstance
  have : IsIso i := isIso_of_mono_of_epi i
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology A).map i) := inferInstance
  have : IsIso i.hom := this
  have : IsIso ((qcqsLocalImage p W).arrow) :=
    inferInstanceAs (IsIso (i.hom.app (op W)))
  exact (qcqsLocalImage_eq p W).symm.trans (Subobject.eq_top_of_isIso_arrow _)

set_option linter.unusedSectionVars false in
/-- Maps admitting local lifts through a sheaf epimorphism jointly detect zero maps.
This is the categorical finite-cover version for Grothendieck abelian coefficients.
(Stacks, Tags 00WL and 01H0) -/
theorem eq_zero_of_locally_liftable_maps
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T)
    (hkill : ∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) : g = 0 := by
  have htop : localImage p W = ⊤ :=
    localImage_eq_top_of_isSheaf A p (qcqsLocalImage_isSheaf A p) W
  apply eq_zero_of_factors_localImage A p W B T x g
  · rw [htop]
    exact Subobject.top_factors x
  · exact hkill

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
