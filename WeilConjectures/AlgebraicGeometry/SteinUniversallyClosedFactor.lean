/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Universal factorization before Stein connectedness

## Implementation details

The relative-spectrum clause is expressed by the canonical algebra identification
`s_* O ≅ f_* O`, obtained by pushing forward `q.c` along the integral (hence affine) map `s`.
An affine scheme with this algebra identification is exactly the relative spectrum, by the
anti-equivalence between affine morphisms and quasi-coherent algebras. For a flat base change,
two Cartesian squares specify the base-changed factorization. These are identifications of
algebras through the canonical sharp maps, rather than arbitrary isomorphisms of ring sheaves.

## References

* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01LW](https://stacks.math.columbia.edu/tag/01LW)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Stein factorization properties for a universally closed, quasi-separated morphism to an
affine scheme: the canonical map `q.c` is invertible, the intermediate scheme is the relative
spectrum of `f_* O` (via the identification `s_* O ≅ f_* O`), and the same holds after every
flat base change. -/
theorem stein_universally_closed_factor
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [UniversallyClosed f] [QuasiSeparated f] :
    UniversallyClosed X.toSpecΓ ∧
      QuasiCompact X.toSpecΓ ∧
      QuasiSeparated X.toSpecΓ ∧
      Surjective X.toSpecΓ ∧
      IsIntegralHom f.steinFactorizationBase ∧
      IsIso X.toSpecΓ.c ∧
      IsIso ((TopCat.Sheaf.pushforward CommRingCat.{u} f.steinFactorizationBase.base).map
        (⟨X.toSpecΓ.c⟩ : Scheme.sheaf (Spec Γ(X, ⊤)) ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} X.toSpecΓ.base).obj (Scheme.sheaf X))) ∧
      (∀ (T B' X' : Scheme.{u}) (g : T ⟶ Spec A) (_ : Flat g)
        (b : B' ⟶ Spec Γ(X, ⊤)) (s' : B' ⟶ T) (x : X' ⟶ X) (q' : X' ⟶ B'),
        IsPullback b s' f.steinFactorizationBase g →
        IsPullback x q' X.toSpecΓ b →
        IsIso ((TopCat.Sheaf.pushforward CommRingCat.{u} s'.base).map
          (⟨q'.c⟩ : Scheme.sheaf B' ⟶
            (TopCat.Sheaf.pushforward CommRingCat.{u} q'.base).obj (Scheme.sheaf X')))) := by
  have hcomp : UniversallyClosed (X.toSpecΓ ≫ f.steinFactorizationBase) := by
    simpa using (inferInstance : UniversallyClosed f)
  have huc : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated _ f.steinFactorizationBase
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hqc : QuasiCompact X.toSpecΓ := inferInstance
  have hqs : QuasiSeparated X.toSpecΓ := inferInstance
  have hsurj : Surjective X.toSpecΓ :=
    surjective_of_isDominant_of_isClosed_range _ X.toSpecΓ.isClosedMap.isClosed_range
  have hint : IsIntegralHom f.steinFactorizationBase := by
    rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom]
    exact ⟨UniversallyClosed.of_comp_surjective X.toSpecΓ _, inferInstance⟩
  let φ : Scheme.sheaf (Spec Γ(X, ⊤)) ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} X.toSpecΓ.base).obj (Scheme.sheaf X) :=
    ⟨X.toSpecΓ.c⟩
  have hφ : IsIso φ := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    intro a
    exact inferInstanceAs (IsIso (X.toSpecΓ.app (PrimeSpectrum.basicOpen a)))
  have hsharp : IsIso X.toSpecΓ.c :=
    (TopCat.Sheaf.forget _ _).map_isIso φ
  refine ⟨huc, hqc, hqs, hsurj, hint, hsharp, inferInstance, ?_⟩
  intro T B' X' g hg b s' x q' hs hq
  have : Flat b := MorphismProperty.of_isPullback (P := @Flat) hs.flip inferInstance
  let φ' : Scheme.sheaf B' ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} q'.base).obj (Scheme.sheaf X') := ⟨q'.c⟩
  have : IsIso φ' := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun W : B'.affineOpens ↦ W.1)
    · simpa only [Subtype.range_coe] using B'.isBasis_affineOpens
    intro W
    change IsIso (q'.app W.1)
    let hbt : W.1 ≤ b ⁻¹ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) := by simp
    let hqt : (⊤ : X.Opens) ≤ X.toSpecΓ ⁻¹ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) := by simp
    let hy : q' ⁻¹ᵁ W.1 = x ⁻¹ᵁ (⊤ : X.Opens) ⊓ q' ⁻¹ᵁ W.1 := by simp
    have hp : IsIso (pushoutSection hq hbt hqt hy) :=
      isIso_pushoutSection_of_isQuasiSeparated_of_flat_right hq hbt hqt hy
        (isAffineOpen_top _) W.2 isCompact_univ isQuasiSeparated_univ
    have : IsIso (X.toSpecΓ.appLE ⊤ ⊤ hqt) := by
      rw [Scheme.Hom.appLE_top_top, Scheme.toSpecΓ_appTop]
      infer_instance
    have he : pushout.inr (X.toSpecΓ.appLE ⊤ ⊤ hqt) (b.appLE ⊤ W.1 hbt) ≫
        pushoutSection hq hbt hqt hy = q'.app W.1 := by
      simp only [pushoutSection, pushout.inr_desc, Scheme.Hom.appLE_eq_app]
    rw [← he]
    infer_instance
  exact (TopCat.Sheaf.pushforward CommRingCat.{u} s'.base).map_isIso φ'

end AlgebraicGeometry
