/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Universal factorization before Stein connectedness

Source: Stacks Project, More on Morphisms, Lemma 37.53.4 (Tag 03GY)
(blueprint: `lem-weil-pbc-stein-universally-closed-factor`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Universal-closed Stein factorization properties from Stacks, Tag 03GY.
(blueprint: lem-weil-pbc-stein-universally-closed-factor)

The structure-sheaf identity means that the canonical map `q.c` is invertible.
The relative-spectrum clause is expressed by the canonical algebra identification
`s_* O ≅ f_* O`: push forward `q.c` along the integral (hence affine) map `s`.
An affine scheme with this algebra identification is exactly the relative spectrum,
by the affine/quasi-coherent-algebra anti-equivalence (Stacks 01S8, 01SA, 01LW).
For every flat base change, two Cartesian squares specify the base-changed factorization;
the same canonical algebra identification asserts that its intermediate scheme is the
relative spectrum of the new pushforward. Thus these are identifications of algebras
through the canonical sharp maps, rather than arbitrary isomorphisms of ring sheaves.

Proof:
1. Universal closedness makes f quasi-compact
   (`lem-weil-pbc-qcqs-morphism-permanence`). Relative normalization
   (`lem-weil-pbc-relative-normalization`) and integrality of global sections
   (`lem-weil-pbc-universally-closed-global-sections-integral`) identify the normalization
   with Spec B and make s integral, with its relative-spectrum description.
2. The image lemma (`lem-weil-pbc-image-universally-closed`) makes q universally closed.
   Composition permanence (`lem-weil-pbc-qcqs-morphism-permanence`) makes it qcqs.
3. Pushforward preserves quasi-coherence (`pqf-lem-pushforward-qcoh`). The affine
   tilde/global-sections equivalence (`lem-weil-pbc-affine-tilde-gamma-adjunction`)
   identifies q_* O with O since their global sections are B and the map is the identity.
4. The closed image is V(I). Each h in I vanishes in every residue field of X, so is
   nilpotent (`lem-weil-pbc-qc-scheme-vanishing-section-nilpotent`). As pullback identifies
   B with global sections, I is nil and V(I) is all of Spec B: q is surjective.
5. Flat base change identifies the new pushforward algebra with the pulled-back algebra
   (`lem-weil-pbc-stein-flat-base-change-global-sections`). Relative Spec commutes with
   base change (`lem-weil-pbc-relative-spec-base-change`), giving the canonical algebra
   identification for the base-changed factorization. -/
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
  sorry

end AlgebraicGeometry
