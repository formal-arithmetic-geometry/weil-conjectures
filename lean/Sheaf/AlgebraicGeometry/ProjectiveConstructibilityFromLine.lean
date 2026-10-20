/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation
import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp
import Sheaf.AlgebraicGeometry.NoetherianSymmetricProductFiniteSurjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct

/-!
# Projective constructibility from the projective line

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-projective-from-line.md`
(blueprint: lem-finrepair-projective-from-line).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- If every projective-line projection over a finite-type `k`-scheme satisfies `C`,
then every projective morphism between finite-type `k`-schemes satisfies `C`.
All coefficient-bearing schemes satisfy the fixed coefficient convention.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-projective-from-line.md`
(blueprint: lem-finrepair-projective-from-line).

Proof plan:
1. Choose the global closed embedding into projective space supplied by
   `def-pc-projective-morphism`.
2. The standard relative-Proj charts are polynomial rings in coordinate ratios.
   Thus projective spaces and successive projective-line bundles are finite type;
   the base-change presentation identifies the latter with products of projective lines.
3. A finite-type scheme over a field is Noetherian, by
   `lem-weil-pbc-finite-type-over-noetherian`.
4. Induct on the number of projective-line factors, starting with the exact identity
   direct image, and use `lem-finrepair-composition-c` at each successor step.
   Zero sheaves are constructible by `def-weil-pbc-constructible-complexes`.
5. For positive dimension the finite surjective symmetric-product map of
   `lem-fin-symmetric-product-finite`, followed by
   `lem-finrepair-finite-surjection-cancellation`, gives `C` for projective space.
   Dimension zero is the identity case.
6. `lem-fin-closed-immersion` gives constructibility and positive-degree vanishing for
   the closed embedding; compose with the projective-space projection using
   `lem-finrepair-composition-c`. -/
theorem hasConstructibleHigherDirectImages_of_projectiveLine
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hline : ∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      (hP : IsSmoothBaseChangeCoefficients N Λ (ProjectiveSpace (ULift.{u} (Fin 2)) T))
      (hT : IsSmoothBaseChangeCoefficients N Λ T),
      @HasConstructibleHigherDirectImages k _ N Λ _ _
        (ProjectiveSpace (ULift.{u} (Fin 2)) T) T _ _
        (inferInstanceAs (LocallyOfFiniteType
          ((ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T) ≫ T ↘ Spec (.of k))))
        (inferInstanceAs (QuasiCompact
          ((ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T) ≫ T ↘ Spec (.of k))))
        _ _ hP hT (ProjectiveSpace (ULift.{u} (Fin 2)) T ↘ T))
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProjective f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  sorry

end AlgebraicGeometry.Etale
