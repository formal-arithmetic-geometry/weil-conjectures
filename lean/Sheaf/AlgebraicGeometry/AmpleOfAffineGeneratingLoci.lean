/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase
import Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple

/-!
# Ampleness from affine nonvanishing loci

Source: Stacks Project, Properties, Definition 28.27.1 (Tag 01PS), and Morphisms,
Lemma 29.40.4 (Tag 01VT) (blueprint: lem-pc-ample-affine-loci-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
