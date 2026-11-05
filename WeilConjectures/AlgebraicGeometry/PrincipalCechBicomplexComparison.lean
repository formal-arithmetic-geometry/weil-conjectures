/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
public import Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.AlgebraicGeometry.PrincipalCechHorizontalSquare
import WeilConjectures.AlgebraicGeometry.PrincipalCechRegroupDifferential
import WeilConjectures.AlgebraicGeometry.PrincipalCechRegroupNaturality

/-! # The explicit Čech bicomplex and its total comparison

Source: Stacks, Tag 08D1, total differential of the alternating Čech double complex
(blueprint: lem-sc-principal-cech-bicomplex-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

end
end AlgebraicGeometry
