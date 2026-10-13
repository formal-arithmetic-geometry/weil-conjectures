/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent

/-! # Finite affine sections generating on a compact open

Source: Stacks Project, Properties, Lemma 01PF, finite-numerator step.
(blueprint: lem-weil-pbc-module-finite-type-affine-generators).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Finitely many sections on an affine open generate a quasi-coherent module on a
compact open where it is of finite type.

Source: Stacks Project, Properties, Lemma 01PF (label lemma-extend), final paragraph,
and Lemma 01PB (label lemma-finite-type-module).
https://stacks.math.columbia.edu/tag/01PF
(blueprint: lem-weil-pbc-module-finite-type-affine-generators).

Proof: Identify H on V with the associated sheaf of M = H(V) using the affine
counit isomorphism. Refine a finite-type generating cover on K by principal opens
D(f) inside K. The affine criterion identifies their modules of sections with
finitely generated localizations M_f. Compactness gives finitely many such opens.
For each of their finite generating families, write the generators as m/f^a and
collect the finitely many numerators m in M. Enumerate them by Fin n and map the
standard basis of the free module to these sections. On each chosen D(f), f is a
unit, so the numerators generate whenever the fractions do. The restriction of
this free-module map is therefore locally surjective on K, hence epimorphic.
Transport the map to the slice site Over V; the free-module comparison preserves
its standard basis. No submodule or monomorphism is asserted here. If K is empty,
use n = 0; every sheaf on the empty open is zero, so the restricted map is epi.
For K = V, finite generation gives the usual finite free surjection. -/
theorem exists_finiteType_affine_generators
    (X : Scheme.{u}) (V : X.affineOpens) (K : X.Opens)
    (hK : IsCompact (K : Set X)) (hKV : K ≤ V.1)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over K).IsFiniteType] :
    ∃ (n : ℕ) (φ : SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V.1) (ULift.{u} (Fin n)) ⟶ H.over V.1),
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hKV)).map φ) := by sorry

end AlgebraicGeometry.Scheme.Modules
