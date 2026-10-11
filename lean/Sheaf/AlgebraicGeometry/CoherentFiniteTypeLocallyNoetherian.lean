/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coherence on locally Noetherian schemes

Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.1, Tag 01XZ
(blueprint: pqf-lem-coherent-ft-locnoeth).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On a locally Noetherian scheme, an `𝒪_X`-module is coherent exactly when it is
quasi-coherent and of finite type.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.1, Tag 01XZ
(blueprint: pqf-lem-coherent-ft-locnoeth).

Proof:
1. If `F` is coherent, its finite-type clause gives local finite free surjections onto `F`.
   Applying the kernel clause gives finite-type relations, hence local finite presentations.
   The affine finite-type criterion (lem-weil-pbc-quasi-coherent-finite-type-affine) then
   gives quasi-coherence; finite type is retained from the coherent hypothesis.
2. Conversely, suppose `F` is quasi-coherent and finite type. For a map from a finite free
   module on an open `U` to `F|_U`, the source is quasi-coherent: on affine opens it is
   the tilde of a finite free module, by lem-weil-pbc-affine-tilde-gamma-adjunction (4).
   Its kernel is quasi-coherent by
   lem-weil-pbc-quasi-coherent-module-kernel. On an affine open, the sections of `F` are a
   finite module by lem-weil-pbc-quasi-coherent-finite-type-affine, and the sections of the
   kernel are the kernel of a map from a finite free module. The ring is Noetherian by
   local Noetherianness and the Noetherian-ring definition, so this kernel is finitely
   generated: induct on the finite free rank, with zero kernel in rank zero; project to
   rank one less, lift generators of the image, and adjoin generators of the kernel
   of this projection, an ideal in the last coordinate. The affine criterion applied to the
   kernel makes it finite type; affine opens cover `U`, so the kernel is finite type.
   The defining coherent predicate follows.
-/
theorem isCoherent_iff_isQuasicoherent_and_isFiniteType
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules) :
    RingedSpace.IsCoherent X.toRingedSpace F ↔
      F.IsQuasicoherent ∧ F.IsFiniteType := by
  sorry

end AlgebraicGeometry.Scheme.Modules
