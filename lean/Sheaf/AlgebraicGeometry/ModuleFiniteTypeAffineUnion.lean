/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.Coherent

/-! # The finite-type submodule on the union with an affine open

Source: Stacks Project, Properties, Lemma 01PF, affine reduction and gluing.
(blueprint: lem-weil-pbc-module-finite-type-affine-union).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Construct the finite-type submodule on the union, before extending it to X.

Source: Stacks Project, Properties, Lemma 01PF, proof, affine reduction and gluing
(https://stacks.math.columbia.edu/tag/01PF).
(blueprint: lem-weil-pbc-module-finite-type-affine-union).

Proof: Quasi-separatedness makes the overlap W intersect V quasi-compact. Identify
H on V with the tilde of its sections. Finite type on W restricts to finite type on
this overlap. Choose a finite cover of the overlap by principal opens D(f_i) with
finitely generated localized modules of sections. Write finitely many generators
as fractions and span their numerators in H(V), obtaining a finitely generated
submodule N. Localization of N includes every chosen generator, so its inclusion
into H(V) becomes an isomorphism on each D(f_i). Tilde is exact, hence tilde N is
a quasi-coherent finite-type submodule on V agreeing with H on the overlap.
Glue this inclusion with the identity inclusion of H on W: sections on an open
of W union V are sections of H whose restrictions to V belong to tilde N.
The sheaf gluing axiom gives the prescribed restrictions and a monomorphism into
H on the union. Quasi-coherence and finite type are local, so the glued module
has both properties. Its restriction to W is H, and its inclusion there is an
isomorphism. If the overlap is empty, use the zero submodule on V and the empty
set of numerators. If W or V is empty the same construction still applies.
This statement constructs only a module on the union; extension to X and the
image of the extended map are separate steps. -/
theorem exists_finiteType_affine_union
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFiniteType] :
    ∃ G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V.1)),
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ ∃ (φ : G ⟶ H.over (W ⊔ V.1)),
        Mono φ ∧ IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ≤ W ⊔ V.1 from le_sup_left))).map φ) := by sorry

end AlgebraicGeometry.Scheme.Modules
