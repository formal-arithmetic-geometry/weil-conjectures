/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Finite-type capture on a compact open inside an affine open

Source: Stacks Project, Properties, Lemma 01PF, affine finite-numerator step.
(blueprint: lem-weil-pbc-module-finite-type-affine-capture).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on an affine open has a finite-type submodule agreeing
with it on a compact open where it is already of finite type.

Source: Stacks Project, Properties, Lemma 01PF (label lemma-extend), the affine
finite-numerator argument, and Lemma 01PB (label lemma-finite-type-module).
https://stacks.math.columbia.edu/tag/01PF
(blueprint: lem-weil-pbc-module-finite-type-affine-capture).

Proof: Identify H on V with the associated sheaf of its module of sections M.
For each point of K choose a principal open D(f) contained in K. On D(f), finite
type of H on K and the affine finite-type criterion imply finite generation of
M localized at f. Compactness of K gives finitely many such principal opens.
Choose finite generating families in their localized modules, express each
as m/f^n, and let N be the submodule of M spanned by the finitely many numerators m.
The localized inclusion N_f -> M_f is injective by exactness of localization,
and surjective since its image contains each chosen generator m/f^n.
Associate sheaves to N and its inclusion in M, and use the counit isomorphism
to obtain Q -> H on V. The associated module of N is quasi-coherent and finite
type. On the finite principal cover its inclusion is an isomorphism, hence it
is an isomorphism on K by the sheaf axiom. Transport from the affine scheme
V to the slice site of opens under V. If K is empty take N = 0 and the empty
family; if K = V the same argument gives an isomorphism on all of V. -/
theorem exists_finiteType_affine_capture
    (X : Scheme.{u}) (V : X.affineOpens) (K : X.Opens)
    (hK : IsCompact (K : Set X)) (hKV : K ≤ V.1)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over K).IsFiniteType] :
    ∃ Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V.1),
      Q.IsQuasicoherent ∧ Q.IsFiniteType ∧ ∃ (ι : Q ⟶ H.over V.1),
        Mono ι ∧ IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hKV)).map ι) := by sorry

end AlgebraicGeometry.Scheme.Modules
