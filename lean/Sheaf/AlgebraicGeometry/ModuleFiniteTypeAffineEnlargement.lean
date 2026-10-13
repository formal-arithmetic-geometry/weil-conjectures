/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.Coherent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Enlarging the open of finite type by one affine open

Source: Stacks Project, Properties, Lemma 01PF, proof, lines 2865--2894.
(blueprint: lem-weil-pbc-module-finite-type-affine-enlargement).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- A quasi-coherent module finite type on W has a quasi-coherent submodule
finite type on W union V, equal to the original on W, when V is affine.

Source: Stacks Project, Properties, Lemma 01PF, proof, lines 2865--2894.
(blueprint: lem-weil-pbc-module-finite-type-affine-enlargement).

Proof: The overlap W intersect V is quasi-compact by quasi-separatedness. On V,
identify H with the associated sheaf of its module of sections. Cover the overlap
by finitely many principal opens on which H has finitely many generators. Choose
numerators in H(V) for these generators and let N be the submodule they generate.
The associated sheaf of N is a finite-type quasi-coherent submodule of H on V.
Its localization equals H on each principal open: it contains the generators,
and the opposite inclusion follows from N being a submodule of H(V). The affine
quasi-coherent equivalence and the sheaf property identify its restriction to the
whole overlap with H. Glue it with H on W, using the subsheaf of H on W union V
whose sections satisfy both local membership conditions. This subsheaf is
quasi-coherent and finite type, both properties being local. The union is
quasi-compact, and its inclusion into X is quasi-compact since X is
quasi-separated. Extend the inclusion map to X by the quasi-coherent extension
theorem 01PE(3), and take its image in H. Images are quasi-coherent, and restriction
is exact, so this image restricts to the glued submodule on the union. It is
therefore finite type there and its inclusion is an isomorphism on W. If the
overlap is empty the list of generators is empty; all constructions still work.
No quasi-compactness of X or finite type outside W union V is claimed. -/
theorem exists_finiteType_affine_enlargement
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFiniteType] :
    ∃ (E : SheafOfModules.{u} (moduleRings X.toRingedSpace)), E.IsQuasicoherent ∧
      (E.over (W ⊔ V.1)).IsFiniteType ∧ ∃ (j : E ⟶ H),
        Mono j ∧ IsIso ((SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) W).map j) := by sorry

end AlgebraicGeometry.Scheme.Modules
