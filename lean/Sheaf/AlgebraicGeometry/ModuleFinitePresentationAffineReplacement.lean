/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import Sheaf.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernel
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # A finitely presented replacement on one affine open

Source: Stacks Project, Properties, Lemma 01PI, affine construction.
(blueprint: lem-weil-pbc-module-finite-presentation-affine-replacement).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Replace a quasi-coherent module on an affine open by a finitely presented module,
with a map which is an isomorphism on the overlap with the previous open.

Source: Stacks Project, Properties, Lemma 01PI, affine construction
(https://stacks.math.columbia.edu/tag/01PI).
(blueprint: lem-weil-pbc-module-finite-presentation-affine-replacement).

Proof: The intersection W intersect V is quasi-compact by quasi-separatedness.
Restriction of H to the intersection is finitely presented, since finite presentation
is local and preserved by restriction. Work on the affine scheme V. Apply 01PF to
H restricted to V and its whole restriction on the intersection, to obtain a
quasi-coherent finite-type submodule H' agreeing with H on the intersection.
Finite global generators on V give an epimorphism from a finite free module to H'.
Its kernel K is quasi-coherent. Restriction preserves the kernel and epimorphism,
and the restricted target is finitely presented. By Modules 01BP, the restricted
kernel is finite type. Apply 01PF again to obtain a finite-type quasi-coherent
submodule K' of K agreeing with K on the intersection. Let E be the cokernel of
K' mapping to the finite free module. By Modules 0H96, E is finitely presented.
The free-module epimorphism kills K', so induces a map from E to H' and then H.
On the intersection K' equals the whole kernel; restriction preserves cokernels,
and an epimorphism in an abelian category is the cokernel of its kernel. Hence
this induced map is an isomorphism there. Transport the construction back to the
localized site over V. If the overlap is empty, choose H' and K' zero; the same
cokernel argument applies. No compactness of the ambient scheme is required. -/
theorem exists_finitePresentation_affine_replacement
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over W).IsFinitePresentation] :
    ∃ E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V.1),
      E.IsFinitePresentation ∧ ∃ (j : E ⟶ H.over V.1),
        IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (show W ⊓ V.1 ≤ V.1 from inf_le_right))).map j) := by sorry

end AlgebraicGeometry.Scheme.Modules
