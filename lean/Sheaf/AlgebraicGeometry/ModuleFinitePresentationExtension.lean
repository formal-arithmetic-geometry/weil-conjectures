/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import Sheaf.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernel
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Extension of finitely presented modules and their morphisms

Source: Stacks Project, Properties of Schemes, Lemma 28.23.4, Tag 01PI
(blueprint: lem-weil-pbc-module-finite-presentation-extension).

Restriction to an open is expressed on the localized site with `SheafOfModules.over`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism from a finitely presented module on a quasi-compact open of a qcqs scheme
into a quasi-coherent module extends to a finitely presented module on the whole scheme.
Source: Stacks Project, Properties of Schemes, Lemma 28.23.4, Tag 01PI
(blueprint: lem-weil-pbc-module-finite-presentation-extension).

Proof (the nine steps of the node):
1. Choose a finite affine open cover of `X` (lem-weil-pbc-affine-opens-basis and
   def-weil-pbc-quasi-compact-scheme), and let `W_k` be `U` union its first `k` opens.
2. Induct on `k`, extending the pair of module and morphism while retaining an
   isomorphism over `U` compatible with the original morphism. At `k = 0` take the
   original pair and the identity; at the last stage `W_k = X`.
3. For the next affine open `V`, put `U' = W_k ∩ V`. Quasi-separatedness and compactness
   make `U'` quasi-compact, and its inclusion in `V` quasi-compact
   (lem-weil-pbc-qcqs-scheme-spectral, def-weil-spectral-space,
   lem-weil-pbc-affine-scheme-qcqs). Restrict the pair to `U'`, preserving finite
   presentation (lem-weil-pbc-module-restriction-open-immersion-colimits).
4. Extend the restricted pair to a quasi-coherent module `H` and map into `F|_V`
   (lem-weil-pbc-quasi-coherent-extension-qc-open); finite presentation implies the
   required quasi-coherence (pqf-def-coherent).
5. Replace `H` by a quasi-coherent finite type submodule `H'` agreeing with it on `U'`
   (lem-weil-pbc-module-finite-type-submodule-extension), and restrict its map.
6. Choose finitely many generating sections on the affine `V` to obtain an epimorphism
   `O_V^m → H'` (lem-weil-pbc-affine-finite-type-generating-sections,
   def-weil-pbc-generating-sections, lem-weil-pbc-quasi-coherent-finite-type-affine).
   Its kernel `K` is quasi-coherent (lem-weil-pbc-quasi-coherent-module-kernel).
   The epimorphism is sheaf-surjective by
   lem-weil-pbc-ringed-space-module-exactness-local-lifting.
7. Restriction preserves the kernel and epimorphism. Since the target on `U'` is
   finitely presented, `K|_U'` is finite type
   (lem-weil-pbc-finite-presentation-kernel-surjection-finite-type). Extend it to a
   quasi-coherent finite type submodule `K'` of `K`
   (lem-weil-pbc-module-finite-type-submodule-extension).
8. Set `G'_V = O_V^m / K'`, finitely presented by
   lem-weil-pbc-module-finite-presentation-cokernel. The quotient induces a map to
   `H'` and hence to `F|_V`. Restriction preserves cokernels
   (lem-weil-pbc-module-restriction-open-immersion-colimits), so this map to `H'`
   becomes an isomorphism on `U'`: in the abelian module category an epimorphism is
   the cokernel of its kernel (def-weil-sheaf-of-modules-category). Its composite
   with the old identification gives an isomorphism compatible with the maps to `F`.
9. Glue the modules over `W_k` and `V` using that isomorphism on `U'`, then glue their
   compatible maps (lem-weil-pbc-glue-sheaves-of-modules). Finite presentation is local,
   so the glued module is finitely presented. Composing the old identification on `U`
   with the gluing identification supplies the compatible isomorphism at `k + 1`. -/
theorem exists_finitePresentation_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    [G.IsFinitePresentation] (φ : G ⟶ F.over U) :
    ∃ (G' : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      G'.IsFinitePresentation ∧
        ∃ (φ' : G' ⟶ F) (e : G'.over U ≅ G),
          (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map φ' = e.hom ≫ φ :=
  sorry

end AlgebraicGeometry.Scheme.Modules
