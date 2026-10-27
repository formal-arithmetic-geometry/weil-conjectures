/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Constants on proper geometrically reduced connected algebraic spaces

Source: Stacks Project, Spaces over Fields, Tag 0DMY, clause (7)
(blueprint: lem-sfb-space-proper-field-global-functions).

Global sections are compatible families on the small etale site (`SheafOfModules.sections`).
The map is exactly `SheafOfModules.sectionsMap` of the prescribed structure map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical constants map is bijective for a proper algebraic space whose
base change to every algebraically closed extension is reduced, nonempty and connected.
The conclusion is bijectivity of Gamma(p-sharp), with Gamma(Spec k, O) identified
with k. Global sections of p-star O_Z are Gamma(Z, O_Z) by the chart-limit definition
of direct image. The chart characterization of
`moduleStructureMap` identifies this map with the unital ring map on functions, so its
bijectivity says it is an isomorphism of k-algebras.

Source: Stacks Project, Spaces over Fields, Tag 0DMY, clause (7)
(blueprint: lem-sfb-space-proper-field-global-functions).

Proof:
1. Choose an algebraic closure Omega/k (def-weil-algebraic-closure). Properness survives
   base change (lem-sfb-space-flat-proper-fp-locality). The geometric hypothesis gives
   reducedness, nonemptiness and connectedness of Z_Omega. By
   lem-sfb-space-proper-connected-function-field its global functions B form a field
   finite-dimensional over Omega.
2. By lem-pc-finite-extension-alg-closed the scalar map Omega -> B is bijective.
3. The field-extension map is flat (lem-pc-field-extension-flat). The structure module
   is quasi-coherent (def-trf-space-quasi-coherent-module), hence its direct image is
   quasi-coherent (lem-trf-space-qc-separated-quasi-coherent-pushforward). Apply
   lem-sfb-space-flat-direct-image-base-change. The canonical pullback of the structure
   module is the structure module, by b tensor a |-> b h-sharp(a), with inverse
   b |-> b tensor 1. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-weil-pbc-module-pullback-affine-sections to evaluate on the affine bases. This
   gives alpha: A tensor_k Omega -> B bijective and Omega-linear, carrying a tensor c
   to h-star(a) times c; in particular alpha(1 tensor c) = c.
4. Since 1_B is nonzero, 1_A is nonzero. Choose a k-basis of A containing 1_A by
   lem-weil-pbc-vector-space-basis-through-vector. By def-weil-vector-space-scalar-extension
   its tensors form an Omega-basis of A tensor_k Omega. Their images form a basis of B
   containing 1_B. Since B = Omega, there is no other basis vector. Thus A = k times 1.
   The constants map is surjective and injective (a nonzero scalar has an inverse).
   Its inverse preserves the algebra operations by injectivity of the constants map. -/
theorem structureMap_globalSections_bijective_of_geometricallyReduced_connected
    (k : Type u) [Field k] (Z : AlgebraicSpace (Spec (CommRingCat.of k)))
    (p : Z ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hp : MapIsProper p)
    (hgeom : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
      (∀ T : CostructuredArrow yoneda
          (Limits.pullback p.hom
            ((Scheme.fppfTopology.over (Spec (CommRingCat.of k))).yoneda.map
              (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
                Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶
                  Over.mk (𝟙 (Spec (CommRingCat.of k)))))).obj,
        IsEtale T.hom → AlgebraicGeometry.IsReduced T.left.left) ∧
      ConnectedSpace (Point
        (Limits.pullback p.hom
          ((Scheme.fppfTopology.over (Spec (CommRingCat.of k))).yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
                Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶
                  Over.mk (𝟙 (Spec (CommRingCat.of k)))))).obj)) :
    Function.Bijective (SheafOfModules.sectionsMap (moduleStructureMap p)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
