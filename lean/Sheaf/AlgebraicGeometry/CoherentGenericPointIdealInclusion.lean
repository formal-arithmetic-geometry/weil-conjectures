/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentHomsOverOpen
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentLocalIsomorphism
import Sheaf.AlgebraicGeometry.CoherentStalkMapExtends
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.SectionsAnnihilatedByIdeal
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # A coherent ideal inclusion near a generic point

Source: Stacks Project, Cohomology of Schemes, Lemma 01YE
(`coherent.tex`, label `lemma-prepare-filter-irreducible`)
(blueprint: lem-weil-pbc-coherent-generic-point-ideal-inclusion).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry
namespace Scheme
namespace Modules
noncomputable section

/-- A coherent module whose generic stalk is killed by the ambient maximal ideal contains
an injective pushforward of a finite direct sum of a coherent ideal on the integral closed
subscheme, and this inclusion is an isomorphism on an ambient neighbourhood of that point.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YE
(`coherent.tex`, label `lemma-prepare-filter-irreducible`)
(blueprint: lem-weil-pbc-coherent-generic-point-ideal-inclusion).

Proof (the seven steps of the node):
1. The closed subscheme Z is Noetherian by lem-weil-pbc-immersion-base-change-lft and
   pqf-lem-locnoeth-lft, and compactness of a closed subset. Its defining ideal J is
   coherent by pqf-lem-coherent-ft-locnoeth and
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. The closed immersion gives a surjective
   local-ring map at the generic point with kernel J_ξ, by
   lem-weil-pbc-closed-pushforward-stalks, lem-weil-pbc-locally-surjective-iff-stalks and
   lem-weil-pbc-module-stalk-exact. Its target is a field by
   lem-weil-pbc-integral-scheme-ideal-generic-stalk, so J_ξ is the maximal ideal.
2. Use lem-weil-pbc-sections-annihilated-by-ideal to form F', the sections killed by J.
   This is a coherent submodule by lem-weil-pbc-coherent-kernel-cokernel-locnoeth, with
   F'_ξ = F_ξ by the annihilation hypothesis. By lem-weil-pbc-coherent-local-isomorphism
   its inclusion is an isomorphism on W₁ containing ξ. The equality J F' = 0 follows
   from lem-weil-pbc-ideal-module-product-stalk and lem-weil-pbc-module-iso-on-stalks.
3. By lem-weil-pbc-closed-immersion-coherent-equivalence, write F' ≅ i_* G for a coherent
   module G on Z. Identify its generic stalk by lem-weil-pbc-closed-pushforward-stalks.
4. The generic stalk G_η is finite-dimensional over the generic local field, by
   pqf-def-coherent and lem-weil-pbc-locally-surjective-iff-stalks. Set r to its dimension.
   Extend a stalk isomorphism from O_Z^{⊕ r} using lem-weil-pbc-coherent-stalk-map-extends
   to a map φ on U containing η. By lem-weil-pbc-coherent-local-isomorphism it is an
   isomorphism on a smaller V containing η.
5. Form the ideal I_T of the reduced complement T = Z ∖ U by
   lem-weil-pbc-reduced-induced-closed-subscheme. Lemma lem-weil-pbc-coherent-homs-over-open
   extends φ to χ : (I_T^n)^{⊕ r} → G for some n. Put I = I_T^n; it is coherent by
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. The identification
   I O_Z^{⊕ r} = I^{⊕ r} follows by the finite-sum tensor formula of
   def-pur-sheaf-tensor-product. The map χ remains an isomorphism on V.
6. The kernel K of χ has zero generic stalk by lem-weil-pbc-module-stalk-exact. Its
   coordinate images in O_Z are quasi-coherent ideals by
   lem-weil-pbc-quasi-coherent-module-cokernel-image, with zero generic stalks. They
   vanish by lem-weil-pbc-integral-scheme-ideal-generic-stalk, so K = 0 and χ is injective.
7. Compose i_* χ with i_* G ≅ F' and F' ↪ F. Sectionwise pushforward preserves its
   injectivity (lem-weil-pbc-closed-pushforward-stalks). Since i is a closed embedding,
   W₂ = X ∖ i(Z ∖ V) is open, contains ξ, and has inverse image V. The composite is an
   isomorphism on W = W₁ ∩ W₂, as required.
-/
theorem coherent_generic_point_ideal_inclusion {X Z : Scheme.{w}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules)
    (hF : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ x : (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint Z))).obj F,
        a • x = 0) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      AlgebraicGeometry.RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      ∃ (α : (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⟶ F),
        Mono α ∧
        ∃ (W : X.Opens), i.base (genericPoint Z) ∈ W ∧
          IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map α)
    := by
  sorry

end
end Modules
end Scheme
end AlgebraicGeometry
