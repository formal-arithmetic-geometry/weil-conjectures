/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Topology.GlueSheavesOfModules
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.StructureSheaf
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation

/-! # Extension from punctured local Picard triviality

Source: EGA IV4, Proposition 21.13.10, Proposition 21.13.8 and Definition 21.13.1
(blueprint: lem-sfb-punctured-picard-local-extension-criterion).

The normality and local dimension assumptions supply the Hartogs condition;
punctured local Picard triviality supplies essential surjectivity.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Invertible modules and their morphisms extend across a closed subset when
all its punctured local spectra have trivial Picard group and local dimension
at least two, on a locally Noetherian scheme with normal-domain stalks.

Source: EGA IV4, Proposition 21.13.10 with Proposition 21.13.8 and
Definition 21.13.1, specialized to normal schemes.
(blueprint: lem-sfb-punctured-picard-local-extension-criterion)

Proof:
1. Fix H and cover it by normal integral Noetherian affine opens W, using
   pqf-lem-affine-open-locnoeth and rem-pc-regular-normal. Their stalks are
   the original stalks. Invertible modules are coherent by
   pqf-lem-coherent-ft-locnoeth, and reflexive by rank-one evaluation.
2. Apply lem-sfb-normal-reflexive-open-equivalence on each W to extend a
   morphism uniquely. Apply its Hom injectivity on affine charts of overlaps;
   lem-weil-pbc-glue-sheaves-of-modules glues the maps. This proves Hom
   bijectivity on every open, independently of object extension.
3. For L on the complement, the same reflexive extension theorem gives a
   coherent reflexive F on W. Its noninvertible locus N is closed in Z.
   If N is nonempty, choose a generic point y of a component using
   lem-sc-noetherian-closed-subset-finite-components and
   lem-weil-pbc-scheme-sober. Every strict generization of y avoids N.
4. Set R to the stalk at y and J to the stalk of F. By
   lem-weil-pbc-spec-local-ring-canonical-morphism its punctured spectrum
   maps to the invertible locus. The localization Noetherian and normal-domain
   lemmas make Spec R Noetherian, normal and integral. The affine germ
   localization and quasi-coherent finite-type affine lemmas make J finite;
   lem-sfb-affine-reflexive-module-comparison makes J reflexive.
5. The tilde-Gamma adjunction, tilde pullback base change and localization
   tensor-over-base comparison identify the pullback of F with tilde J.
   Pullback preserves rank-one trivializations by def-pc-module-pullback.
   Thus tilde J is invertible on the puncture, where the hypothesis makes it
   trivial.
6. The reflexive open-equivalence theorem extends that trivialization and
   its inverse over Spec R; Hom injectivity makes them inverse. Global sections
   give J isomorphic to R. By lem-weil-pbc-coherent-local-finite-presentation
   and lem-trf-finite-presentation-stalk-basis-spread this basis spreads to
   a neighbourhood of y, contradicting its membership in N. Hence F is invertible.
7. Use step 2 to extend the transition isomorphisms of these local extensions.
   Uniqueness gives inverse and cocycle identities. Glue by
   lem-weil-pbc-glue-sheaves-of-modules; invertibility is local by
   def-sc-invertible-module. The comparison with L glues as well. Empty opens
   use the empty cover; for empty Z use L itself. No density assumption is needed:
   a nonempty integral chart cannot lie in Z since its generic stalk has dimension zero. -/
theorem punctured_picard_local_extension_criterion
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (Z : Set X) (hZ : IsClosed Z)
    (hdim : ∀ z : X, z ∈ Z → 2 ≤ ringKrullDim (X.presheaf.stalk z))
    (hpic : ∀ z : X, z ∈ Z →
      ∀ L : (puncturedSpectrum (X.presheaf.stalk z)).toScheme.Modules,
        L.IsInvertible → Nonempty (L ≅ SheafOfModules.unit _)) :
    ∀ H : X.Opens,
      (∀ A B : H.toScheme.Modules, A.IsInvertible → B.IsInvertible →
        Function.Bijective
          (fun f : A ⟶ B ↦
            (Scheme.Modules.pullback
              (H.ι ⁻¹ᵁ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens)).ι).map f)) ∧
      (∀ L : (H.ι ⁻¹ᵁ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens)).toScheme.Modules,
        L.IsInvertible → ∃ M : H.toScheme.Modules, M.IsInvertible ∧
          Nonempty ((Scheme.Modules.pullback
            (H.ι ⁻¹ᵁ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens)).ι).obj M ≅ L)) := by
  sorry

end AlgebraicGeometry
