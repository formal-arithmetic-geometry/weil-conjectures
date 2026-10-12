/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.RingTheory.FormalGlueingComplexExact
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.Topology.GlueSheavesOfModules
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Lifting compatible maps between coherent isogenies under a fixed module

Source: Stacks Project, Lemma 0889(2), omitted uniqueness verification;
More on Algebra, Lemma 05EK
(blueprint: lem-weil-pbc-completion-isogeny-from-hom-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Completion uniquely lifts compatible morphisms between coherent isogenies under G.
The formal morphism need not be invertible. This is Hom descent, independent of
existence of an algebraization of a formal object.
Source: Stacks Project, Lemma 0889(2), omitted uniqueness verification, expanded in
steps 6 and 8 of lem-weil-pbc-grothendieck-existence-easy; More on Algebra, Lemma 05EK
(blueprint: lem-weil-pbc-completion-isogeny-from-hom-lift).

Proof. Lift on a basis of Noetherian affine opens and then glue the unique maps.
On Spec A put S = A^ and choose generators f_i of I. Identify completions of the
finite modules with their base changes, naturally on morphisms, by 087W and 00MA.
Localizing at f_i kills the kernels and cokernels of a and a', so their localized
maps are invertible. Put u_i = a'_i composed with the inverse of a_i. The equation
for theta forces its localization to be the base change of u_i, by cancellation
of the localized a_i. The u_i agree after localizing at f_i f_j.
For x in H the pair (theta(1 tensor x), (u_i(x/1))_i) is therefore in the kernel of
the difference map of the gluing complex of H'. Exactness of 05EK gives a unique
gamma(x) with those components. Injectivity of that complex proves additivity and
A-linearity. The completed map equals theta on pure tensors, and its localizations
are u_i. Injectivity of the gluing complex of H' proves gamma composed with a equals
a', as this equation holds after base change and every localization. Any other
compatible lift has those same completed and localized maps, hence equals gamma
by injectivity of that complex. For I=0 the empty gluing complex reduces to the
identity completion. For I=1 the maps a and a' are already isomorphisms.
Transfer gamma back by the fully faithful affine sheaf/module dictionary.
Restriction is compatible with completion and preserves the torsion bounds, so
uniqueness makes the affine lifts compatible under further restriction. Every
overlap is covered by smaller affine opens: the maps agree on these, so 04TN glues
them globally. The two equations and uniqueness hold locally, hence globally.
No assumption that intersections of affine opens are affine is used.
-/
theorem completion_isogeny_from_hom_lift (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    ∀ (G H H' : CoherentModules X) (a : G ⟶ H) (a' : G ⟶ H'),
      (∃ t : ℕ, 1 ≤ t ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2 (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a.hom))) →
      (∃ t : ℕ, 1 ≤ t ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2 (kernel a'.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a'.hom))) →
      ∀ θ : (completion X I).obj H ⟶ (completion X I).obj H',
        (completion X I).map a ≫ θ = (completion X I).map a' →
        ∃! γ : H ⟶ H', a ≫ γ = a' ∧ (completion X I).map γ = θ := by sorry

end AlgebraicGeometry
