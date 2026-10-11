/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Coherent modules on the projective line have graded representations

Source: Stacks Project, Cohomology of Schemes, Tags 0AG6 and 0BXD;
blueprint proof of lem-sc-p1-graded-resolution, first sentence
(blueprint: lem-sc-p1-coherent-proj-representation).

The associated sheaf is specified by its degree-zero localization sections, scalar
compatibility and canonical restrictions, using the encoding of
`Proj.gradedModuleSheaf_exists`. No second associated-sheaf construction is made.
-/

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every coherent module on `Proj k[x₀,x₁]` is isomorphic to the sheaf associated to a
finite, integer-graded module. The chart maps identify sections with the degree-zero
fractions and respect scalars and the canonical localization restriction maps.
Source: Stacks Project, Tags 0AG6 (4) and 0BXD, final paragraph of the proof;
blueprint lem-sc-p1-graded-resolution, first sentence.
(blueprint: lem-sc-p1-coherent-proj-representation)

Proof:
1. Form `M = ⨁_{n ≥ 0} Γ(P, G(n))` with its natural polynomial-ring action and extend
   the grading by zero in negative degrees. By lem-sc-p1-serre-section-module-finite
   (Stacks 0AG6 (4)), this module is finitely generated.
2. The canonical degree-zero localization maps on the standard opens glue to a map
   from the associated sheaf to `G`. By lem-sc-p1-serre-section-module-comparison
   (Stacks 0BXD, final paragraph), it is an isomorphism. Use the section identifications
   of lem-weil-pbc-proj-graded-module-sheaf-exists to obtain the displayed chart maps;
   their scalar and restriction formulas are exactly those of the associated sheaf.
-/
theorem coherent_exists_graded_representation
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (homogeneousSubmodule (Fin 2) k)).toRingedSpace G) :
    ∃ (M : ModuleCat.{u} (MvPolynomial (Fin 2) k)),
      Module.Finite (MvPolynomial (Fin 2) k) M ∧
    ∃ (𝓜 : ℤ → AddSubgroup M), DirectSum.IsInternal 𝓜 ∧
      (∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
        a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z)) ∧
    ∃ (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules), Nonempty (F ≅ G) ∧
    ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M),
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f)) ∧
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s) ∧
      (∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by
  sorry

end AlgebraicGeometry.Proj
