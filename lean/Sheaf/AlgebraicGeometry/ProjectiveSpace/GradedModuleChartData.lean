/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# Chart data for a graded polynomial module

Source: Stacks Project, Tag 01M6 and Lemma 01M7.
(blueprint: lem-sc-p1-graded-module-chart-data).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An integer-graded polynomial module has an associated sheaf with explicit chart data.
Source: Stacks Project, construction before Definition 01M6 and Lemma 01M7.
(blueprint: lem-sc-p1-graded-module-chart-data).

Proof:
Apply gradedModuleSheaf_exists to the additive-subgroup form of the homogeneous
polynomial grading. Changing from homogeneous submodules to their underlying additive
subgroups preserves all homogeneous ideals and all degree-zero localizations. These
identifications commute with basic opens and structure-sheaf restrictions, hence induce
an isomorphism of their Proj schemes. Transport the constructed sheaf across this
isomorphism. On each chart compose its additive equivalence to the degree-zero
submodule with the submodule inclusion into the ordinary localization. Injectivity
comes from the equivalence and inclusion, and surjectivity onto degree-zero fractions
comes from the equivalence and the specified carrier of the submodule. Apply the
submodule inclusion to the scalar equation. For a relation g^e = a*f, apply it to the
restriction equation and then the formula for rho supplied by gradedModuleSheaf_exists.
These give precisely the three chart properties below. -/
theorem graded_module_chart_data_exists (k : Type u) [Field k]
    (A : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝒢 : ℤ → AddSubgroup A) (h𝒢 : DirectSum.IsInternal 𝒢)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : A),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 j → s • x ∈ 𝒢 ((n : ℤ) + j)) :
    ∃ E : (Proj (homogeneousSubmodule (Fin 2) k)).Modules,
    ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f A),
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝒢 n : Set A)) (Submonoid.powers f)) ∧
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
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
        ∀ (m : ℕ) (y : A)
          (s : E.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (E.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by
  sorry

end AlgebraicGeometry.Proj
