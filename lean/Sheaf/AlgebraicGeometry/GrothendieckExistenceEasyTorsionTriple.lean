/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.FiniteIffFormalGlueing
import Sheaf.RingTheory.FormalGlueingComplexExact
import Sheaf.RingTheory.FormalGlueingIsogeny
import Sheaf.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Torsion-controlled triples for easy algebraization

Source: Stacks Project, Tag 0889, part (1)
(blueprint: lem-weil-pbc-easy-algebraization-torsion-triple).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Easy algebraization with the torsion condition on the actual coherent map retained.
Uniqueness is among torsion-controlled triples. This restriction matters when the ideal
is the unit ideal: completion then forgets everything, and an unrestricted triple need
not be isomorphic to the chosen one.

Source: Stacks Project, Tag 0889, part (1), including condition (1)(b)
(blueprint: lem-weil-pbc-easy-algebraization-torsion-triple).

Proof:
Restrict to a finite affine cover. The coherent-formal-module affine equivalence turns
alpha into a map from a finite completed module to the completion of a finite module.
Remark 0888 converts the uniform component annihilation into annihilation of the limit
kernel and cokernel. The formal-gluing isogeny theorem constructs a module map with
ideal-power-torsion kernel and cokernel whose completion is this map. The finiteness
criterion for formal gluing makes its source finite. Formal gluing also gives unique
isomorphisms of any two such torsion-controlled triples, respecting both the map and
completion comparison. On overlaps those isomorphisms satisfy the cocycle identity by
uniqueness; glue the modules and their maps and completion comparisons. Finitely many
affines give a uniform positive exponent for the glued kernel and cokernel. The same
uniqueness glues isomorphisms of triples and proves the asserted global uniqueness.
-/
theorem grothendieckExistenceEasy_torsionTriple
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) ∧
      ∀ (F' : CoherentModules X) (a' : F' ⟶ H)
        (β' : N ≅ (completion X J).obj F'),
        δ = β'.hom ≫ (completion X J).map a' →
        (∃ s : ℕ, 1 ≤ s ∧
          IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
            (kernel a'.hom)) ∧
          IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
            (cokernel a'.hom))) →
        ∃! γ : F ≅ F', γ.hom ≫ a' = a ∧
          β.hom ≫ (completion X J).map γ.hom = β'.hom := by
  sorry

end AlgebraicGeometry
