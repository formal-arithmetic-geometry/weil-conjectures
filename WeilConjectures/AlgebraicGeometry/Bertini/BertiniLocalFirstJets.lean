/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ConormalSequenceSmoothImmersion
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ConormalSequenceSmoothImmersion
import Mathlib.Algebra.MvPolynomial.CommRing
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Local first jets of an immersive generating system

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

/-- The actual relative cotangent fibre on an open of the source.
Source: Stacks Project, Tags 01UM and 02G1.
(blueprint: lem-zl-bertini-local-first-jets). -/
abbrev bertiniCotangentFibre {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (U : Y.Opens) (z : U) :
    ModuleCat ((U : Scheme).residueField z) :=
  Scheme.Hom.relativeDifferentialsStalkFibre (U.ι ≫ f) (𝟙 (U : Scheme)) z

/-- The value and relative differential of an actual local regular function.
The two entries use the same germ, after restriction to the specified source open.
Source: Stacks Project, Tags 01UM and 0FD6.
(blueprint: lem-zl-bertini-local-first-jets). -/
def bertiniLocalFirstJet {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (U : Y.Opens) (z : U)
    (W : Y.Opens) (hz : U.ι z ∈ W) (a : Γ(Y, W)) :
    (U : Scheme).residueField z × bertiniCotangentFibre f U z :=
  ((U : Scheme).residue z
      ((U : Scheme).presheaf.germ (U.ι ⁻¹ᵁ W) z hz (U.ι.app W a)),
    Scheme.Hom.relativeDifferentialsStalkFibreGerm (U.ι ≫ f) (𝟙 (U : Scheme)) z
      (U.ι ⁻¹ᵁ W) hz (U.ι.app W a))

set_option linter.unusedVariables false in
end

end AlgebraicGeometry
