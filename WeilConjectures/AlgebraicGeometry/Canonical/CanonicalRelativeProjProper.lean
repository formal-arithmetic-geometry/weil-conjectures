/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleAffinePresentations
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalRelativeProjProperLocal

/-! # Properness of finite type relative Proj

Source: Stacks Project, Morphisms, Lemma 01WC, with Lemma 01WB.

The remaining local argument is: use affine presentations of a finite type
quasi-coherent module, identify the corresponding open restrictions of relative
Proj with the local projective bundles, prove those restrictions H-projective,
and apply target-locality of properness.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The canonical relative projective bundle of a finite type quasi-coherent module is proper.

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC. -/
theorem canonicalRelativeProj_proper {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) :
    IsProper (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom := by
  obtain ⟨I, U, _n, hU, _hlocal⟩ :=
    exists_affine_projectiveBundle_presentations S E hE
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U hU
  intro i
  exact canonicalRelativeProj_restrict_proper E hE (U i) (_hlocal i).1

end AlgebraicGeometry

end
