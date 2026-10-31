/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalRelativeProjProper
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveImpliesProper

/-!
# Properness of projective-bundle morphisms

Source: Stacks Project, Morphisms, Lemma 01WC (lemma-locally-projective-proper),
together with Lemma 01WB (lemma-characterize-locally-projective) and Definition 01W8
(definition-projective),
(blueprint: lem-trf-projective-bundle-proper).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism presented as a closed subscheme of the relative projective bundle of a
finite-type quasi-coherent module is proper.

Source: Stacks Project, Morphisms, Lemma 01WC (lemma-locally-projective-proper),
together with Lemma 01WB (lemma-characterize-locally-projective) and Definition 01W8
(definition-projective).

Proof: Unpack `IsProjectiveBundle` to obtain the relative projective-bundle presentation.
Locally on the target, finite type gives finitely many generating sections.  The relative
Proj construction restricts to the projective bundle of the restricted module, and the
globally generated projective-bundle theorem makes its projection H-projective.  The
H-projective properness theorem then makes that projection proper.  Base changing the
closed immersion to each target open and composing with the proper projection gives
properness of the restricted morphism.  Properness is local on the target, so the original
morphism is proper.  These are the arguments recorded in the proof dependencies
`lem-trf-projective-bundle-global-generated-h-projective`, `lem-kun-projective-implies-proper`,
`lem-weil-pbc-closed-immersion-base-change`, `lem-weil-pbc-closed-immersion-proper`, and
`lemma-nagata-projective-target-local`.
(blueprint: lem-trf-projective-bundle-proper). -/
theorem projectiveBundle_proper {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsProjectiveBundle f) : IsProper f := by
  obtain ⟨E, hE, hEfin, i, hi, hcomp⟩ := hf
  have hA : IsProper
      (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom :=
    canonicalRelativeProj_proper E ⟨hE, hEfin⟩
  have hi' : IsProper i :=
    (hProjective_properness.2.2.1 i hi)
  have hicomp : IsProper
      (i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom) :=
    hProjective_properness.2.2.2 i
      (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom hi' hA
  rw [← hcomp]
  exact hicomp

end AlgebraicGeometry

end
