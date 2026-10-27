/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import Sheaf.AlgebraicGeometry.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Integer twists separate on every nonempty base neighbourhood

Source: EGA II, Remark 4.2.7; Stacks, Tag 0BXJ.
(blueprint: lem-sfb-projective-bundle-integer-twist-separation)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- Integer twists which agree above a neighbourhood containing a base point have equal degrees.

Source: EGA II, Remark 4.2.7, printed p.75; Stacks, divisors.tex, Tag 0BXJ.
(blueprint: lem-sfb-projective-bundle-integer-twist-separation)

Proof: pull the given isomorphism back to the fibre over s. Base change identifies that
fibre and its normalized tautological quotient with the projective bundle of the
r-dimensional residue vector space E(s). Pullback preserves integer tensor powers,
including negative powers because their inverse evaluations pull back. The field
normal-form theorem, applied to this residue-field bundle and its tautological line,
has a unique integer exponent. Both m and n satisfy that normal form, so m = n.
The hypothesis s in U supplies a nonempty base fibre; r >= 2 excludes projective
space of dimension zero, where integer twists would all be trivial. -/
theorem projective_bundle_integer_twist_separation (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E) (U : S.Opens) (s : S) (hs : s ∈ U) (m n : ℤ)
    (e : Nonempty ((tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
        (integerLinePower D.line D.invertible m) ≅
      (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
        (integerLinePower D.line D.invertible n))) : m = n := by
  sorry

end AlgebraicGeometry.ProjectiveBundlePicardClassification
