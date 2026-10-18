/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Mathlib.CategoryTheory.Functor.OfSequence

import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Sheaf.Topology.ProfiniteCondensedRing

/-!
# Inverting the prime in the integral pro-étale coefficient ring

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-prop-sfb-qlbar-colimit-x/sk-prop-sfb-qlbar-colimit-x-invert-ell.md and its proof
(blueprint: det-prop-sfb-qlbar-colimit-x-invert-ell).

The coefficient rings and inclusion are the published constructions. The helpers only
specialize the regular module, restriction of scalars, and sequential-diagram constructors.
The theorem exhibits the specified fraction cocone on E_X as a colimit and identifies any
colimit equipped with its localization ring structure with E_X as a ring object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The regular integral coefficient module on X.
Source: the displayed sequence in the blueprint localization lemma
(blueprint: det-prop-sfb-qlbar-colimit-x-invert-ell). -/
abbrev padicIntegersRegularModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)

/-- The existing coefficient ring E_X as an integral module along the specified inclusion φ.
Source: the blueprint localization lemma, first and last sentences
(blueprint: det-prop-sfb-qlbar-colimit-x-invert-ell). -/
abbrev padicSubfieldIntegralModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (Mod.comap (padicIntegersToPadicSubfield X ℓ E)).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) X))

/-- The sequence of regular integral modules with transition multiplication by ℓ.
Source: the displayed sequence in the blueprint localization lemma
(blueprint: det-prop-sfb-qlbar-colimit-x-invert-ell). -/
abbrev padicIntegersEllSequence (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (padicIntegersRegularModule X ℓ E))

/-- E_X is the localization of the integral coefficient sheaf at ℓ, with fraction maps
ℓ⁻ᵐφ, and is flat over that integral sheaf.

The witness j is φ with its integral-module linearity. The witness t is the inverse of
multiplication by ℓ on E_X, so j ≫ t^m is exactly ℓ⁻ᵐφ. The natural transformation α,
with these specified components and vertex E_X, is a colimit cocone. For any colimit c
carrying its localization ring structure (in particular its zeroth leg is a ring map),
the comparison is a ring isomorphism with the prescribed value on every term. This states
the comparison independently of any choice of colimit representative. Finally, exactness
of extension of scalars expresses flatness: this functor is already a left adjoint, so
finite-limit preservation supplies the remaining half of exactness.

Source: the blueprint localization lemma and its five proof paragraphs
(blueprint: det-prop-sfb-qlbar-colimit-x-invert-ell).

Proof:
1. On a profinite test S, compactness bounds every continuous E-valued function by one
common denominator ℓ^m. Multiplication by ℓ is injective on C(S, O_E). Thus the maps
h ↦ ℓ⁻ᵐh identify C(S,E) with the sequential abelian-group colimit, naturally in S.
Use the continuous-function coefficient rings of sk-def-sfb-condensed-ring and the
inclusion of def-sfb-integers-to-subfield-point.
2. Every covering of a profinite set has a finite covering family. The sheaf condition
is therefore a finite limit; filtered colimits commute with it by
lem-weil-pbc-filtered-colimits-commute-finite-limits. The same cocone is a sheaf colimit.
3. Pull back using the additive strong monoidal left adjoint of
sk-def-sfb-pullback-from-point. It preserves colimits and multiplication by ℓ. The legs
are integral-linear. To see the colimit also in modules, compare the two linearity maps
on O_E,X tensor E_X; tensor preserves this colimit by sk-def-sfb-sheaf-tensor, so equality
on every stage implies equality on the colimit. The zeroth leg is the recorded φ.
4. The inverse of multiplication by ℓ on the point pulls back to t. The ring map φ
extends uniquely to the localization. On every stage its value is ℓ⁻ᵐφ; hence its
underlying map is the module-colimit comparison, and is invertible. The multiplication
formula on fractions is (a/ℓ^m)(b/ℓ^n) = ab/ℓ^(m+n), giving the claimed ring comparison.
5. In the universes of def-weil-pbc-proetale-site, use the exact filtered colimits and
tensor-colimit formula of lem-pc-module-filtered-colimits-tensor. Tensoring with E_X is
the colimit of M --ℓ--> M --ℓ--> M, and thus preserves short exact sequences. This is
flatness and requires no quasi-compactness or Noetherian hypothesis on X. -/
theorem padicIntegers_invertEll (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ j : padicIntegersRegularModule X ℓ E ⟶ padicSubfieldIntegralModule X ℓ E,
      j.hom = padicIntegersToPadicSubfield X ℓ E ∧
      ∃ t : End (padicSubfieldIntegralModule X ℓ E),
        (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E)) ≫ t = 𝟙 _ ∧
        t ≫ (ℓ • 𝟙 (padicSubfieldIntegralModule X ℓ E)) = 𝟙 _ ∧
        ∃ α : padicIntegersEllSequence X ℓ E ⟶
            (Functor.const ℕ).obj (padicSubfieldIntegralModule X ℓ E),
          (∀ m : ℕ, α.app m = j ≫ t ^ m) ∧
          Nonempty (IsColimit
            ({ pt := padicSubfieldIntegralModule X ℓ E, ι := α } :
              Cocone (padicIntegersEllSequence X ℓ E))) ∧
          (∀ (c : Cocone (padicIntegersEllSequence X ℓ E)), IsColimit c →
            ∀ [MonObj c.pt.X] [IsCommMonObj c.pt.X],
              IsMonHom (@id
                (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X ⟶ c.pt.X)
                (c.ι.app 0).hom) →
              ∃ e : Mon.mk c.pt.X ≅
                  Mon.mk (condensedRingObj (Profinite.continuousMapRingObj E.1) X),
                ∀ m : ℕ, (c.ι.app m).hom ≫ e.hom.hom = (α.app m).hom) ∧
          PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) := by
  sorry

end AlgebraicGeometry.ProEtale
