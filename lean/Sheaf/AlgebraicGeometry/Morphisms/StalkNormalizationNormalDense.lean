/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart
import Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDensePart

/-!
# Normality and density of the localized relative normalization

Source: Stacks Project, Tags 035L, 035K, 035I, 0307 and 0EYJ.
(blueprint: lem-sbc-stalk-normalization-normal-dense)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Localization of the relative normalization is normal, with dense punctured source.

Source: Stacks Project, Tags 035L (normality of relative normalization),
035K (locality), 035I (dominance), 0307 (localization), and 0EYJ.
(blueprint: lem-sbc-stalk-normalization-normal-dense)

Proof: Smoothness over a normal base makes C normal. The finite etale scheme P over
C_U is normal and locally Noetherian, with locally finite irreducible components.
Relative normalization in P is therefore normal: on an affine chart decompose P
into its normal integral components, take integral closures in their rings of
sections, and localize. Each such integral closure is a normal domain. Localization
at s commutes with integral closure, so the same description proves normality of
the displayed pullback. The map from P to its relative normalization is
schematically dominant. After localization it remains schematically dominant,
since localization is flat. Its image lies over C_U, so the displayed open
preimage is dense. If P is empty both claims are vacuous. -/
theorem stalk_normalization_normal_and_dense {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    (∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z)) ∧
    Dense (↑(n ⁻¹ᵁ (l ⁻¹ᵁ (c ⁻¹ᵁ U))) :
      Set (pullback f.fromNormalization l : Scheme.{u})) := by
  exact ⟨stalk_normalization_normal_part hS c U PA s,
    stalk_normalization_dense_part hS c U PA s⟩

end AlgebraicGeometry.Scheme
