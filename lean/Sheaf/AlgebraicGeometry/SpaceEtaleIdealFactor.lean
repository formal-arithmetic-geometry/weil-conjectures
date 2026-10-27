/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.SpaceEtaleFiniteFpEnvelope
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeSubmoduleExtension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedStructureFinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteFpModuleDirectImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFittingIdealCalculus
import Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.RingTheory.FittingIdealDirectSum

/-! # Pushing an ideal factor through a separated étale map of spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 087B, lemma-push-ideal
(blueprint: lem-sfb-space-etale-ideal-factor).

Both sides are subsheaves specified by locally generated section families. On the left,
local generation of the canonical tensor map's range gives its sheaf image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-type ideal trivial above a quasi-compact open divides an extended base ideal.
Source: Stacks Project, More on Morphisms of Spaces, Tag 087B, lemma-push-ideal
(blueprint: lem-sfb-space-etale-ideal-factor).

Proof:
1. By lem-sfb-space-etale-finite-fp-envelope factor φ as a quasi-compact open W → Y
   followed by a finite finitely presented π : Y → T. Integral qcqs permanence and
   lem-sfb-space-quasicompact-affine-tests make Y qcqs and both j(W) and Y_U
   quasi-compact. Their union V is quasi-compact.
2. Glue I on j(W) with the unit ideal on Y_U, using the hypothesis on their overlap.
   Extend this finite-type quasi-coherent ideal from V to I₂ on Y by
   lem-sfb-space-finite-type-submodule-extension.
3. The closed subspace Z defined by I₂ exists by lem-sfb-space-closed-ideal-correspondence.
   Its immersion is finitely presented by lem-sfb-space-closed-structure-finite-presentation.
   Composition (lem-sfb-space-separated-fp-composition) makes τ : Z → T finitely
   presented. It is finite since quotients of finite algebras are finite, and Z_U is empty.
4. By lem-sfb-space-finite-fp-module-direct-image, F = τ_* O_Z is finitely presented
   and quasi-coherent. Take J = Fit₀(F) using lem-sfb-space-fitting-ideal-calculus.
   Affine base change (lem-sfb-space-affine-module-base-change) makes F zero on U,
   so J restricts to the unit ideal there.
5. The graph W → W ×_T Y is open by the étale diagonal calculation
   lem-sfb-space-separated-etale-diagonal-complement, and closed by separatedness of π.
6. Its pullback cuts W ×_T Z into the clopen union V(I) ⨿ Z′. Base change and
   idempotent quotients preserve finite finite presentation on affine charts, using
   lem-sfb-space-relative-spec-correspondence. Thus N = (Z′ → W)_* O_Z′ is finitely
   presented quasi-coherent by lem-sfb-space-finite-fp-module-direct-image.
7. Affine base change identifies φ^*F with (O_W/I) ⊕ N. Set I′ = Fit₀(N).
   The one-generator presentation gives Fit₀(O_W/I) = I; then
   lem-trf-fitting-ideal-direct-sum gives Fit₀(φ^*F) = I I′.
8. Pullback compatibility in lem-sfb-space-fitting-ideal-calculus identifies the image
   of the canonical tensor map φ^*J → O_W with that same ideal product. Equality of
   its sections on every étale test is equality of ideal subsheaves. -/
theorem exists_finiteType_ideal_factor_of_etale
    {S : Scheme.{u}} (T W U : AlgebraicSpace S) (φ : W ⟶ T) (j : U ⟶ T)
    (hTqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ T.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (hTqs : IsAbsolutelyQuasiSeparated T)
    (hφqc : MapIsQuasiCompact φ.hom.hom) (hφsep : MapIsSeparated φ)
    (hφet : MapIsLocally (@Etale) φ)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hUqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ U.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (I : QuasiCoherentIdeal W) (hIft : (I.val : W.Modules).IsFiniteType)
    (hIU : ∀ V : W.EtaleSite,
      (∃ a : yoneda.obj V.obj.left ⟶ U.obj.obj,
        V.obj.hom ≫ φ.hom.hom = a ≫ j.hom.hom) →
      idealSectionImage I.val.arrow V = ⊤) :
    ∃ (J : QuasiCoherentIdeal T) (I' : QuasiCoherentIdeal W),
      (J.val : T.Modules).IsFiniteType ∧ (I'.val : W.Modules).IsFiniteType ∧
      IsIso (idealTensorMap j J) ∧
      ∀ V : W.EtaleSite,
        idealPowerSubsheafSections (idealTensorMap φ J)
            (SheafOfModules.unit W.structureSheaf) (fun _ ↦ Set.univ) 1 V =
          idealPowerSubsheafSections I.val.arrow (SheafOfModules.unit W.structureSheaf)
            (fun V' ↦ Set.range (I'.val.arrow.val.app (op V'))) 1 V := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
