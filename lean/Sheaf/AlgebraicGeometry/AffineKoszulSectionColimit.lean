/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import Sheaf.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import Sheaf.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare
import Sheaf.AlgebraicGeometry.SchemeIsoDerivedQCoh
import Sheaf.AlgebraicGeometry.SchemeIsoPerfectTransport

/-! # The Koszul section colimit on an arbitrary affine scheme

Source: Stacks Project, Tags 08DC, 08DD and 08EH.
(blueprint: lem-sc-affine-koszul-section-colimit).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- The whole Hom-colimit comparison, transported from the spectrum presentation.
This asserts a compatible system of perfect derived augmentations and its colimit;
it does not choose a finite-stage representative or any chain map or K-flat complex.
Source: Stacks Project, perfect.tex, Equation comparison (Tag 08DC), Proposition
represent-cohomology-class-on-open (Tag 08DD), and lemma-lift-map (Tag 08EH).
(blueprint: lem-sc-affine-koszul-section-colimit).

Proof:
1. Put A = Γ(X,O_X) and use X.isoSpec. The image of U under this homeomorphism is
   compact open. The principal-open basis and compactness express it as a finite
   union D(f_i), including the empty union when U is empty.
2. Transfer the chosen derived localizations along the isomorphism, without changing
   the morphism universe, using exists_scheme_iso_derived_localizations. Pushforward
   along the isomorphism and its inverse give the derived equivalence of
   exists_scheme_iso_derived_equivalence. Transport E to Spec A; its cohomology is
   quasi-coherent by scheme_iso_derived_inverse_preserves_qcoh.
3. Apply affine_perfect_open_represent_cohomology to this transported object and
   the finite family. Its perfect objects, augmentations, two-sided inverses, Hom
   diagram and colimit cocone supply the system on Spec A. The structure object is
   the localization of the tilde of the extended single A[0]. The extension-single
   comparison, singleMapHomologicalComplex and tildeSelf identify it with O[0].
4. Transport the diagram and cocone through the global derived equivalence and the
   restriction square exists_scheme_iso_derived_restriction_square. Compose that
   square with the exact overEquiv on each open site. Localized restriction along
   a scheme isomorphism preserves the unit, by Modules.restrictUnitIso, so its single
   complex identifies the transported structure object with Q(T). Naturality gives
   the displayed formula for each leg and transports both inverse identities.
   Equivalences preserve colimits; the induced natural equivalences on Hom sets
   transport the original colimit cocone to the displayed one. Perfectness transports
   by scheme_iso_derived_inverse_preserves_perfect. All these operations are exact
   and use no boundedness of E. For empty U the restricted category is zero and the
   Hom diagram has singleton colimit; the same construction applies to the zero ring.
-/
theorem affine_koszul_section_colimit
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∃ (P : ℕ → schemeDerivedCategory X)
      (a : ∀ n : ℕ, P n ⟶ DerivedCategory.Q.obj T),
      (∀ n : ℕ, IsPerfect X (P n)) ∧
      ∃ v : ∀ n : ℕ, R.obj (DerivedCategory.Q.obj T) ⟶ R.obj (P n),
        (∀ n : ℕ, R.map (a n) ≫ v n = 𝟙 _) ∧
        (∀ n : ℕ, v n ≫ R.map (a n) = 𝟙 _) ∧
        ∃ (D : ℕ ⥤ Type wD) (hD : ∀ n : ℕ, D.obj n = (P n ⟶ E.obj)),
        ∃ ι : D ⟶ (Functor.const ℕ).obj
            (R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj),
          (∀ (n : ℕ) (ξ : P n ⟶ E.obj),
            ι.app n (cast (hD n).symm ξ) = v n ≫ R.map ξ) ∧
          Nonempty (IsColimit (Cocone.mk _ ι)) := by sorry

end AlgebraicGeometry.Scheme
