/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Curve.PointedEtaleStalk

/-! # Canonical global arrows used by the normalized line-family stalk comparison

Source: blueprint latest, sk-prop-a1-kummer, prop-pur-gm-relative-kummer.proof.md,
Step 2; Stacks Project, Tags 03Q8, 03Q9 and 03PL
(blueprint: def-pur-normalized-kummer-global-arrows).

This module only defines data; it states no theorem. For a k-scheme B it gives the
family C_B = C x_k B with its projection a_B and k-structure, the derived global sections
G(T) and derived direct image I(f) of the root line L, the global germ Gamma -> stalk at
a geometric point s through the terminal etale object, the edge germ G(X) -> I(f)_s
(inverse Leray comparison followed by the derived germ), the constant map
c_T : A_T -> L_T, a -> zeta tensor a, its transpose under the constant-sheaf/sections
derived adjunction, the untwisted unit A_B[0] -> L_B -> I(f) and its stalk through the
canonical constant-stalk identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The projection a_B of the specified family.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerProjection {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) (b : Bool) := pullback.snd (KummerLine.structureMap k b) p

/-- Its k-structure, using the projection to C.
Source: blueprint Step 2 (blueprint: def-pur-normalized-kummer-global-arrows). -/
abbrev normalizedKummerStructure {k : Type u} [Field k] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) (b : Bool) :=
  pullback.fst (KummerLine.structureMap k b) p ≫ KummerLine.structureMap k b

end AlgebraicGeometry.Etale
