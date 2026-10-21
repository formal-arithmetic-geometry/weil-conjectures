# WeilConjectures.PurityFiniteSetting.PurityFiniteReductionEquation

## Reason

Restore the assigned quarantined module `Sheaf.Paper.VectorPurityFiniteReduction`.
The current row of `coord/rework.tsv` records its removal during the cluster
restore, with the authoritative archive at
`quarantine/Sheaf/Paper/VectorPurityFiniteReduction.lean`.
This is a definition-restoration assignment with zero proof holes.
The live module is absent; restoring its seven actual constructions repairs
that absence. The archive remains untouched.

## Old

The live path `lean/Sheaf/Paper/VectorPurityFiniteReduction.lean` is absent.
The existing node's Lean attachment, statement dependencies and normalization
requirements remain in force. The archived source is reproduced under New.

## New

Restore the archived module verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityScalarSingle
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Derived finite-reduction equation for vector purity

Source: main-20261015 sec-smooth-purity/sk-prop-an, integration and Steps 4--6
(blueprint: def-pur-vector-purity-finite-reduction).

## Main definitions

This module gives the canonical comparisons and their displayed source equation.
Every map is constructed before the compatibility proposition is stated.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The finite coefficient ring at a positive level. Source: sk-def-purity-conv,
finite quotients (blueprint: def-pur-vector-purity-finite-reduction). -/
noncomputable abbrev purityReductionRing (P : PurityFiniteSetting.{u}) (n : ℕ)
    (_hn : 1 ≤ n) : Type (u + 1) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension n)

/-- The canonical quotient map between positive coefficient levels.
Source: sk-prop-an, Step 6 (blueprint: def-pur-vector-purity-finite-reduction). -/
noncomputable def purityReductionRingMap (P : PurityFiniteSetting.{u})
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≤ n) :
    purityReductionRing P n hn →+* purityReductionRing P m hm :=
  RingHom.ulift (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn))

/-- Pure root tensors fix the ordinary scalar-line comparison independently of purity.
Source: sk-prop-an, Kummer normalization in Step 6
(blueprint: def-pur-vector-purity-finite-reduction). -/
def PurityScalarLineNormalization {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (N : ℕ) (hA : (N : A) = 0) (hA' : (N : A') = 0)
    (T : Scheme.{u})
    (c : (Etale.purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateLine T N A hA) ≅
      Scheme.finiteEtaleTateLine T N A' hA') : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj U),
    (((Etale.purityScalarSheafAdjunction φ T).homEquiv _ _ c.hom).hom.app U)
        (Scheme.finiteEtaleTateOneGenerator A N T hA U a z) =
      Scheme.finiteEtaleTateOneGenerator A' N T hA' U (φ a) z

/-- Scalar extension of the ordered Tate power, from the scalar tensorator, scalar
shift map, and the specified ordinary coefficient-line map.
Source: sk-prop-an, Step 6 (blueprint: def-pur-vector-purity-finite-reduction). -/
def purityScalarPower {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (N : ℕ) (hA : (N : A) = 0) (hA' : (N : A') = 0)
    (T : Scheme.{u})
    (c : (Etale.purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateLine T N A hA) ≅
      Scheme.finiteEtaleTateLine T N A' hA') : ∀ d : ℕ,
    (Etale.purityScalarExtension φ T).obj (Etale.affineLinearBaseCoefficient A N hA T d) ⟶
      Etale.affineLinearBaseCoefficient A' N hA' T d
  | 0 => purityScalarUnitMap φ T
  | d + 1 =>
    letI := (Etale.purityScalarAdjunction φ T).leftAdjointCommShift ℤ
    (Etale.purityScalarTensor φ T _ _).hom ≫
      (purityScalarPower φ N hA hA' T c d ⊗ₘ
        ((Functor.commShiftIso (Etale.purityScalarExtension φ T) (2 : ℤ)).hom.app _ ≫
          (purityScalarSingleMap φ T (Scheme.finiteEtaleTateLine T N A hA) ≫
            (DerivedCategory.singleFunctor _ 0).map c.hom)⟦(2 : ℤ)⟧'))

/-- The scalar/pullback/twist comparison a_{n,m}; its ingredients contain no purity
map. Source: sk-prop-an, Step 6 (blueprint: def-pur-vector-purity-finite-reduction). -/
def purityScalarSourceMap {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (φ : A →+* A') (N : ℕ) (hA : (N : A) = 0) (hA' : (N : A') = 0)
    (B : Scheme.{u}) [IsNoetherian B] (d : ℕ) (F : B.Modules)
    [F.IsFiniteLocallyFreeOfRank d]
    (c : (Etale.purityScalarSheaf φ B).obj (Scheme.finiteEtaleTateLine B N A hA) ≅
      Scheme.finiteEtaleTateLine B N A' hA')
    (K : Etale.DerivedCategoryModule A B) :
    (Etale.purityScalarExtension φ (VectorBundleZeroSection.scheme B d F)).obj
      ((RfPullback A (VectorBundleZeroSection.π B d F)).obj
        (Etale.affineLinearBaseCoefficient A N hA B d) ⊗
        (RfPullback A (VectorBundleZeroSection.π B d F)).obj K) ⟶
      (RfPullback A' (VectorBundleZeroSection.π B d F)).obj
        (Etale.affineLinearBaseCoefficient A' N hA' B d) ⊗
        (RfPullback A' (VectorBundleZeroSection.π B d F)).obj
          ((Etale.purityScalarExtension φ B).obj K) :=
  (Etale.purityScalarTensor φ (VectorBundleZeroSection.scheme B d F) _ _).hom ≫
    (((Etale.purityScalarPullback φ (VectorBundleZeroSection.π B d F)).hom.app _ ≫
        (RfPullback A' (VectorBundleZeroSection.π B d F)).map
          (purityScalarPower φ N hA hA' B c d)) ⊗ₘ
      (Etale.purityScalarPullback φ (VectorBundleZeroSection.π B d F)).hom.app K)

/-- The finite-reduction equation with both coefficient rings left abstract. This is
exactly the quotient-reduction condition below, factored before substituting the
concrete quotient rings so that kernel checking shares the coefficient structures.
The compact-support coefficient arrow q is the published
`ExceptionalCoefficients.compactSupportMap` on the chosen compactification (the scalar
mate of the proper part at the open extension, then proper direct image of the open
comparison), and b is its published counit transpose `ExceptionalCoefficients.mateMap`,
the geometric adjunct of q⁻¹ ≫ Q_B(ε); q is asserted invertible first, so b is the
actual adjunct. Source: sk-prop-an, Step 6
(blueprint: def-pur-vector-purity-finite-reduction). -/
def PurityScalarReductionEquation {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    [Finite A] [Finite A'] (φ : A →+* A')
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F) : Prop :=
    ∃ hA' : (N : A') = 0,
    ∃ c : (Etale.purityScalarSheaf φ B).obj
        (Scheme.finiteEtaleTateLine B N A hA) ≅
      Scheme.finiteEtaleTateLine B N A' hA',
    ∃ γm : VectorPurityGamma A' N hA' B d F,
    VectorPurityGammaNormalized A' N hN hA' B hB d F γm ∧
    PurityScalarLineNormalization φ N hA hA' B c ∧
    ∀ K : Etale.DerivedCategoryModule A B,
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B K ∨
        K = 𝟙_ _) →
      IsIso (purityScalarSourceMap φ N hA hA' B d F c K) ∧
      IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ
        (HasCompactification.compactification (VectorBundleZeroSection.π B d F))
        ((RfUpper A (VectorBundleZeroSection.π B d F)).obj K)) ∧
      IsIso (Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K) ∧
      (Etale.purityScalarExtension φ (VectorBundleZeroSection.scheme B d F)).map
          (γ.app K) ≫
          Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K =
        purityScalarSourceMap φ N hA hA' B d F c K ≫
          γm.app ((Etale.purityScalarExtension φ B).obj K)

/-- Reduction along the actual positive-level quotient. Its equation includes
K = the monoidal coefficient-unit object, using the same maps as all other components.
Source: sk-prop-an, Step 6 (blueprint: def-pur-vector-purity-finite-reduction). -/
def PurityFiniteReductionEquation (P : PurityFiniteSetting.{u}) [Finite P.Coefficient]
    (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma P.Coefficient N hA B d F) : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level),
    let A' := purityReductionRing P m hm
    letI : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension m) :=
      Padic.finite_coefficientExtensionRing P.coefficients.l P.extension m hm
    letI : Finite A' := inferInstanceAs (Finite (ULift.{u + 1}
      (Padic.coefficientExtensionRing P.coefficients.l P.extension m)))
    let φ : P.Coefficient →+* A' :=
      purityReductionRingMap P m P.level hm P.level_pos hmn
    PurityScalarReductionEquation φ N hN hA B hB d F γ


end WeilConjectures.PurityFiniteSetting
```

All seven declaration signatures, bodies, universes, visibility and five public
imports are identical to the archive. In particular, the coefficient map is the
actual lifted quotient factor map, the rank-zero power uses the published
normalized scalar unit, and the exceptional comparison uses the published
`ExceptionalCoefficients.compactSupportMap` and `mateMap`. No new comparison,
existence witness, theorem assumption or proof hole is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.VectorPurityFiniteReduction | M3 (dispatcher assignment) | Restore seven archived definitions; clean single-file server compile, 34.2 seconds. |
| Sheaf.Paper.VectorBundlePurity | No local claim record; quarantined | Its public import and `VectorBundlePurityConclusion` recover the identical finite-reduction predicate. No adaptation. |

The direct search of `lean/Sheaf`, `lean/WeilConjectures` and `quarantine/Sheaf`
finds the archived `VectorBundlePurity` consumer and no live consumer. The
DAG parent `cor-pur-vector-bundle-purity` still cites this node in its statement
dependencies, proof dependencies and proof steps; its route is preserved.
The existing unit `sk-prop-an` route and all target statements are unchanged.
No module held by another group is edited, and there are no forced adaptations.
The node copy in this delivery is byte-identical to the existing node: its Lean
attachment and all dependencies are retained.

Edge cases checked by reading the constructions: positive levels include m=n;
rank zero uses `purityScalarUnitMap`; the equation explicitly tests the coefficient
unit object as well as constructible finite-Tor objects; no nonempty-base
assumption is introduced. The predicate requires invertibility of the compact
support arrow before using the published total mate, so the zero fallback of
`comparisonInverse` cannot weaken a satisfied reduction equation.

## Status

landed 20261021T021918-L-2792197 2026-10-21 (merge of deliver/M3/Sheaf.Paper.VectorPurityFiniteReduction)
