/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorBundleThomClass
public import Sheaf.Paper.VectorBundleThomMaps
public import Sheaf.Paper.VectorBundleThomProduct
public import Sheaf.Paper.FiniteForwardProductSymmetry
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import Sheaf.AlgebraicGeometry.GeometricPointCohomology
import Sheaf.Paper.CompactProductProperSupportCompatibility
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.Paper.FiniteProductCompactification
import Sheaf.Paper.DegreeZeroDerivedMapGluing
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # The specified vector-bundle Thom isomorphism

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-vector-bundle-thom` (blueprint: thm-pur-vector-bundle-thom).

The isomorphism concerns `vectorBundleThomTau`, not an unspecified identification
of its source and target. Base change uses the normalized proper/open exchange;
direct sums use the forward relative compact-support product. The trace is its inverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

variable {P : PurityFiniteSetting.{u}}

variable {B : Scheme.{u}} {hB : B ⟶ Spec (.of P.field.k)}
  [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}

/-- The actual Thom map is invertible, including rank zero and the empty base.
Source: blueprint theorem and proof Steps 1--2 (blueprint: thm-pur-vector-bundle-thom).
Proof: work at the arbitrary finite level in P. The finite twists are rank-one
locally free, bounded constructible and finite Tor by lem-pur-twist-sheaf-locally-free
and lem-asd-etale-finite-twist-pullback. Rank zero is the empty-product identity of
def-pur-vector-bundle-thom-class. L1 of thm-pur-localized-top-chern identifies the
rank-one class with thm-pur-rank-one-thom. L2 and compact base change give the actual
base-change square for tau: the zero-section/projection source square is the identity
by thm-cbc-finite-torsion and thm-sf-comp-composition. On A^j over the fixed field,
induct using lem-pur-compact-product-proper-support-compatibility: the class of the
origin is the compact exterior product of the two origin classes. The finite-Tor
Kunneth map and the induction hypothesis are invertible. Trivialize the bundle on
finite-type Zariski charts using def-amb-finite-locally-free-module and
lem-weil-pbc-symmetric-algebra-free-module-polynomial. The normalized base-change
square identifies tau there with this universal model. Apply the covering criterion
of lem-cbc-proetale-stalk-conservative, including the empty covering of the empty base.
No detection of arbitrary pro-etale sheaves by geometric stalks is used. -/
theorem isIso_vectorBundleThomTau (V : PurityVectorBundle P B hB r) :
    IsIso (vectorBundleThomTau V) := by
  sorry

attribute [instance] isIso_vectorBundleThomTau

/-- The vector-bundle trace is the inverse of the specified Thom map.
Source: blueprint final display (blueprint: thm-pur-vector-bundle-thom). -/
def vectorBundleTrace (V : PurityVectorBundle P B hB r) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (vectorBundleThomInput P V.E r) ⟶
        (P.functorialCupSingle true B).obj (P.constant B) :=
  inv (vectorBundleThomTau V)

/-- The two inverse identities specify the trace, with no additional trace choice.
Source: blueprint final display (blueprint: thm-pur-vector-bundle-thom).
Proof: apply the hom-inverse and inverse-hom identities of the Thom isomorphism. -/
theorem vectorBundleTrace_inverse (V : PurityVectorBundle P B hB r) :
    vectorBundleThomTau V ≫ vectorBundleTrace V = 𝟙 _ ∧
      vectorBundleTrace V ≫ vectorBundleThomTau V = 𝟙 _ := by
  sorry

section BaseChange

variable {B' : Scheme.{u}} (g : B' ⟶ B)
  [IsSeparated (g ≫ hB)] [LocallyOfFiniteType (g ≫ hB)] [QuasiCompact (g ≫ hB)]
  (V : PurityVectorBundle P B hB r) (V' : PurityVectorBundle P B' (g ≫ hB) r)
  (v : V'.E ⟶ V.E) (sq : IsPullback v V'.p V.p g)

/-- Base change preserves the actual Thom morphism for every base change in the
fixed setting; no flatness is assumed. Its source comparison is the constant-unit map.
Source: blueprint compatibility clause, proof Step 2
(blueprint: thm-pur-vector-bundle-thom).
Proof: the normalized generator equation identifies the pulled-back tautological
section with that of V'. Polynomial coordinates show it is regular after every base
change. Apply L2 of thm-pur-localized-top-chern, then naturality of the exchange of
thm-cbc-finite-level-proetale on the supported map. Paste the zero-section and bundle
squares: pi z=id makes their source exchange the identity by the identity and vertical
pasting laws of thm-cbc-finite-torsion and thm-sf-comp-composition. Insert the prescribed
twist pullback. Compactification coherence gives precisely the displayed equality. -/
theorem vectorBundleThomTau_baseChange
    (_linear : VectorBundleThomBaseChange g V V' v sq) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
        (vectorBundleThomTau V) ≫ vectorBundleThomBaseChangeMap g V V' v sq =
      (vectorBundleThomUnitPullback g).hom ≫ vectorBundleThomTau V' := by
  sorry

/-- The vector-bundle trace has the inherited base-change compatibility.
Source: blueprint inverse trace and compatibility (blueprint: thm-pur-vector-bundle-thom).
Proof: invert the preceding Thom square, using the two inverse identities and the
constant-unit source identification. This gives the displayed square for the trace. -/
theorem vectorBundleTrace_baseChange
    (_linear : VectorBundleThomBaseChange g V V' v sq) :
    vectorBundleThomBaseChangeMap g V V' v sq ≫ vectorBundleTrace V' =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
        (vectorBundleTrace V) ≫ (vectorBundleThomUnitPullback g).hom := by
  sorry

end BaseChange

section DirectSum

variable {s : ℕ} (V : PurityVectorBundle P B hB (r + s))
  (V₁ : PurityVectorBundle P B hB r) (V₂ : PurityVectorBundle P B hB s)
  (e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔)

/-- The coefficient-unit multiplication Hom type in the published derived tensor.
Source: blueprint Step 5 (blueprint: thm-pur-vector-bundle-thom). -/
abbrev VectorBundleThomUnitMultiplyHom (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) :=
  ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B).obj
    ((P.functorialCupSingle true B).obj (P.constant B))).obj
    ((P.functorialCupSingle true B).obj (P.constant B)) ⟶
      (P.functorialCupSingle true B).obj (P.constant B)

/-- Unit multiplication is the native single-complex root multiplication at twist zero.
Source: blueprint A_B tensor A_B = A_B (blueprint: thm-pur-vector-bundle-thom). -/
structure VectorBundleThomUnitMultiplySpec (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (hB : B ⟶ Spec (.of P.field.k)) (f : VectorBundleThomUnitMultiplyHom P B) : Prop where
  /-- The ordinary and derived coefficient maps are both fixed.
  Source: blueprint Step 5 (blueprint: thm-pur-vector-bundle-thom). -/
  normalized :
    ∃ μ : (P.constant B :
        Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)) ⊗
          P.constant B ⟶ P.constant B,
      HEq μ (P.functorialCupTwistProduct true B hB 0 0).hom ∧
        HEq f (ProEtale.cupDerivedCoefficientMap μ)

/-- The normalized unit multiplication exists uniquely in the published tensor.
Source: blueprint coefficient-unit identification (blueprint: thm-pur-vector-bundle-thom).
Proof: twist zero is the constant coefficient unit. Its prescribed root multiplication
is the ordinary unit multiplication. Apply the native single-complex comparison and
transport the identical tensor presentations; heterogeneous equality fixes both maps. -/
theorem existsUnique_vectorBundleThomUnitMultiply (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (hB : B ⟶ Spec (.of P.field.k)) :
    ∃! f : VectorBundleThomUnitMultiplyHom P B, VectorBundleThomUnitMultiplySpec P B hB f := by
  sorry

/-- Coefficient-unit multiplication in the derived category, using the zero-twist
normalization rather than a chosen scalar trivialization.
Source: blueprint A_B tensor A_B = A_B (blueprint: thm-pur-vector-bundle-thom). -/
def vectorBundleThomUnitMultiply (P : PurityFiniteSetting.{u}) (B : Scheme.{u})
    (hB : B ⟶ Spec (.of P.field.k)) : VectorBundleThomUnitMultiplyHom P B :=
  (existsUnique_vectorBundleThomUnitMultiply P B hB).exists.choose

/-- The ordinary tensor-square equation, with heterogeneous equalities identifying
presentations of all five specified arrows. Every arrow is fixed by those equalities.
Source: blueprint direct-sum display (blueprint: thm-pur-vector-bundle-thom). -/
def VectorBundleThomTensorEquation {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    (L₁ L₂ M₁ M₂ U V : C) {α₁ α₂ α₃ α₄ α₅ : Sort (w + 1)}
    (f₁ : α₁) (f₂ : α₂) (f : α₃) (product : α₄) (unit : α₅) : Prop :=
  ∃ (a : L₁ ⟶ M₁) (b : L₂ ⟶ M₂) (c : U ⟶ V)
    (p : (T.obj M₁).obj M₂ ⟶ V) (m : (T.obj L₁).obj L₂ ⟶ U),
    HEq a f₁ ∧ HEq b f₂ ∧ HEq c f ∧ HEq p product ∧ HEq m unit ∧
      vectorBundleThomTensorMap T a b ≫ p = m ≫ c

/-- The reverse trace-square equation in one shared category presentation, retaining
heterogeneous equalities to each trace, the actual product and unit multiplication.
Source: blueprint inverse trace display (blueprint: thm-pur-vector-bundle-thom). -/
def VectorBundleTraceTensorEquation {C : Type v} [Category.{w} C] (T : C ⥤ C ⥤ C)
    (L₁ L₂ M₁ M₂ U V : C) {α₁ α₂ α₃ α₄ α₅ : Sort (w + 1)}
    (f₁ : α₁) (f₂ : α₂) (f : α₃) (product : α₄) (unit : α₅) : Prop :=
  ∃ (a : M₁ ⟶ L₁) (b : M₂ ⟶ L₂) (c : V ⟶ U)
    (p : (T.obj M₁).obj M₂ ⟶ V) (m : (T.obj L₁).obj L₂ ⟶ U),
    HEq a f₁ ∧ HEq b f₂ ∧ HEq c f ∧ HEq p product ∧ HEq m unit ∧
      p ≫ c = vectorBundleThomTensorMap T a b ≫ m

/-- Direct sums preserve the specified Thom maps under the canonical relative product.
The equality is written in the forward direction, inverse to kappa_B of the proof.
Source: blueprint direct-sum compatibility (blueprint: thm-pur-vector-bundle-thom).
Proof: on the fixed-field trivial models L3 of thm-pur-localized-top-chern and the
coordinate-block transversality identify the supported class with the cup product.
The properly supported product equation of lem-pur-compact-product-proper-support-compatibility
then gives the same identity after compact support. The relative product is precisely
this exterior product by lem-pur-finite-product-compactification, reversing the six
arrows of sk-thm-sf-kunneth-relative. Trivialize the two bundles simultaneously.
Base change transports the model identity to these charts. By the Thom isomorphism
all three compact images are in degree zero, so lem-pur-degree-zero-derived-map-gluing
identifies the actual global maps. Zero ranks give the empty tensor-unit product. -/
theorem vectorBundleThomTau_directSum :
    VectorBundleThomTensorEquation
      (ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B)
      ((P.functorialCupSingle true B).obj (P.constant B))
      ((P.functorialCupSingle true B).obj (P.constant B))
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V₁.p).obj
        (vectorBundleThomInput P V₁.E r))
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V₂.p).obj
        (vectorBundleThomInput P V₂.E s))
      ((P.functorialCupSingle true B).obj (P.constant B))
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (vectorBundleThomInput P V.E (r + s)))
      (vectorBundleThomTau V₁) (vectorBundleThomTau V₂) (vectorBundleThomTau V)
      (vectorBundleThomSumProduct V V₁ V₂ e) (vectorBundleThomUnitMultiply P B hB) := by
  sorry

/-- The trace of a direct sum is the tensor product of the two traces followed by
unit multiplication, under the same forward relative product identification.
Source: blueprint inverse trace and direct sums (blueprint: thm-pur-vector-bundle-thom).
Proof: cancel the invertible tensor of the two Thom maps in the preceding equality
and use both inverse identities. Equivalently this is
tr_sum = (tr_1 tensor tr_2) kappa_B, with the coefficient-unit identification. -/
theorem vectorBundleTrace_directSum :
    VectorBundleTraceTensorEquation
      (ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B)
      ((P.functorialCupSingle true B).obj (P.constant B))
      ((P.functorialCupSingle true B).obj (P.constant B))
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V₁.p).obj
        (vectorBundleThomInput P V₁.E r))
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V₂.p).obj
        (vectorBundleThomInput P V₂.E s))
      ((P.functorialCupSingle true B).obj (P.constant B))
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (vectorBundleThomInput P V.E (r + s)))
      (vectorBundleTrace V₁) (vectorBundleTrace V₂) (vectorBundleTrace V)
      (vectorBundleThomSumProduct V V₁ V₂ e) (vectorBundleThomUnitMultiply P B hB) := by
  sorry

end DirectSum

end WeilConjectures.PurityFiniteSetting
