/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.RelativeProductGeometricFactors
public import Sheaf.Paper.RelativeExternalPowerRegrouping
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Concrete repeated relative-product constructions

Source: blueprint relative Kunneth construction and the product-domain induction
(blueprint: def-pur-relative-product-constructions).

This definition module owns the specialized constructions below and publicly re-exports
RelativeExternalPower.product/fst/snd, RelativeProduct.D/exchange, the finite-module
projectionMapOfCompactification, and originCompactSupport/originCompositionModel/
originCompositionAmbient. These are the existing concrete definitions; their theorem
modules are implementation imports, not prerequisites asserting their theorems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures.AffineSpaceProduct

/-- Specialize the recorded iterated fibre product to a constant family.
Source: blueprint sk-prop-an (blueprint: def-pur-relative-product-constructions). -/
abbrev space {X B : Scheme.{u}} (f : X ⟶ B) (j : ℕ) : Over B :=
  RelativeExternalPower.product (fun _ ↦ Over.mk f) j

/-- The finite coefficient derived category, in the recorded fixed-module coordinates.
Source: def-pur-conventions (blueprint: def-pur-relative-product-constructions). -/
abbrev D (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) := RelativeProduct.D P T

/-- The concrete derived pullback, with no exceptional adjoint.
Source: def-pur-conventions (blueprint: def-pur-relative-product-constructions). -/
abbrev pull (P : PurityFiniteSetting.{u}) {T U : Scheme.{u}} (a : T ⟶ U) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor

/-- The recorded two projections, specialized to repeated equal factors.
Source: def-pc-fibre-product (blueprint: def-pur-relative-product-constructions). -/
abbrev first {X B : Scheme.{u}} (f : X ⟶ B) (j : ℕ) :=
  RelativeExternalPower.fst (fun _ ↦ Over.mk f) j

/-- The last projection in a repeated relative product.
Source: def-pc-fibre-product (blueprint: def-pur-relative-product-constructions). -/
abbrev last {X B : Scheme.{u}} (f : X ⟶ B) (j : ℕ) :=
  RelativeExternalPower.snd (fun _ ↦ Over.mk f) j

/-- The recorded external tensor in fixed-module coordinates, canonically regrouped.
The first term is M; the successor is Lpi_X* M_j tensor Lpi_Y* M.
Source: relative external-power regrouping, rho_j
(blueprint: def-pur-relative-product-constructions). -/
def external (P : PurityFiniteSetting.{u}) {X B : Scheme.{u}} (f : X ⟶ B)
    (M : D P X) : (j : ℕ) → D P (space f j).left
  | 0 => M
  | j + 1 => (pull P (first f j)).obj (external P f M j) ⊗
      (pull P (last f j)).obj M

/-- The concrete compact-support functor attached to a compactification.
Source: def-pur-conventions (blueprint: def-pur-relative-product-constructions). -/
abbrev support (P : PurityFiniteSetting.{u}) {T U : Scheme.{u}} {a : T ⟶ U}
    (c : Compactification a) :=
  ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c

/-- V_(j+1), with all choices of compactification allowed.
Source: blueprint sk-prop-an (blueprint: def-pur-relative-product-constructions). -/
def image (P : PurityFiniteSetting.{u}) {X B : Scheme.{u}} (f : X ⟶ B)
    (M : D P X) (c : ∀ j, Compactification (space f j).hom) (j : ℕ) : D P B :=
  (support P (c j)).obj (external P f M j)

/-- The concrete projection transformation at two specified coefficients.
Source: def-exchange-projection, finite-stage formula
(blueprint: def-pur-relative-product-constructions). -/
@[irreducible] def projection (P : PurityFiniteSetting.{u})
    {T U : Scheme.{u}} {a : T ⟶ U}
    (c : Compactification a) (K : D P T) (L : D P U) :
    (support P c).obj K ⊗ L ⟶ (support P c).obj (K ⊗ (pull P a).obj L) :=
  ((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app K).app L

/-- The published Koszul braiding, kept opaque to avoid repeatedly expanding its descent.
Source: relative-product tensor symmetries
(blueprint: def-pur-relative-product-constructions). -/
@[irreducible] def symmetry (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (K L : D P T) : K ⊗ L ≅ L ⊗ K := by
  letI := _root_.DerivedCategory.braidedCategory'
    (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
  exact β_ K L

/-- The specified exchange in the m by 1 square, before inversion.
Source: def-exchange-projection and the relative-product geometric factors
(blueprint: def-pur-relative-product-constructions). -/
@[irreducible] def exchange (P : PurityFiniteSetting.{u})
    {X B : Scheme.{u}} (f : X ⟶ B)
    (M : D P X) (c : ∀ j, Compactification (space f j).hom) (j : ℕ) :
    (pull P f).obj (image P f M c j) ⟶
      (support P ((c j).ofIsPullback
        (IsPullback.of_hasPullback (space f j).hom f))).obj
          ((pull P (first f j)).obj (external P f M j)) :=
  (RelativeProduct.exchange P (IsPullback.of_hasPullback (space f j).hom f) (c j)).app
    (external P f M j)

/-- The canonical composition inverse on the origin class, including the canonical
comparisons to all three specified compactifications and the equality of structure maps.
Source: thm-sf-comp-composition, relative-product factor (1)
(blueprint: def-pur-relative-product-constructions). -/
def compositionInverse (P : PurityFiniteSetting.{u}) {T U V : Scheme.{u}}
    (a : T ⟶ U) (b : U ⟶ V) (t : T ⟶ V) (w : a ≫ b = t)
    [QuasiCompact a] [QuasiCompact b]
    (ca : Compactification a) (cb : Compactification b) (ct : Compactification t)
    (K : D P T)
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T K) :
    (support P ct).obj K ≅ (support P cb).obj ((support P ca).obj K) := by
  subst t
  letI := ca.hasCompactification
  letI := cb.hasCompactification
  letI := ct.hasCompactification
  let O := (⟨K, hK⟩ : (ProEtale.DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} P.Coefficient) T).FullSubcategory)
  exact (ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso P.Coefficient
      ct (HasCompactification.compactification (a ≫ b))).app O ≪≫
    (ProEtale.originCompositionAmbient P.Coefficient a b).symm.app O ≪≫
    (ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso P.Coefficient
      (HasCompactification.compactification b) cb).app
        ((ProEtale.originCompactSupport P.Coefficient a).obj O) ≪≫
    (support P cb).mapIso
      ((ProEtale.rightDerivedLowerShriekOfCompactificationEtaleOriginIso P.Coefficient
        (HasCompactification.compactification a) ca).app O)

/-- All actual input domains required before the next relative-product operation.
The base coefficients of the two projection maps are M and V_(j+1), respectively.
These are conclusions of the theorem, never assumptions on the original morphism.
Source: blueprint product-domain induction, Step 3
(blueprint: def-pur-relative-product-constructions). -/
structure StageDomain (P : PurityFiniteSetting.{u}) {X B : Scheme.{u}} (f : X ⟶ B)
    (M : D P X) (c : ∀ j, Compactification (space f j).hom) (j : ℕ) : Prop where
  quasiCompact : QuasiCompact (space f j).hom
  firstInput : ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} P.Coefficient) (space f (j + 1)).left
      ((pull P (first f j)).obj (external P f M j))
  baseM : ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} P.Coefficient) X M
  baseV : ProEtale.DerivedCategory.constructibleFiniteTor
    (ModuleCat.{u + 1} P.Coefficient) B (image P f M c j)
  origin : ProEtale.DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} P.Coefficient) (space f (j + 1)).left (external P f M (j + 1))
  projectionFirst : IsIso (projection P
    ((c j).ofIsPullback (IsPullback.of_hasPullback (space f j).hom f))
      ((pull P (first f j)).obj (external P f M j)) M)
  projectionLast : IsIso (projection P (c 0) M (image P f M c j))
  exchangeIso : IsIso (exchange P f M c j)

/-- The actual six-factor relative map at the next inductive stage. Inversion requires
only the domain proofs that the theorem establishes, not an ambient duality axiom.
Source: thm-sf-kunneth-relative, displayed construction
(blueprint: def-pur-relative-product-constructions). -/
def step (P : PurityFiniteSetting.{u}) {X B : Scheme.{u}} (f : X ⟶ B)
    [QuasiCompact f] (M : D P X) (c : ∀ j, Compactification (space f j).hom)
    (j : ℕ) (d : StageDomain P f M c j) :
    image P f M c (j + 1) ⟶ image P f M c j ⊗ image P f M c 0 := by
  letI := d.quasiCompact
  letI := d.projectionFirst
  letI := d.projectionLast
  letI := d.exchangeIso
  let cq := (c j).ofIsPullback (IsPullback.of_hasPullback (space f j).hom f)
  exact (compositionInverse P (last f j) f (space f (j + 1)).hom
      (pullback.condition.symm) cq (c 0) (c (j + 1)) _ d.origin).hom ≫
    (support P (c 0)).map
      (inv (projection P cq ((pull P (first f j)).obj (external P f M j)) M)) ≫
    (support P (c 0)).map (inv (exchange P f M c j) ⊗ₘ 𝟙 M) ≫
    (support P (c 0)).map (symmetry P X ((pull P f).obj (image P f M c j)) M).hom ≫
    inv (projection P (c 0) M (image P f M c j)) ≫
    (symmetry P B (image P f M c 0) (image P f M c j)).hom


/-- A nonempty tensor power with the same left association as the induction.
Source: blueprint kappa_m formula (blueprint: def-pur-relative-product-constructions). -/
def tensorPower (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) (V : D P B) : ℕ → D P B
  | 0 => V
  | j + 1 => tensorPower P B V j ⊗ V

/-- The recursive kappa_m, using exactly the previously checked finite-stage maps.
Source: blueprint kappa_1=1 and kappa_(m+1)=(kappa_m tensor 1) kappa_(m,1)
(blueprint: def-pur-relative-product-constructions). -/
def comparison (P : PurityFiniteSetting.{u}) {X B : Scheme.{u}} (f : X ⟶ B)
    [QuasiCompact f] (M : D P X) (c : ∀ j, Compactification (space f j).hom)
    (d : ∀ j, StageDomain P f M c j) :
    (j : ℕ) → image P f M c j ⟶ tensorPower P B (image P f M c 0) j
  | 0 => 𝟙 _
  | j + 1 => step P f M c j (d j) ≫ (comparison P f M c d j ⊗ₘ 𝟙 _)

/-- Tensor the given u in every factor and apply the canonical tensor-unit constraints.
Source: blueprint u tensor m, kappa_m display
(blueprint: def-pur-relative-product-constructions). -/
def unitPower (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) {V : D P B}
    (u : V ≅ 𝟙_ (D P B)) : (j : ℕ) → tensorPower P B V j ⟶ 𝟙_ (D P B)
  | 0 => u.hom
  | j + 1 => (unitPower P B u j ⊗ₘ u.hom) ≫ (λ_ (𝟙_ (D P B))).hom

end WeilConjectures.AffineSpaceProduct
