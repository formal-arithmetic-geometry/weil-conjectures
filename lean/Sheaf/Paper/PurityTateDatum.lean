/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.TwistFrobeniusScalar
public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions

/-!
# Strict geometric-Weil and Tate data

This file fixes one coefficient stage.  Its object is the published finite-Tor
constructible pro-etale category, and its only data are a complex and its strict
geometric-Frobenius isomorphism.  The displayed induced maps use the canonical
scheme-Frobenius comparison, Tate-line normalization, pullback-tensor comparison,
and smooth exceptional exchange from the preceding nodes.

Source: the current blueprint statement (blueprint: def-pur-tate-datum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace WeilConjectures.Purity

/-- A strict geometric-Weil datum at the fixed coefficient stage `P.Ring`.
Source: blueprint `def-pur-tate-datum` (blueprint: def-pur-tate-datum).
The carrier is the actual bounded constructible finite-Tor category.
The only data are the complex and its strict geometric-Frobenius isomorphism.
(blueprint: def-pur-tate-datum) -/
structure UniformPurityTateDatum (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    (sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀))
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] where
  K : finiteTorConstructibleCategory P.coefficients.l P.extension P.level
    P.level_pos (P.frobeniusFiber Y₀).left
  φK : (P.finiteReductionPullback (P.frobeniusGaloisMap Y₀)).obj K.obj ≅ K.obj

/-- The finite-reduction form of the recorded scheme-Frobenius comparison.
Source: scheme-Frobenius clause (blueprint: def-pur-tate-datum). -/
noncomputable def finiteReductionSchemeGeometricFrobeniusComparison
    (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    P.finiteReductionPullback (P.frobeniusSchemeMap T₀) ≅
      P.finiteReductionPullback (P.frobeniusGaloisMap T₀) :=
  (P.finiteReductionRawPullbackModel (P.frobeniusSchemeMap T₀)).symm ≪≫
    P.schemeGeometricFrobeniusComparison T₀ ≪≫
    P.finiteReductionRawPullbackModel (P.frobeniusGaloisMap T₀)

/-- The scheme-Frobenius form `u_K = φ_K ∘ κ_{Y,K}`, using the recorded
`schemeGeometricFrobeniusComparison` itself.
Source: scheme-Frobenius form (blueprint: def-pur-tate-datum). -/
noncomputable def UniformPurityTateDatum.uK
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    {sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    (D : UniformPurityTateDatum P f₀ d sq) :
    (P.finiteReductionPullback (P.frobeniusSchemeMap Y₀)).obj D.K.obj ≅ D.K.obj :=
  (finiteReductionSchemeGeometricFrobeniusComparison P Y₀).app D.K.obj ≪≫ D.φK

/-- The canonical Tate line map at exponent `r` on the fixed setting `P` and
its geometric-Frobenius base change.
Source: Tate normalization clause (blueprint: def-pur-tate-datum). -/
noncomputable def UniformPurityTateDatum.tau
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    {sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    (_D : UniformPurityTateDatum P f₀ d sq) (r : ℤ) :=
  letI : IsIso (P.frobeniusGaloisMap Y₀) :=
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.1
  FrobeniusCoefficientTwists.finiteDerivedLineMap P.coefficients.l
    P.extension (P.frobeniusGaloisMap Y₀) (P.level - 1) r

/-- The finite and integral Tate-line actions are the normalized scalar actions
of `twist_frobenius_scalar_finite_integral`; its value on exponent `r` is the
canonical `q⁻¹`-power scalar on the Tate line.  Source: the Tate normalization
clause of the blueprint (blueprint: def-pur-tate-datum). -/
noncomputable def tau_scalar
    (P : PurityFiniteSetting.{u}) (m : ℤ) :=
  TwistFrobeniusScalar.twist_frobenius_scalar_finite_integral
    P.field P.coefficients.l P.coefficients.different P.extension m

/-- The four `IsOver` proofs for the twisted Frobenius square.  The left
corners use `a'_T = g_{T,γ} ≫ a_T` and the right corners use `a_T`.
Source: the first Cartesian square (blueprint: def-pur-tate-datum).
Proof: the equations for the horizontal arrows are the definitions of `a′_T`.
For the right vertical arrow use the base-change structure equation of `f₀`.
Compose it with `g_X`, use the first Frobenius square, and reassociate to
obtain the equation for the left vertical arrow. -/
theorem twistedFrobeniusSquareOver
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    {sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    [LocallyOfFiniteType ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [IsSeparated (P.frobeniusMap f₀)] [LocallyOfFiniteType (P.frobeniusMap f₀)]
    [QuasiCompact (P.frobeniusMap f₀)]
 :
  let X : Scheme := (P.frobeniusFiber X₀).left
  let Y : Scheme := (P.frobeniusFiber Y₀).left
  let X' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).left
  let Y' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).left
  let aX : X ⟶ Spec (.of P.field.k) := (P.frobeniusFiber X₀).hom
  let aY : Y ⟶ Spec (.of P.field.k) := (P.frobeniusFiber Y₀).hom
  let aX' : X' ⟶ Spec (.of P.field.k) :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).hom
  let aY' : Y' ⟶ Spec (.of P.field.k) :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom
  let iX : X.Over (Spec (.of P.field.k)) := ⟨aX⟩
  let iY : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let iX' : X'.Over (Spec (.of P.field.k)) := ⟨aX'⟩
  let iY' : Y'.Over (Spec (.of P.field.k)) := ⟨aY'⟩
  let u : X' ⟶ X := P.frobeniusGaloisMap X₀
  let f' : X' ⟶ Y' := P.frobeniusMap f₀
  let f : X ⟶ Y := P.frobeniusMap f₀
  let v : Y' ⟶ Y := P.frobeniusGaloisMap Y₀
  @Scheme.Hom.IsOver X' X u (Spec (.of P.field.k)) iX' iX ∧
    @Scheme.Hom.IsOver X' Y' f' (Spec (.of P.field.k)) iX' iY' ∧
    @Scheme.Hom.IsOver X Y f (Spec (.of P.field.k)) iX iY ∧
    @Scheme.Hom.IsOver Y' Y v (Spec (.of P.field.k)) iY' iY := by
  dsimp only
  have hf : P.frobeniusMap f₀ ≫ (P.frobeniusFiber Y₀).hom =
      (P.frobeniusFiber X₀).hom :=
    Over.w ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map f₀)
  refine ⟨⟨rfl⟩, ⟨?_⟩, ⟨hf⟩, ⟨rfl⟩⟩
  change P.frobeniusMap f₀ ≫
      (P.frobeniusGaloisMap Y₀ ≫ (P.frobeniusFiber Y₀).hom) =
    P.frobeniusGaloisMap X₀ ≫ (P.frobeniusFiber X₀).hom
  rw [← Category.assoc, ← sq.w, Category.assoc, hf]

/-- The finite-type and smoothness instances on the same twisted corners and arrow.
Source: the Frobenius base-change square (blueprint: def-pur-tate-datum).
Proof: `schemeGeometricFrobenius_squares` makes each `g_T` an isomorphism.
The twisted structure map is its composite with the original finite-type,
quasi-compact structure map, hence has both properties. The vertical map
is the same underlying scheme morphism as `f`, so separatedness, finite type,
quasi-compactness and relative smooth dimension are unchanged. -/
theorem twistedFrobeniusFiniteClasses
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    {sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    [LocallyOfFiniteType ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [IsSeparated (P.frobeniusMap f₀)] [LocallyOfFiniteType (P.frobeniusMap f₀)]
    [QuasiCompact (P.frobeniusMap f₀)] :
  let X' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).left
  let Y' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).left
  let f' : X' ⟶ Y' := P.frobeniusMap f₀
  letI : X'.Over (Spec (.of P.field.k)) :=
    ⟨(Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).hom⟩
  letI : Y'.Over (Spec (.of P.field.k)) :=
    ⟨(Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom⟩
  LocallyOfFiniteType (X' ↘ Spec (.of P.field.k)) ∧
    QuasiCompact (X' ↘ Spec (.of P.field.k)) ∧
    LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k)) ∧
    QuasiCompact (Y' ↘ Spec (.of P.field.k)) ∧
    IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧
    SmoothOfRelativeDimension d f' := by
  cases sq
  have : LocallyOfFiniteType (P.frobeniusFiber X₀).hom :=
    inferInstanceAs
      (LocallyOfFiniteType ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k)))
  have : QuasiCompact (P.frobeniusFiber X₀).hom :=
    inferInstanceAs (QuasiCompact ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k)))
  have : LocallyOfFiniteType (P.frobeniusFiber Y₀).hom :=
    inferInstanceAs
      (LocallyOfFiniteType ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k)))
  have : QuasiCompact (P.frobeniusFiber Y₀).hom :=
    inferInstanceAs (QuasiCompact ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k)))
  have h := P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d
  have : IsIso (P.frobeniusGaloisMap X₀) := h.1
  have : IsIso (P.frobeniusGaloisMap Y₀) := h.2.1
  change LocallyOfFiniteType
      (P.frobeniusGaloisMap X₀ ≫ (P.frobeniusFiber X₀).hom) ∧
    QuasiCompact (P.frobeniusGaloisMap X₀ ≫ (P.frobeniusFiber X₀).hom) ∧
    LocallyOfFiniteType (P.frobeniusGaloisMap Y₀ ≫ (P.frobeniusFiber Y₀).hom) ∧
    QuasiCompact (P.frobeniusGaloisMap Y₀ ≫ (P.frobeniusFiber Y₀).hom) ∧
    IsSeparated (P.frobeniusMap f₀) ∧ LocallyOfFiniteType (P.frobeniusMap f₀) ∧
    QuasiCompact (P.frobeniusMap f₀) ∧ SmoothOfRelativeDimension d (P.frobeniusMap f₀)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Source: smooth-purity clause (blueprint: def-pur-tate-datum).  This is
built from the recorded pullback-tensor comparison, the first Frobenius
pullback square and shift, then the root-chart Tate identity and `Lf^*(φK)`. -/
noncomputable def φpur
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} {f₀ : X₀ ⟶ Y₀} {d : ℕ}
    {sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    [LocallyOfFiniteType ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [IsSeparated (P.frobeniusMap f₀)] [LocallyOfFiniteType (P.frobeniusMap f₀)]
    [QuasiCompact (P.frobeniusMap f₀)]
    (D : UniformPurityTateDatum P f₀ d sq) :
    (P.finiteReductionPullback (P.frobeniusGaloisMap X₀)).obj
        ((P.compositionShiftedPullback (P.frobeniusMap f₀) d).obj D.K.obj) ≅
      (P.compositionShiftedPullback (P.frobeniusMap f₀) d).obj D.K.obj := by
  let X : Scheme := (P.frobeniusFiber X₀).left
  let Y : Scheme := (P.frobeniusFiber Y₀).left
  let X' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).left
  let Y' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).left
  let aX : X ⟶ Spec (.of P.field.k) := (P.frobeniusFiber X₀).hom
  let aY : Y ⟶ Spec (.of P.field.k) := (P.frobeniusFiber Y₀).hom
  let aX' : X' ⟶ Spec (.of P.field.k) :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).hom
  let aY' : Y' ⟶ Spec (.of P.field.k) :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom
  let iX : X.Over (Spec (.of P.field.k)) := ⟨aX⟩
  let iY : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let iX' : X'.Over (Spec (.of P.field.k)) := ⟨aX'⟩
  let iY' : Y'.Over (Spec (.of P.field.k)) := ⟨aY'⟩
  have hOver := twistedFrobeniusSquareOver (P := P) (sq := sq) f₀ d
  have hCls := twistedFrobeniusFiniteClasses (P := P) (sq := sq) f₀ d
  have hsq : IsPullback (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀) :=
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.1
  exact @PurityFiniteSetting.finiteReductionBaseChangeSource P X X' Y Y' iX iX'
    (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀) (P.frobeniusMap f₀)
    (P.frobeniusGaloisMap Y₀) hsq d D.K.obj ≪≫
      (P.compositionShiftedPullback (P.frobeniusMap f₀) d).mapIso D.φK

/-- Source: exceptional-inverse-image clause (blueprint: def-pur-tate-datum).
This is the recorded finite smooth exchange on the twisted first square,
followed by `(compositionExceptional f).mapIso D.φK`. -/
noncomputable def φ!
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} {f₀ : X₀ ⟶ Y₀} {d : ℕ}
    {sq : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    [LocallyOfFiniteType ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [IsSeparated (P.frobeniusMap f₀)] [LocallyOfFiniteType (P.frobeniusMap f₀)]
    [QuasiCompact (P.frobeniusMap f₀)]
    (D : UniformPurityTateDatum P f₀ d sq) :
    (P.finiteReductionPullback (P.frobeniusGaloisMap X₀)).obj
        ((P.compositionExceptional (P.frobeniusMap f₀)).obj D.K.obj) ≅
      (P.compositionExceptional (P.frobeniusMap f₀)).obj D.K.obj := by
  let X : Scheme := (P.frobeniusFiber X₀).left
  let Y : Scheme := (P.frobeniusFiber Y₀).left
  let X' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).left
  let Y' : Scheme :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).left
  let aX : X ⟶ Spec (.of P.field.k) := (P.frobeniusFiber X₀).hom
  let aY : Y ⟶ Spec (.of P.field.k) := (P.frobeniusFiber Y₀).hom
  let aX' : X' ⟶ Spec (.of P.field.k) :=
    (Over.mk ((P.frobeniusGaloisMap X₀) ≫ (P.frobeniusFiber X₀).hom)).hom
  let aY' : Y' ⟶ Spec (.of P.field.k) :=
    (Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom
  let iX : X.Over (Spec (.of P.field.k)) := ⟨aX⟩
  let iY : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let iX' : X'.Over (Spec (.of P.field.k)) := ⟨aX'⟩
  let iY' : Y'.Over (Spec (.of P.field.k)) := ⟨aY'⟩
  have hOver := twistedFrobeniusSquareOver (P := P) (sq := sq) f₀ d
  have hCls := twistedFrobeniusFiniteClasses (P := P) (sq := sq) f₀ d
  have hsq : IsPullback (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀) :=
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.1
  exact @PurityFiniteSetting.finiteReductionSmoothExchange P X X' Y Y' iX iX' iY iY'
    inferInstance inferInstance hCls.1 hCls.2.1 inferInstance inferInstance
    hCls.2.2.1 hCls.2.2.2.1
    (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀) (P.frobeniusMap f₀)
    (P.frobeniusGaloisMap Y₀) hOver.2.2.2 hOver.2.2.1 hOver.2.1
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    hsq d inferInstance inferInstance D.K.obj D.K.property ≪≫
      (P.compositionExceptional (P.frobeniusMap f₀)).mapIso D.φK

/-- The strict Weil datum at a coefficient stage, on the Frobenius base-change of `Y₀`.
The source object is pinned to `a'_Y = g_{Y,γ} ≫ a_Y`; `Over.homMk` bundles
the actual geometric-Frobenius map with its defining structure equation.
The carrier is bounded constructible in the condensed category, and `finiteTor`
imposes finite Tor amplitude, giving exactly the `D^b_ctf` stage.
Source: the uniform coefficient clause of the blueprint
(blueprint: def-pur-tate-datum). -/
structure CondensedStrictWeilDatum
    (P : PurityFiniteSetting.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar P.field.k).Prime]
    [Fact (ringChar P.field.k ≠ ℓ)] {Y₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    [LocallyOfFiniteType (P.frobeniusFiber Y₀).hom]
    [QuasiCompact (P.frobeniusFiber Y₀).hom]
    [IsSeparated (P.frobeniusFiber Y₀).hom]
    [LocallyOfFiniteType (Over.mk
      ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom]
    [QuasiCompact (Over.mk
      ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom]
    [IsSeparated (Over.mk
      ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom)).hom]
    where
  K : let _ := (AlgebraicGeometry.ProEtale.upperStarFromPoint
      (P.frobeniusFiber Y₀).left).monObjObj Λ
    AlgebraicGeometry.ProEtale.BoundedConstructible
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ (P.frobeniusFiber Y₀).left)
  finiteTor : _root_.DerivedCategory.finiteTorAmplitude _ K.obj
  φK :
    let gY : Over.mk ((P.frobeniusGaloisMap Y₀) ≫ (P.frobeniusFiber Y₀).hom) ⟶
        P.frobeniusFiber Y₀ := Over.homMk (P.frobeniusGaloisMap Y₀) rfl
    (AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar
      Λ ℓ gY).obj K ≅ K

/-- The published fixed-pair Weil structure used by the rational/common-stage
coefficient realizations.  Source: the Weil-complex clause of the blueprint
(blueprint: def-pur-tate-datum). -/
abbrev sfWeilStructure
    (D : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :=
  sfWeilComplex D ℓ hℓ Y₀ E

end WeilConjectures.Purity
