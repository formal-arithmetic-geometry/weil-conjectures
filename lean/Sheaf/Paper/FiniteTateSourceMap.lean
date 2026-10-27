module
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.Paper.FiniteReductionComparisons

/-!
# Canonical finite Tate source map

Source: `def-pur-tate-datum.md`, source-of-purity composite
(blueprint: def-pur-finite-tate-source-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting


/-- Canonical source map for a Cartesian Frobenius square.  The source side is
formed on the twisted over-structure `g_X ≫ a_X`, exactly as in `Purity.φpur`.
The over-structures on `X` and `Y` are explicit hypotheses of the square.
Source: `def-pur-tate-datum.md`, displayed source-of-purity composite, applied to
an arbitrary Frobenius-type pullback square
(blueprint: def-pur-finite-tate-source-map). -/
noncomputable def finiteTateSourceMapOfSquare
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (gX : X ⟶ X) (gY : Y ⟶ Y) (f : X ⟶ Y) (d : ℕ)
    (hsq : IsPullback gX f f gY)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (φK : (P.finiteReductionPullback gY).obj K ≅ K) :
    (P.finiteReductionPullback gX).obj
        ((P.compositionShiftedPullback f d).obj K) ≅
      (P.compositionShiftedPullback f d).obj K := by
  let X' : Scheme := (Over.mk (gX ≫ (X ↘ Spec (.of P.field.k)))).left
  let Y' : Scheme := (Over.mk (gY ≫ (Y ↘ Spec (.of P.field.k)))).left
  let aX' : X' ⟶ Spec (.of P.field.k) := (Over.mk
    (gX ≫ (X ↘ Spec (.of P.field.k)))).hom
  let aY' : Y' ⟶ Spec (.of P.field.k) := (Over.mk
    (gY ≫ (Y ↘ Spec (.of P.field.k)))).hom
  let iX' : X'.Over (Spec (.of P.field.k)) := ⟨aX'⟩
  let iY' : Y'.Over (Spec (.of P.field.k)) := ⟨aY'⟩
  exact @PurityFiniteSetting.finiteReductionBaseChangeSource P X X' Y Y' ‹_› iX'
    gX f f gY hsq d K ≪≫ (P.compositionShiftedPullback f d).mapIso φK

/-- Canonical comparison of two pullback composites around a commuting square:
the inverse compositor, the transport along the square's equation, and the
compositor.  Source: `def-pur-tate-datum.md`, ordinary pullback comparison
factors `C_T` of the source-of-purity composite
(blueprint: def-pur-finite-tate-source-map). -/
noncomputable def finiteTatePullbackComparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    (v : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : v ≫ g = g' ≫ v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionPullback v).obj
        ((P.finiteReductionPullback g).obj K) ≅
      (P.finiteReductionPullback g').obj
        ((P.finiteReductionPullback v).obj K) :=
  (P.finiteReductionPullbackCompositor v g K).symm ≪≫
    eqToIso (congrArg (fun q ↦ (P.finiteReductionPullback q).obj K) h) ≪≫
    P.finiteReductionPullbackCompositor g' v K

/-- The canonical finite Tate source map, with the twisted source structure
`g_X ≫ a_X` used by `Purity.φpur`.  This is its unbundled definitionally equal
finite-reduction base-change composite, followed by the strict map `φK`.
Source: `def-pur-tate-datum.md`, displayed source-of-purity composite
`ψ = (F φ_K ⊗ τ_d)[2d] b_{f,K}` (blueprint: def-pur-finite-tate-source-map).
-/
noncomputable def finiteTateSourceMap
    (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    (K : Scheme.proEtaleDerivedCategory (P.frobeniusFiber Y₀).left P.Ring)
    (φK : (P.finiteReductionPullback (P.frobeniusGaloisMap Y₀)).obj K ≅ K) :
    (P.finiteReductionPullback (P.frobeniusGaloisMap X₀)).obj
        ((P.compositionShiftedPullback (P.frobeniusMap f₀) d).obj K) ≅
      (P.compositionShiftedPullback (P.frobeniusMap f₀) d).obj K := by
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
  have hsq : IsPullback (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀) :=
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.1
  exact @PurityFiniteSetting.finiteReductionBaseChangeSource P X X' Y Y' iX iX'
    (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀) (P.frobeniusMap f₀)
    (P.frobeniusGaloisMap Y₀) hsq d K ≪≫
      (P.compositionShiftedPullback (P.frobeniusMap f₀) d).mapIso φK

end WeilConjectures.PurityFiniteSetting
