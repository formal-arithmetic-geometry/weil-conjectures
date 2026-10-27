module
public import Sheaf.Paper.FiniteTateSourceMap

/-!
# Finite Tate-source comparison calculus

Source: `def-pur-tate-datum.md`, displayed source-of-purity composite
(blueprint: lem-pur-finite-tate-source-comparison-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Finite coefficient reduction intertwines the canonical Tate source map.
The reduction map is the canonical `finiteReductionSourceComparison`; the
Frobenius comparisons are the canonical pullback comparisons, and the target
strict datum is obtained by reducing `φK` through the canonical `C_Y` map.
Source: the finite reduction clause of `def-pur-tate-datum`
(blueprint: lem-pur-finite-tate-source-comparison-calculus).
Proof: expand the source map into the canonical pullback-square comparison and
`φK`, use naturality of the finite pullback and tensor comparisons, apply the
canonical Tate-line reduction equation, and reassociate the shifted tensor
maps. This is the reduction part of the constituent-compatibility assembly;
no exceptional base change is used.
-/
theorem finiteTateSourceComparisonReduction
    (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (K : Scheme.proEtaleDerivedCategory (P.frobeniusFiber Y₀).left P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left K)
    (φK : (P.finiteReductionPullback (P.frobeniusGaloisMap Y₀)).obj K ≅ K) :
    let QX := P.finiteReduction m hm hmn (P.frobeniusFiber X₀).left
    let QY := P.finiteReduction m hm hmn (P.frobeniusFiber Y₀).left
    let GX' := (P.finiteReductionSetting m hm).finiteReductionPullback
      (P.frobeniusGaloisMap X₀)
    let C_Y := P.finiteReductionPullbackComparison m hm hmn
      (P.frobeniusGaloisMap Y₀) K
    let φK' := C_Y.symm ≪≫ QY.mapIso φK
    let ψ := finiteTateSourceMap P f₀ d K φK
    let ψ' := finiteTateSourceMap (P.finiteReductionSetting m hm) f₀ d
      (QY.obj K) φK'
    let a_P := P.finiteReductionSourceComparison m hm hmn
      (P.frobeniusMap f₀) d K
    let C_X := P.finiteReductionPullbackComparison m hm hmn
      (P.frobeniusGaloisMap X₀)
      ((P.compositionShiftedPullback (P.frobeniusMap f₀) d).obj K)
    QX.map ψ.hom ≫ a_P.hom =
      C_X.hom ≫ GX'.map a_P.hom ≫ ψ'.hom := by
  sorry

/-- Ordinary derived pullback along a chosen Cartesian square intertwines the
canonical Tate source map. The two Frobenius comparisons are the canonical
pullback-composition comparisons around the commuting horizontal maps.
Source: the Cartesian-square clause of `def-pur-tate-datum`
(blueprint: lem-pur-finite-tate-source-comparison-calculus).
Proof: expand both source maps using `finiteTateSourceMapOfSquare`; use the
pasted pullback compositors defining `finiteTatePullbackComparison`, then use
bifunctoriality of the ordinary derived pullback and tensor comparison. No
exceptional base change or Cartesian scheme-Frobenius square is asserted.
-/
theorem finiteTateSourceComparisonCartesian
    (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u f' f v) (d : ℕ)
    [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    (gX : X ⟶ X) (gX' : X' ⟶ X') (gY : Y ⟶ Y) (gY' : Y' ⟶ Y')
    (hX : u ≫ gX = gX' ≫ u) (hY : v ≫ gY = gY' ≫ v)
    (hXpb : IsPullback gX f f gY) (hX'pb : IsPullback gX' f' f' gY')
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (φK : (P.finiteReductionPullback gY).obj K ≅ K) :
    let QX := P.finiteReductionPullback u
    let QY := P.finiteReductionPullback v
    let hpb := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
      sq.hom_fst sq.hom_snd
    let C_X := finiteTatePullbackComparison P u gX gX' hX
      ((P.compositionShiftedPullback f d).obj K)
    let C_Y := finiteTatePullbackComparison P v gY gY' hY K
    let φK' := C_Y.symm ≪≫ QY.mapIso φK
    let ψ := finiteTateSourceMapOfSquare P gX gY f d hXpb K φK
    let ψ' := finiteTateSourceMapOfSquare P gX' gY' f' d hX'pb
      (QY.obj K) φK'
    let a_P := P.finiteReductionBaseChangeSource u f' f v hpb d K
    QX.map ψ.hom ≫ a_P.hom =
      C_X.hom ≫ (P.finiteReductionPullback gX').map a_P.hom ≫ ψ'.hom := by
  sorry


end WeilConjectures.PurityFiniteSetting
