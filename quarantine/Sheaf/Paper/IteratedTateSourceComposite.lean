module

public import Sheaf.Paper.PurityTateDatum
public import Sheaf.Paper.PurityCompositionComparisons

/-!
# Iterated Tate source compatibility

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/def-pur-tate-datum.md,
Displayed source-of-purity composite
(blueprint: lem-pur-iterated-tate-source-composite).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.Purity

/--
For two composable smooth maps, the inverse of the canonical comparison
`compositionSourceIdentification` carries the iterated strict Tate source arrow
to the source arrow for the composite.  The
three unshifted factors are the pullback of the datum, the pulled-back Tate
arrow, and the outer Tate arrow; the degree-zero cases use the coefficient unit.
Source: the displayed source-of-purity composite and the canonical comparison
of `def-pur-composition-comparisons` in `def-pur-tate-datum.md`
(blueprint: lem-pur-iterated-tate-source-composite).
Proof: expand the two source-arrow definitions using the pullback-tensor
comparison; use the structural composition equation for the source comparison;
apply Tate-arrow naturality and additivity; use naturality of the pullback
compositor and the even-shift sign convention.  The coefficient-unit clauses
cover `d = 0` and `e = 0` (and hence `d = e = 0`). -/
theorem iteratedTateSourceComposite
    {P : PurityFiniteSetting.{u}}
    {X₀ Y₀ Z₀ : Over (Spec (CommRingCat.of P.field.k₀))}
    {f₀ : X₀ ⟶ Y₀} {h₀ : Y₀ ⟶ Z₀}
    {d e : ℕ}
    {sqₕ : CommSq (P.frobeniusGaloisMap Y₀) (P.frobeniusMap h₀)
      (P.frobeniusMap h₀) (P.frobeniusGaloisMap Z₀)}
    {sq_f : CommSq (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)}
    {sqₕf : CommSq (P.frobeniusGaloisMap X₀)
      (P.frobeniusMap (f₀ ≫ h₀)) (P.frobeniusMap (f₀ ≫ h₀))
      (P.frobeniusGaloisMap Z₀)}
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated h₀.left]
    [SmoothOfRelativeDimension e (P.frobeniusMap h₀)]
    [LocallyOfFiniteType (f₀ ≫ h₀).left] [QuasiCompact (f₀ ≫ h₀).left]
    [IsSeparated (f₀ ≫ h₀).left]
    [SmoothOfRelativeDimension (d + e) (P.frobeniusMap (f₀ ≫ h₀))]
    [LocallyOfFiniteType ((P.frobeniusFiber X₀).left ↘
      Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber X₀).left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType ((P.frobeniusFiber Y₀).left ↘
      Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber Y₀).left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType ((P.frobeniusFiber Z₀).left ↘
      Spec (.of P.field.k))]
    [QuasiCompact ((P.frobeniusFiber Z₀).left ↘ Spec (.of P.field.k))]
    [IsSeparated (P.frobeniusMap f₀)]
    [LocallyOfFiniteType (P.frobeniusMap f₀)]
    [QuasiCompact (P.frobeniusMap f₀)]
    [IsSeparated (P.frobeniusMap h₀)]
    [LocallyOfFiniteType (P.frobeniusMap h₀)]
    [QuasiCompact (P.frobeniusMap h₀)]
    [IsSeparated (P.frobeniusMap (f₀ ≫ h₀))]
    [LocallyOfFiniteType (P.frobeniusMap (f₀ ≫ h₀))]
    [QuasiCompact (P.frobeniusMap (f₀ ≫ h₀))]
    (D : UniformPurityTateDatum P h₀ e sqₕ)
    (D_f : UniformPurityTateDatum P f₀ d sq_f)
    (hcomp : P.frobeniusMap (f₀ ≫ h₀) =
      P.frobeniusMap f₀ ≫ P.frobeniusMap h₀)
    (hKf : D_f.K.obj =
      (P.compositionShiftedPullback (P.frobeniusMap h₀) e).obj D.K.obj)
    (hφf : HEq D_f.φK (φpur (P := P) (sq := sqₕ) D))
    [((P.frobeniusFiber X₀).left).Over (Spec (.of P.field.k))]
    [((P.frobeniusFiber Y₀).left).Over (Spec (.of P.field.k))]
    [((P.frobeniusFiber Z₀).left).Over (Spec (.of P.field.k))] :
    (P.finiteReductionPullback (P.frobeniusGaloisMap X₀)).map
        ((P.compositionShiftedPullback (P.frobeniusMap f₀) d).map
          (eqToHom hKf.symm)) ≫
      (φpur (P := P) (sq := sq_f) D_f).hom ≫
      (P.compositionShiftedPullback (P.frobeniusMap f₀) d).map
          (eqToHom hKf) ≫
      (P.compositionSourceIdentification (P.frobeniusMap f₀)
        (P.frobeniusMap h₀) d e D.K.obj).symm.hom =
    (P.finiteReductionPullback (P.frobeniusGaloisMap X₀)).map
        (P.compositionSourceIdentification (P.frobeniusMap f₀)
          (P.frobeniusMap h₀) d e D.K.obj).symm.hom ≫
      (P.finiteReductionPullback (P.frobeniusGaloisMap X₀)).map
        (eqToHom (congrArg (fun m ↦
          (P.compositionShiftedPullback m (d + e)).obj D.K.obj) hcomp.symm)) ≫
      (φpur (P := P) (sq := sqₕf) { K := D.K, φK := D.φK }).hom ≫
      eqToHom (congrArg (fun m ↦
        (P.compositionShiftedPullback m (d + e)).obj D.K.obj) hcomp) := by
  sorry

end WeilConjectures.Purity
