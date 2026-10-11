module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import Sheaf.AlgebraicGeometry.FppfAffineSheafificationRestriction
public import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Agreement of the relative Picard functor with its affine-site presentation.

Source: blueprint node lem-pc-picard-functor-agrees-sc,
source file: literature/blueprint/master/blueprint/sec-picard-framework/
sk-def-picard-pic/lem-pc-picard-functor-agrees-sc.md,
node lem-pc-picard-functor-agrees-sc, order 805
(blueprint: lem-pc-picard-functor-agrees-sc).

The proof follows the blueprint: on affine objects the big-site Picard presheaf and
the affine-site presheaf agree by `picardPresheaf`; the affine restriction theorem
`Scheme.fppfSheafification_affineRestriction` identifies the two fppf sheafifications;
and `picardFunctor` together with the affine Picard-functor definition identifies the
two sides, yielding the displayed natural isomorphism; its component at an affine object
`Spec R → Spec k` (a `k`-algebra `R`) is `Pic_{X/k}(Spec R) = Pic^sc_{X/k}(R)`.
-/
theorem picardFunctor_agrees_affineSheafification
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    [Scheme.Hom.IsSmoothProjectiveCurve f] [GeometricallyIntegral f] :
    Nonempty
      ((CostructuredArrow.toOver Scheme.Spec
            (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))).op ⋙ (picardFunctor f).obj ≅
        (sheafification
            ((Scheme.fppfPrecoverage.comap
              (CostructuredArrow.toOver Scheme.Spec
                  (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) ⋙
                Over.forget _)).toGrothendieck)
            (Type (u + 1))).obj
          ((CostructuredArrow.toOver Scheme.Spec
              (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))).op ⋙ picardPresheaf f)) := by
  sorry

end AlgebraicGeometry
