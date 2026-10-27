module

public import Sheaf.Paper.CompactSupportStrictScalarCompositionPrelude

/-! # Support realization of strict scalar comparison

The image-tower comparison is transported through the chosen support models,
reduction balancing, and retained-level maps. This is the support realization
part of the compact-support composition argument.
(blueprint: lem-pur-compact-support-strict-scalar-composition-support-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- The support realization maps are coherent with the composite tower
associator. This is the postcomposition part of the strict compact-support
composition calculation; it contains no image-level mate comparison.
Source: returned comparison Step 11, proof Steps 3--6.
(blueprint: lem-pur-compact-support-strict-scalar-composition-support-realization).
Proof: expand the arrow for F ⊂ L. The selection square is the localized identity
square, so it commutes with the support-model maps for F and those cancel. Arithmetic
selection is restriction along an index functor and acts termwise on the ordinary
proper/open mates, so the F-level selection through the image commutes with the
L/F comparison. Naturality of that comparison moves the F-level balancing in front.
What remains is an equation of isomorphisms under the L-image. The balancing maps
compose: both sides satisfy the counit equation of reductionBalancing_existsUnique,
because the ordinary balancings compose by ((x ⊗ b) ⊗ d) ↦ x ⊗ bd. The image
selections for e and h compose through compositionRetained to the one for h * e.
The L support model is natural in compositionCompleted. -/
theorem supportRealization_coherence
    (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (comparison l F L j c).app
        ((T l E F i X).obj ((reduction l E X SE).obj M)) ≫
      (image l L c).map ((compositionTower l E F i L j X).hom.app
        ((reduction l E X SE).obj M)) ≫
      (image l L c).map
        ((reductionBalancing l E L (j.comp i) X SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos)).hom.app M) ≫
      (reindexImage l L c (h * e) (one_le_mul hhpos hepos)).inv.app
        ((reduction l L X SL).obj
          ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)) ≫
      (subsequence l L Y (h * e)).map
        ((supportModel l L c SL).inv.app
          ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)) =
    (T l F L j Y).map
        ((image l F c).map
          ((reductionBalancing l E F i X SE SF e he hepos).hom.app M)) ≫
      (T l F L j Y).map
        ((reindexImage l F c e hepos).inv.app
          ((reduction l F X SF).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (T l F L j Y).map
        ((subsequence l F Y e).map
          ((supportModel l F c SF).inv.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (compositionSelection l F L j Y e).hom.app
        ((support l F c SF).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
      (subsequence l L Y e).map
        ((arrow l F L j c SF SL h hh hhpos).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
      (compositionRetained l L Y e h hepos hhpos).hom.app
        ((support l L c SL).obj
          ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
      (subsequence l L Y (h * e)).map
        ((support l L c SL).map
          ((compositionCompleted l E F i L j X).hom.app M)) := by
  sorry

end Geometry
end WeilConjectures.PurStrictScalar
