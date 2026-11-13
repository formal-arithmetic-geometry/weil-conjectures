/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.RelativeMayerVietoris
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenNestedComparison

/-! # Source-open union gluing for the single-complex comparison

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Mayer--Vietoris on a union, expressed in the ambient scheme's open coordinates. -/
theorem singleComplexOpenComparison_union
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X)
    (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hU : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ U))
    (hV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ V))
    (hUV : IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊓ V))) :
    IsIso (singleComplexOpenComparison f f' g g' sq.w K K' φ (U ⊔ V)) := by
  let W : X.Opens := U ⊔ V
  let fW : W.toScheme ⟶ S := W.ι ≫ f
  let fW' : pullback g' W.ι ⟶ S' := pullback.fst g' W.ι ≫ f'
  let gW' : pullback g' W.ι ⟶ W.toScheme := pullback.snd g' W.ι
  have sqW : IsPullback gW' fW' fW g :=
    (IsPullback.of_hasPullback g' W.ι).flip.paste_vert sq
  let KW := (derivedPullback W.ι).obj K
  let KW' := (derivedPullback (pullback.fst g' W.ι)).obj K'
  let φW : (derivedPullback gW').obj KW ⟶ KW' :=
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' W.ι) W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' W.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' W.ι)).map φ)
  let A : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  let B : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have hWqc : IsCompact (W : Set X) := hUqc.union hVqc
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWqc
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : QuasiCompact W.ι := inferInstance
  have : QuasiCompact fW := inferInstance
  have : QuasiSeparated fW := inferInstance
  have hcover : A ⊔ B = ⊤ := by
    change (W.ι ⁻¹ᵁ U) ⊔ (W.ι ⁻¹ᵁ V) = ⊤
    rw [← Scheme.Hom.preimage_sup]
    exact W.ι_preimage_self
  have hA : IsIso (singleComplexOpenComparison fW fW' g gW' sqW.w KW KW' φW A) :=
    (singleComplexOpenComparison_nested_isIso_iff f f' g g' sq.w K K' φ
      W U le_sup_left).mp hU
  have hB : IsIso (singleComplexOpenComparison fW fW' g gW' sqW.w KW KW' φW B) :=
    (singleComplexOpenComparison_nested_isIso_iff f f' g g' sq.w K K' φ
      W V le_sup_right).mp hV
  have hAB : IsIso
      (singleComplexOpenComparison fW fW' g gW' sqW.w KW KW' φW (A ⊓ B)) := by
    simpa only [A, B, Scheme.Hom.preimage_inf] using
      (singleComplexOpenComparison_nested_isIso_iff f f' g g' sq.w K K' φ
        W (U ⊓ V) (inf_le_left.trans le_sup_left)).mp hUV
  exact relativeMayerVietoris fW fW' g gW' sqW KW KW' φW
    A B hcover hA hB hAB

end AlgebraicGeometry
