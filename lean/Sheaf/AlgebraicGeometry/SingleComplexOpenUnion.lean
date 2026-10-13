/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.RelativeMayerVietoris
import Sheaf.AlgebraicGeometry.SingleComplexOpenNestedComparison
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Source-open union gluing for the single-complex comparison

Source: Stacks Project, Tag 0DJ9, induction step.
(blueprint: lem-pc-single-complex-open-union).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Mayer--Vietoris on a union, expressed in the ambient scheme's open coordinates.
Source: Stacks Project, Tag 0DJ9, induction step.
(blueprint: lem-pc-single-complex-open-union).

Proof: Put W = U union V. Inside W take the inverse images of U and V; they cover W,
are quasi-compact, and their intersection identifies with U intersection V. Since
X is quasi-separated over the affine S, the quasi-compact open immersion W → X
is quasi-compact, and W → S is qcqs. Base change identifies W' with X' times_X W.
Restrict K and K' and transport phi by the pullback composition comparisons.
Open restriction preserves quasi-coherent cohomology. Apply relativeMayerVietoris
to the resulting square with source W. Its three comparison hypotheses are the
ambient comparisons on U, V and their intersection: the identifications follow
from singleComplexOpenComparison_nested_isIso_iff, the canonical nested-open
transport. The conclusion is definitionally the ambient comparison on W.
Empty opens cause no exception; a redundant member of the cover
also gives the same comparison. -/
theorem singleComplexOpenComparison_union
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X))
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
  have hKW : schemeDerivedQCohProperty W.toScheme KW :=
    (derivedPullback_tensor_preserve_QCoh W.ι).1 K hK
  have hKW' : schemeDerivedQCohProperty (pullback g' W.ι) KW' :=
    (derivedPullback_tensor_preserve_QCoh (pullback.fst g' W.ι)).1 K' hK'
  have hAqc : IsCompact (A : Set W.toScheme) := W.ι.isCompact_preimage hUqc
  have hBqc : IsCompact (B : Set W.toScheme) := W.ι.isCompact_preimage hVqc
  have hABqc : IsCompact ((A ⊓ B : W.toScheme.Opens) : Set W.toScheme) := by
    simpa only [A, B, Scheme.Hom.preimage_inf] using W.ι.isCompact_preimage hUVqc
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
  exact relativeMayerVietoris fW fW' g gW' sqW KW hKW KW' hKW' φW
    A B hAqc hBqc hABqc hcover hA hB hAB

end AlgebraicGeometry
