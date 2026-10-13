/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison

/-! # Comparison invariance under nested source-open restriction

Source: Stacks Project, Tag 0DJ9, restriction to a source open in the induction step,
and Tag 08HY, canonical base-change map.
(blueprint: lem-pc-single-complex-open-nested-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Computing the comparison on a smaller open after restricting to a larger open
preserves and reflects invertibility. This is a coordinate transport statement:
it has no cover, compactness, quasi-coherence or local-isomorphism hypotheses.
Source: Stacks Project, Tag 0DJ9, induction step on a source open, and Tag 08HY.
(blueprint: lem-pc-single-complex-open-nested-comparison).

Proof: Write A = W.ι⁻¹(Z). The composite A → W → X has image Z since Z ≤ W.
The canonical isomorphism A ≅ Z over X identifies the smaller source. Pasting
pullback squares identifies (X' ×_X W) ×_W A with X' ×_X Z over both X' and Z.
The derived pullback composition comparisons identify the twice-restricted K
with its restriction to Z, and the twice-restricted K' with its restriction to
X' ×_X Z. Their associativity law and naturality with respect to φ identify the
twice-restricted coefficient morphism with the coefficient morphism restricted
once. More explicitly, let e : A ≅ Z be the image isomorphism and let
e′ : ((X′ ×_X W) ×_W A) ≅ (X′ ×_X Z) be the pullback-pasting
isomorphism. The structural maps to S and S′ agree after composition
with e and e′. The pullback comparisons and their right-adjoint mates
therefore identify the two comparison domains and codomains; the units
and counits for e and e′ are invertible since these maps are isomorphisms.
The open immersion W → X itself needs no invertible adjunction unit.
The direct-image comparisons are the mates of these same pullback
comparisons under the canonical derived adjunctions. Transpose the two
base-change arrows under their direct-image adjunctions: by Tag 08HY both
transposes consist of the pullback composition comparison followed by the
counit of the source adjunction. Naturality of that counit and the associativity
law identify the transposes. Thus the two comparison arrows are conjugate by
isomorphisms on their domain and codomain, which preserves and reflects IsIso.
For Z empty the same constructions take place in the zero module category;
for Z = W this is the identity restriction comparison. No affine hypothesis is
used, and no arbitrary coefficient witness is chosen. -/
theorem singleComplexOpenComparison_nested_isIso_iff
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (W Z : X.Opens) (hZW : Z ≤ W) :
    let hW : pullback.snd g' W.ι ≫ (W.ι ≫ f) =
        (pullback.fst g' W.ι ≫ f') ≫ g := by
      rw [← pullback.condition_assoc, Category.assoc, h, ← Category.assoc]
    let φW : (derivedPullback (pullback.snd g' W.ι)).obj
        ((derivedPullback W.ι).obj K) ⟶
        (derivedPullback (pullback.fst g' W.ι)).obj K' :=
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.snd g' W.ι) W.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := W.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' W.ι) g').inv.app K ≫
    (derivedPullback (pullback.fst g' W.ι)).map φ)
    IsIso (singleComplexOpenComparison f f' g g' h K K' φ Z) ↔
      IsIso (singleComplexOpenComparison (W.ι ≫ f) (pullback.fst g' W.ι ≫ f')
        g (pullback.snd g' W.ι) hW ((derivedPullback W.ι).obj K)
        ((derivedPullback (pullback.fst g' W.ι)).obj K') φW (W.ι ⁻¹ᵁ Z)) := by sorry

end AlgebraicGeometry
