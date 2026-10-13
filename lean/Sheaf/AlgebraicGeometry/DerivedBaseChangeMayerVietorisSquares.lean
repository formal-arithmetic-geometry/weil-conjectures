/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps


/-! # Unit and restriction squares for relative Mayer--Vietoris base change

Source: Stacks Project, Tags 08BV, 08HY and 0DJ9
(blueprint: lem-pc-rf-mv-base-change-first-two-squares).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

/-- The unit and difference-of-restrictions squares commute for the canonical
open adjunctions and the constructed pullback/restriction comparisons. No
boundary or triangle morphism is asserted.
Source: Stacks Project, Tags 08HY and 0DJ9, induction step, using Tag 0D5S
(blueprint: lem-pc-rf-mv-base-change-first-two-squares).
Proof:
1. Use the derived adjunctions and composition comparisons occurring literally
   in schemeDerivedBaseChangeMap. For each open W, the isomorphism
   mvPullbackOpenRestrictionIso is the path through pullback of the two open
   immersions, with their pullback/restriction adjoint comparisons at the ends.
   The unit and counit equations of these comparisons are proved as
   mvOpenPullbackIso_unit and mvOpenPullbackIso_counit. Thus transposing the
   pasted open map gives restriction of the transpose of ψ; no bare existence
   isomorphism is substituted in this calculation.
2. Insert the adjunction unit on W on either side of that identity. The triangle
   identities cancel its counit and naturality moves ψ through the remaining
   unit. This proves F.map(unit_W) followed by the W component equals the
   whole-space component followed by G.map(unit_W'). Prove it for U and V,
   then assemble the two equalities using biproduct inclusion/projection laws.
3. For W contained in U, expand schemeDerivedOpenDirectImageRestriction as
   the mate of the restricted U counit. Apply the counit equation in step 1.
   The two paths of pullback comparisons agree by the associativity law in
   exists_derivedPullbackComposition; exact nested restriction has the same
   underived composition. Naturality of the counit then gives the restriction
   square, including its fixed canonical overlap identification. Apply this
   separately to U intersect V contained in U and in V. Functor additivity
   turns their pair of equalities into the difference square displayed here.
4. The equations are natural in both objects and ψ since every step uses
   natural transformations, their mates, and their composition laws. Affine
   permanence supplies qcqs hypotheses if the calculation is made using
   K-flat and K-injective representatives. No boundedness or flatness is used. -/
theorem derivedBaseChange_mayerVietoris_firstTwoSquares
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
:
    ∀ (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X'),
      schemeDerivedQCohProperty X K → schemeDerivedQCohProperty X' K' →
      ∀ ψ : (derivedPullback g').obj K ⟶ K',
    let adjU := mvOpenRestrictionAdjunction X U
    let adjV := mvOpenRestrictionAdjunction X V
    let adjUV := mvOpenRestrictionAdjunction X (U ⊓ V)
    let adjU' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)
    let adjV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V)
    let adjUV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let a₀ := schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫ G.map ψ
    let a₂ := mvBaseChangeMiddle f f' g g' hsq.w K K' ψ U V
    let a₃ := mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V)
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K 0
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' 0
    F.map T.mor₁ ≫ a₂ = a₀ ≫ G.map T'.mor₁ ∧
    F.map T.mor₂ ≫ a₃ = a₂ ≫ G.map T'.mor₂ := by sorry

end AlgebraicGeometry
