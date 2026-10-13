/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps

/-! # Pinned relative Mayer--Vietoris vertex comparisons

Source: Stacks Project, Cohomology, Tags 08HY and 08HZ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Vertex comparisons for the canonical exact-restriction presentation of the
relative Mayer--Vietoris rows. The overlap component satisfies the vertical-pasting
identity. No boundary, distinguishedness, or morphism of triangles is asserted.

Source: Stacks Project, Cohomology, Tags 08BV, 08HZ and 08HY; Derived Categories
of Schemes, Tag 0DJ9, the induction diagram.
(blueprint: lem-pc-relative-mv-pinned-vertex-comparisons).

Proof: For each open W, compare derived exact restriction with derived pullback
using leftAdjointUniq for mvOpenRestrictionAdjunction and relativeMVAdj. Apply
the direct-image functor and compose with relativeMVImageComp W.ι f. Apply Lg*
to obtain the source comparisons. On the inverse-image cover, identify its open
scheme with the chosen pullback using the projection-preserving canonical scheme
isomorphism. Derive this isomorphism and use the same adjunction and composition
comparisons to obtain the target comparisons. At the middle vertices compose the
additive functors' biproduct comparison with biprod.mapIso of the two open
comparisons. The unit identity for leftAdjointUniq proves the two first-arrow
identities. Transpose the restricted counits under these adjunction comparisons;
the counit identity and composition coherence prove the two second-arrow
identities, with subtraction on the V summand. For the overlap expand the
base-change map as the mate of the pulled-back counit. Substitute the composite
adjunction counit formula and cancel both triangle identities. The two pullback
projection composites are equal; transport along this equality and compose the
two pinned pullback comparisons. The remaining map is precisely
relativeMVLocalArrow. This gives the last equality. No compactness,
quasi-coherence, or cover condition is used by these comparisons; empty opens,
zero objects, repeated opens and the zero object map obey the same identities. -/
theorem relativeMV_pinned_vertex_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (U V : X.Opens) :
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
      (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
      (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K 0
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
      ((TopologicalSpace.Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((TopologicalSpace.Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
      (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' 0
    let a := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (e₂ : F.obj T.obj₂ ≅ (a U).left ⊞ (a V).left)
      (e₃ : F.obj T.obj₃ ≅ (a (U ⊓ V)).left)
      (e₂' : G.obj T'.obj₂ ≅ (a U).right ⊞ (a V).right)
      (e₃' : G.obj T'.obj₃ ≅ (a (U ⊓ V)).right),
      F.map T.mor₁ ≫ e₂.hom = relativeMVSourceFirst f g U V K ∧
      F.map T.mor₂ ≫ e₃.hom = e₂.hom ≫ relativeMVSourceSecond f g U V K ∧
      G.map T'.mor₁ ≫ e₂'.hom = relativeMVTargetFirst g' f' U V K' ∧
      G.map T'.mor₂ ≫ e₃'.hom = e₂'.hom ≫ relativeMVTargetSecond g' f' U V K' ∧
      mvBaseChangeOpenMap f f' g g' hpull.w K K' φ (U ⊓ V) ≫ e₃'.hom =
        e₃.hom ≫ (a (U ⊓ V)).hom := by sorry

end AlgebraicGeometry
