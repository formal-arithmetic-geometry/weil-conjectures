/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections


import Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective
import Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction

/-! # Natural section comparisons under successive base change

Source: Stacks Project, Tags 0B91 and 08HY.
(blueprint: lem-sc-picard-direct-image-section-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The additive section comparison for a direct image is natural for arbitrary successive
base changes. This is the cohomological part of the argument; it asserts no property
of the image of a scheme morphism and uses no residue point or open neighbourhood.
Source: Stacks Project, Tags 0B91, 08HY and 0D5S.
(blueprint: lem-sc-picard-direct-image-section-naturality)

Proof: Set p = pr_W and M = pr_X^*L. Flatness of f and invertibility of L imply
that M is finitely presented and flat over W, and these properties persist after
base change. Tag 0B91 makes the canonical map Lt^*Rp_*(M[0]) to the derived direct
image of M_T[0] invertible for every t. The cartesian comparison identifies M_T
with pr_X^*L by the tensor-pullback composition isomorphism. Pullback of O_W[0]
is O_T[0], since the tensor unit is flat. Derived adjunction and full faithfulness
of the degree-zero single functor now identify test morphisms with morphisms
O_{X_T} to L_T. Evaluation on 1 over the top open is the additive equivalence to
global sections. Let q_t be the composite of these additive equivalences, using
the canonical base-change maps throughout.

For i followed by t, the two given projection equations identify j with the
cartesian comparison by the fibre-product universal property. Tensor composition
along j and pr_X gives the displayed, fixed coefficient isomorphism. Naturality of the
derived adjunction unit and counit
identifies pullback of a test morphism with pullback of its transpose. The
canonical degree-zero mate square identifies this with the ordinary tensor
adjunction unit. Associativity of the canonical derived composition comparisons
shows that the pulled-back test morphism is exactly the conjugation defining
picardDerivedModelRestriction. Evaluate the resulting equality of module
morphisms at 1 on the top open. The pushforward unit has values on j inverse top;
compose its presheaf restriction to top and the inverse composition comparison to obtain the
formula. This proof uses no nonempty scheme or fibre assumption: on empty schemes
the same maps are equivalences of zero section groups. -/
theorem picard_direct_image_section_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∃ q : ∀ {T : Scheme.{v}} (t : T ⟶ W),
        picardDerivedModelSections E t ≃+
          Γ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L, ⊤),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            (c.app L).inv.app ⊤
              (((Modules.tensorPullback j).obj
                ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).presheaf.map
                  (homOfLE j.preimage_top.ge).op
                    (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                      ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).val.app
                        (Opposite.op ⊤) (q t ξ))) =
              q t' (picardDerivedModelRestriction E i t t' h ξ) := by
  classical
  refine ⟨fun t ↦ AddEquiv.ofBijective (picardDirectImageSectionMap f L W k t)
    (picardDirectImageSectionMap_bijective f L W k t), ?_⟩
  intro T T' i t t' h j hj₁ hj₂
  exact picardDirectImageSectionMap_restriction f L W k i t t' h j hj₁ hj₂

end AlgebraicGeometry.Scheme
