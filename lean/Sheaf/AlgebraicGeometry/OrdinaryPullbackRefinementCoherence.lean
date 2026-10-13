/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Ordinary pullback coherence for a refined three-step path
Source: Stacks Project, Tags 0095 and 0096. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Ordinary pullbacks of two refined three-step paths agree.
Source: Stacks Project, Tags 0095 and 0096; ordinary-pullback portion of step 2
of lem-pc-open-cover-tensor-comparison-coherence.
(blueprint: lem-pc-ordinary-pullback-refinement-coherence).
Proof: Expand rhoK and rhoL. Apply pseudofunctor_associativity to reassociate each
three-step path to the pullback of its composite. Naturality of pullbackComp moves
the first comparison through pullback z. The equations Hz, Hd identify the composite
path z then pK then sK with pL then sL; H0 identifies the path z then rK with rL.
The equations HK and HL identify each of these total paths followed by f with the
path through h. Congruence is eqToIso, so its composites depend only on the endpoint
equality, by proof irrelevance. Thus both expanded composites are the same canonical
comparison between the pullbacks of the same scheme map. Cancel inverse composition
comparisons, restore the associators, and evaluate at M. This argument uses no open
cover condition, tensor pullback or adjunction, and applies to empty schemes, zero
modules and identity refinements. -/
theorem ordinary_pullback_refinement_coherence
    {X A B C K L W : Scheme.{u}}
    (f : A ⟶ X) (sK : B ⟶ A) (sL : C ⟶ A)
    (pK : K ⟶ B) (pL : L ⟶ C) (rK : K ⟶ W) (rL : L ⟶ W) (h : W ⟶ X)
    (d : C ⟶ B) (z : L ⟶ K)
    (Hd : d ≫ sK = sL) (Hz : z ≫ pK = pL ≫ d) (H0 : z ≫ rK = rL)
    (HK : (pK ≫ sK) ≫ f = rK ≫ h) (HL : (pL ≫ sL) ≫ f = rL ≫ h)
    (M : X.Modules) :
    let S := pullback f
    let QK := pullback sK
    let QL := pullback sL
    let PK := pullback pK
    let PL := pullback pL
    let RK := pullback rK
    let RL := pullback rL
    let D := pullback d
    let Zf := pullback z
    let rhoK0 : pullback h ⋙ RK ≅ (S ⋙ QK) ⋙ PK :=
      pullbackComp rK h ≪≫ (pullbackCongr HK).symm ≪≫
      (pullbackComp (pK ≫ sK) f).symm ≪≫
      Functor.isoWhiskerLeft S (pullbackComp pK sK).symm ≪≫
      (Functor.associator S QK PK).symm
    let rhoL0 : pullback h ⋙ RL ≅ (S ⋙ QL) ⋙ PL :=
      pullbackComp rL h ≪≫ (pullbackCongr HL).symm ≪≫
      (pullbackComp (pL ≫ sL) f).symm ≪≫
      Functor.isoWhiskerLeft S (pullbackComp pL sL).symm ≪≫
      (Functor.associator S QL PL).symm
    let gamma0 : S ⋙ QL ≅ (S ⋙ QK) ⋙ D := Functor.isoWhiskerLeft S
      ((pullbackCongr Hd).symm ≪≫ (pullbackComp d sK).symm) ≪≫
      (Functor.associator S QK D).symm
    let beta0 : RK ⋙ Zf ≅ RL := pullbackComp z rK ≪≫ pullbackCongr H0
    let delta0 : PK ⋙ Zf ≅ D ⋙ PL :=
      pullbackComp z pK ≪≫ pullbackCongr Hz ≪≫ (pullbackComp pL d).symm
    ∀ (rhoK : pullback h ⋙ RK ≅ (S ⋙ QK) ⋙ PK) (_ : rhoK = rhoK0)
      (rhoL : pullback h ⋙ RL ≅ (S ⋙ QL) ⋙ PL) (_ : rhoL = rhoL0)
      (gamma : S ⋙ QL ≅ (S ⋙ QK) ⋙ D) (_ : gamma = gamma0)
      (beta : RK ⋙ Zf ≅ RL) (_ : beta = beta0)
      (delta : PK ⋙ Zf ≅ D ⋙ PL) (_ : delta = delta0),
    Zf.map (rhoK.hom.app M) ≫ delta.hom.app ((S ⋙ QK).obj M) ≫
      PL.map (gamma.inv.app M) = beta.hom.app ((pullback h).obj M) ≫
        rhoL.hom.app M := by sorry

end AlgebraicGeometry.Scheme.Modules
