/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Natural local-ring presentation of an affine module model

Source: Stacks Project, Tags 01BH, 01HV (7), and 008B.
(blueprint: new-e3-affine-model-stalk-presentation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TensorProduct
namespace AlgebraicGeometry

/-- An affine model presents the original module stalk over its own local ring.
Source: Stacks Project, Tag 01BH, Lemma 17.10.5 (3), and Tag 01HV (7).
(blueprint: new-e3-affine-model-stalk-presentation)

Proof: Put q = isoSpec(x) and p = q.asIdeal. Restriction along the open immersion
U -> Y identifies F_x with (F|U)_x. Take the stalk of the supplied model
isomorphism and then use restriction along isoSpec to identify this with the
stalk of tilde M at q. These identifications are compatible with the stalk-ring
maps: represent both a ring element and a module element by germs on a common
neighborhood, and use the restriction scalar action and germ_smul. The germ
A -> S identifies S with A localized at A minus p. The map tilde.toStalk M q
is a module localization at the same multiplicative set. Transport this map
through the above stalk identifications. Its localization universal property,
and IsLocalizedModule.isBaseChange, give an S-linear equivalence S tensor_A M
-> F_x sending s tensor m to s times the transported germ of m. This specifies
the equivalence uniquely. For a compatible pair c,d, the given square identifies
their maps on germs of elements m. The stalk maps are S-linear, and pure tensors
generate S tensor_A M, so the two composites agree on every tensor. This proves
naturality. No global quasi-coherence of F is used: only its restriction is modeled
by tilde M. The zero module is covered by the same localization universal property;
an empty affine open has no point x satisfying hx. -/
theorem exists_affine_model_stalk_presentation
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1) :
    let A := (Γ(Y, U.1) : Type u)
    let S := (Y.presheaf.stalk x : Type u)
    letI : Algebra A S := (Y.presheaf.germ U.1 x hx).hom.toAlgebra
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ δ : ∀ (F : Y.Modules) (M : ModuleCat.{u} A),
      ((Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M) →
        (S ⊗[A] M) ≃ₗ[S] F.presheaf.stalk x,
      ∀ (F G : Y.Modules) (M N : ModuleCat.{u} A) (c : F ⟶ G) (d : M ⟶ N)
        (eF : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj M)
        (eG : (Scheme.Modules.restrictFunctor U.1.ι).obj G ≅ T.obj N),
        (Scheme.Modules.restrictFunctor U.1.ι).map c ≫ eG.hom = eF.hom ≫ T.map d →
        ∀ t, c.stalkLinearMap x (δ F M eF t) =
          δ G N eG (d.hom.baseChange S t) := by sorry

end AlgebraicGeometry
