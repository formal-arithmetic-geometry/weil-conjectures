/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.Paper.LocalizeRingedSiteMorphism
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.SixFunctors.GeometricInverseImageConstantModule

/-!
# Pullback of locally constant finite module sheaves

Source: Stacks Project, sites-modules.tex, Tag 093R, lemma-pullback-locally-constant,
specialized to the small pro-etale topoi
(blueprint: lem-exc-proetale-pullback-locally-constant).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback preserves the given finite constant module models on the base-changed cover.
The arrows to `ProEt.mk (𝟙 V)` are unique, hence are precisely the structure maps of the
base-changed objects. The conclusion retains the same modules `M i`, not just their sizes.
Source: Stacks Project, Tag 093R, lemma-pullback-locally-constant
(blueprint: lem-exc-proetale-pullback-locally-constant).

Proof:
1. The base-change functor preserves finite limits and coverings. By
   lem-weil-pbc-left-exact-site-inverse-image-tensor it induces a geometric morphism.
   By prop-weil-pbc-proetale-constant-ring-map its canonical coefficient map is an
   isomorphism preserving constant scalars. Thus the tensor module pullback is the
   fixed-ring module inverse image of lem-pe-constant-left-module-inverse-image.
   By lem-sfb-geometric-inverse-image-constant-module it takes a constant module
   sheaf to the constant sheaf with the very same module.
2. The objects W_i = u_f(U_i) form a cover, by base-change preservation of covers.
   Apply lem-weil-pbc-localize-ringed-site-morphism at U_i: restriction of the tensor
   pullback to W_i is the localized tensor pullback of the restriction to U_i.
   Its ring map is the restricted coefficient isomorphism. Apply this localized
   pullback to the given trivialization, then the constant-module comparison of
   step 1 on the localized sites. This gives the displayed isomorphism with M_i.
   Every M_i is still finite, and these isomorphisms witness local constancy.
   Empty covering members require no choice of a point: their sheaves are zero.
   Empty schemes and empty covering families are included throughout. -/
theorem proEtaleConstantModulePullback_locallyConstant
    {V X : Scheme.{u}} (f : V ⟶ X) (A : Type u) [CommRing A] [Finite A]
    (F : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X A)))
    (I : Type (u + 1)) (U : I → X.ProEt)
    (a : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
    (hcover : Presieve.ofArrows U a ∈ (ProEt.precoverage X).coverings _)
    (M : I → ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (hfinite : ∀ i : I, Finite (M i))
    (htrivial : ∀ i : I,
      Nonempty (F.over (U i) ≅ proEtaleConstantModuleSheafOver X A (U i) (M i))) :
    ∃ b : ∀ i : I, (proEtaleBaseChange f).obj (U i) ⟶ ProEt.mk (𝟙 V),
      Presieve.ofArrows (fun i : I ↦ (proEtaleBaseChange f).obj (U i)) b ∈
          (ProEt.precoverage V).coverings _ ∧
        (∀ i : I, Nonempty
          ((proEtaleConstantModulePullback f A F).over ((proEtaleBaseChange f).obj (U i)) ≅
            proEtaleConstantModuleSheafOver V A ((proEtaleBaseChange f).obj (U i)) (M i))) ∧
        IsLocallyConstantProEtaleModuleSheaf V A (proEtaleConstantModulePullback f A F) := by
  sorry

end AlgebraicGeometry.Scheme
