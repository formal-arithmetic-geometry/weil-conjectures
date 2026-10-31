/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.ProEtaleScalarBalancingChain
public import WeilConjectures.AlgebraicGeometry.ProEtaleModulePullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtalePullbackStalkCoherence
import all WeilConjectures.SecSmoothPurity.OrdinaryRestrictionPullbackSquare

/-!
# Ordinary coefficient comparisons for nested pro-etale opens

Source: Stacks Project, sites-modules.tex, Tag 03D3,
lemma-adjoint-push-pull-modules; the Locality paragraph of
literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md
(blueprint: lem-sp-proetale-open-coefficient-pullback-composition).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The ordinary constant-ring pullback compositor, directed from successive pullbacks
 to the pullback of the composite. The existing existence theorem determines its
 inverse uniquely: its adjunction conjugate is restriction along the canonical
 fibre-product pasting isomorphism on every section. Thus this extracts the specified
 compositor, with no arbitrary natural-isomorphism choice.

Source: Stacks Project, Tag 03D8, lemma-push-pull-composition-modules, used in the
ordinary refinement of Tag 03D3
(blueprint: lem-sp-proetale-open-coefficient-pullback-composition). -/
def proEtaleOrdinaryConstantPullbackCompositor
    {U V Z : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ Z)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A j₂ ⋙ proEtaleConstantRingPullback A j₁ ≅
      proEtaleConstantRingPullback A (j₁ ≫ j₂) :=
  (proEtaleConstantRingModulePullbackComposition j₁ j₂ A).choose.symm

attribute [local irreducible] proEtaleRingModulePullback

private theorem ordinaryCompositor_eq
    {U V Z : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ Z)
    (A : Type u) [CommRing A] :
    proEtaleOrdinaryConstantPullbackCompositor f g A =
      (StrictTower.moduleGComp (ULift.{u + 1, u} A) f g).symm := by
  apply congrArg Iso.symm
  apply Iso.ext
  apply (conjugateEquiv
    ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
    (proEtaleConstantRingAdjunction A (f ≫ g))).injective
  have hd := (proEtaleConstantRingModulePullbackComposition f g A).choose_spec
  have he : hd.choose = StrictTower.moduleRComp (ULift.{u + 1, u} A) f g := by
    apply (StrictTower.moduleRComp_existsUnique (ULift.{u + 1, u} A) f g).unique
    · exact hd.choose_spec.1
    · exact (StrictTower.moduleRComp_existsUnique
        (ULift.{u + 1, u} A) f g).choose_spec.1
  have hc := congrArg Iso.hom hd.choose_spec.2
  change conjugateEquiv _ _
    (proEtaleConstantRingModulePullbackComposition f g A).choose.hom = _ at hc
  rw [he] at hc
  exact hc.trans
    (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).symm

private theorem beta_identity_inverse
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (Z : Scheme.{u})
    (N : proEtaleRingModules Z (proEtaleConstantRing Z B)) :
    (proEtaleStalkIdentityPullback A Z).inv.app ((scalarMateRestriction φ Z).obj N) ≫
        (scalarBalancingBeta φ (𝟙 Z)).inv.app N =
      (scalarMateRestriction φ Z).map ((proEtaleStalkIdentityPullback B Z).inv.app N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext n
  have hA := (proEtaleStalkIdentityPullback_existsUnique A Z).exists.choose_spec
  have hB := (proEtaleStalkIdentityPullback_existsUnique B Z).exists.choose_spec
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [hA _ W.unop n]
  erw [PresheafOfModules.naturality_apply]
  erw [(proEtaleScalarBalancingChain φ (𝟙 Z)).2.1 N W.unop n]
  exact (hB N W.unop n).symm

/-- The specified ordinary scalar-restriction/pullback comparisons compose for nested
opens, and are the identity for an identity open under the canonical unit comparisons.
Here `scalarBalancingBeta.inv` is precisely the ordinary comparison beta, whose inverse
is descended to the derived comparison b. All equalities are of natural transformations.

Source: Stacks Project, sites-modules.tex, Tag 03D3,
lemma-adjoint-push-pull-modules, and the Locality paragraph of
literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md
(blueprint: lem-sp-proetale-open-coefficient-pullback-composition).

Proof: (1) the chosen ordinary compositor is the inverse of the strict constant-ring
compositor `StrictTower.moduleGComp`: its direct-image conjugate is restriction along the
fibre-product pasting isomorphism, so uniqueness in `moduleRComp_existsUnique`, injectivity
of `conjugateEquiv` and `conjugateEquiv_leftAdjointCompIso_inv` identify the two
(`ordinaryCompositor_eq`). (2) The first equality is then, componentwise in the module N
and after cancelling `moduleGComp_A.hom`, the proved composition calculation
`comparison_comp` of the ordinary restriction/pullback square, since
`scalarBalancingBeta.inv` is by definition the ordinary restriction comparison.
(3) For the identity, the defining section formula of the inverse identity-pullback
(module unit followed by restriction along the fibre-product diagonal), naturality of beta
and the unit-section conjunct of `proEtaleScalarBalancingChain` show that e_A.inv followed by
beta.inv is restriction of scalars of e_B.inv (`beta_identity_inverse`); cancelling e_A.inv
and e_B.inv_hom_id give the second equality. No hypothesis on nonemptiness, nonzero rings
or flatness is used, so the assertions include empty opens, zero rings and nonflat
coefficient maps. -/
theorem proEtaleOpenCoefficientPullbackComposition
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) :
    (∀ {U V Z : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ Z)
        [IsOpenImmersion j₁] [IsOpenImmersion j₂],
      Functor.whiskerLeft (scalarMateRestriction φ Z)
          (proEtaleOrdinaryConstantPullbackCompositor j₁ j₂ A).hom ≫
        (scalarBalancingBeta φ (j₁ ≫ j₂)).inv ≫
        Functor.whiskerRight (proEtaleOrdinaryConstantPullbackCompositor j₁ j₂ B).inv
          (scalarMateRestriction φ U) =
      Functor.whiskerRight (scalarBalancingBeta φ j₂).inv
          (proEtaleConstantRingPullback A j₁) ≫
        Functor.whiskerLeft (proEtaleConstantRingPullback B j₂)
          (scalarBalancingBeta φ j₁).inv) ∧
    (∀ Z : Scheme.{u},
      (scalarBalancingBeta φ (𝟙 Z)).inv ≫
        Functor.whiskerRight (proEtaleStalkIdentityPullback B Z).hom
          (scalarMateRestriction φ Z) =
      Functor.whiskerLeft (scalarMateRestriction φ Z)
        (proEtaleStalkIdentityPullback A Z).hom) := by
  constructor
  · intro U V Z j₁ j₂ _ _
    apply NatTrans.ext
    funext N
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [ordinaryCompositor_eq, ordinaryCompositor_eq]
    apply (cancel_epi ((StrictTower.moduleGComp (ULift.{u + 1, u} A) j₁ j₂).hom.app
      ((scalarMateRestriction φ Z).obj N))).1
    simp only [Iso.symm_hom, Iso.symm_inv, Iso.hom_inv_id_app_assoc]
    have h := comparison_comp φ j₁ j₂ N
    simpa only [scalarBalancingBeta, Iso.symm_inv, asIso_hom,
      ordinaryRestrictionComparison, scalarMateRestriction, ordinaryScalarRestriction,
      ordinaryConstantPullback, StrictTower.modulePullback, StrictTower.constantRingIso,
      proEtaleConstantRingPullback, proEtaleConstantRingComparison, Category.assoc] using h.symm
  · intro Z
    apply NatTrans.ext
    funext N
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply (cancel_epi ((proEtaleStalkIdentityPullback A Z).inv.app
      ((scalarMateRestriction φ Z).obj N))).1
    rw [← Category.assoc, beta_identity_inverse]
    simp only [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (scalarMateRestriction φ Z).map_id _

end AlgebraicGeometry.ProEtale
