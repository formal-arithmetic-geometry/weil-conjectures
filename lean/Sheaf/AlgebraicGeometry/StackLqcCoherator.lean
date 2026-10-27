/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.AlgebraicGeometry.StackSmallEtaleRestriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # The quasi-coherator on locally quasi-coherent stack modules

Source: Stacks Project, stacks-cohomology.tex, Tag 0778 (lemma-adjoint),
section-locally-quasi-coherent and definition-flat-base-change
(blueprint: lem-sfb-stack-lqc-coherator).

Small étale restrictions are constructed from the slice equivalence of a fibred
category in groupoids. Their rings are the existing structure sheaf evaluated on the
chosen lifts, hence canonically the regular-function rings, with the same ULift as
on the total site. Local quasi-coherence uses the equivalent small-étale local-presentation
criterion of the cited source. No equality between site universes is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- Naturality of pullback on regular functions in the lifted tests.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: lem-sfb-stack-lqc-coherator).
Proof: apply the regular-function presheaf to moduliEtaleLiftArrow_naturality,
reverse composition on taking opposites, and use its functor composition law. -/
theorem moduliEtaleRingMap_naturality {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x)
    {V W : ((moduliSchemeForget F).obj x).Etaleᵒᵖ} (f : V ⟶ W) :
    (moduliEtaleModuleRings F hF x).obj.map f ≫
        (moduliModuleRings F hF).obj.map (moduliEtaleLiftArrow F hF a W.unop).op =
      (moduliModuleRings F hF).obj.map (moduliEtaleLiftArrow F hF a V.unop).op ≫
        (moduliEtaleModuleRings F hF y).obj.map
          (((moduliSchemeForget F).map a).Etale.op.map f) := by
  sorry

/-- Pullback of regular functions along the actual restriction arrows.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: lem-sfb-stack-lqc-coherator). -/
noncomputable def moduliEtaleRingMap {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x) :
    moduliEtaleModuleRings F hF x ⟶
      (((moduliSchemeForget F).map a).Etale.sheafPushforwardContinuous _ _ _).obj
        (moduliEtaleModuleRings F hF y) :=
  ⟨{ app V := (moduliModuleRings F hF).obj.map (moduliEtaleLiftArrow F hF a V.unop).op
     naturality {_V _W} f := moduliEtaleRingMap_naturality F hF a f }⟩

/-- The restriction map H_x to u_* H_y, with its original section maps.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: lem-sfb-stack-lqc-coherator). -/
noncomputable def moduliEtaleRestrictionMap {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x)
    (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF)) :
    (moduliEtaleRestriction F hF x).obj H ⟶
      (SheafOfModules.pushforward (moduliEtaleRingMap F hF a)).obj
        ((moduliEtaleRestriction F hF y).obj H) :=
  letI := moduliEtaleLift_isContinuous F hF x
  letI := moduliEtaleLift_isContinuous F hF y
  letI := Functor.isContinuous_comp ((moduliSchemeForget F).map a).Etale
    (moduliEtaleLift F hF y) ((moduliSchemeForget F).obj x).smallEtaleTopology
    ((moduliSchemeForget F).obj y).smallEtaleTopology (moduliFppfTopology F)
  (SheafOfModules.pushforwardNatTrans
    (F := ((moduliSchemeForget F).map a).Etale ⋙ moduliEtaleLift F hF y)
    (G := moduliEtaleLift F hF x)
    (J := ((moduliSchemeForget F).obj x).smallEtaleTopology)
    (K := moduliFppfTopology F) (𝟙 (moduliEtaleModuleRings F hF x))
    (moduliEtaleLiftTransformation F hF a)).app H

/-- Sheafification on every small étale slice in the common ambient universe.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: lem-sfb-stack-lqc-coherator).
Proof: the slice has objects and arrows in the ambient universe. Two plus
constructions for additive presheaves therefore exist in that same universe
and give the sheafification adjunction. -/
@[instance] theorem moduliEtaleSliceHasWeakSheafify
    (T : Scheme.{u}) (V : T.Etale) [UnivLE.{u + 1, t}] :
    HasWeakSheafify (T.smallEtaleTopology.over V) AddCommGrpCat.{t} := by
  sorry

/-- Sheafification inverts exactly locally bijective maps on these étale slices.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: lem-sfb-stack-lqc-coherator).
Proof: the plus-construction unit is locally bijective. A locally bijective map
becomes an isomorphism by locally lifting sections and gluing using local
injectivity. Conversely local representatives and the locally bijective units
show that an isomorphism after sheafification was locally bijective. -/
@[instance] theorem moduliEtaleSliceWEqualsLocallyBijective
    (T : Scheme.{u}) (V : T.Etale) [UnivLE.{u + 1, t}] :
    (T.smallEtaleTopology.over V).WEqualsLocallyBijective
      AddCommGrpCat.{t} := by
  sorry

/-- Locally bijective additive maps are the sheafification equivalences on the
small étale site itself, in every sufficiently large coefficient universe.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: lem-sfb-stack-lqc-coherator).
Proof: the same two-plus construction as on slices has locally bijective unit;
local lifting and local equality characterize its inverted maps. -/
@[instance] theorem moduliEtaleWEqualsLocallyBijective
    (T : Scheme.{u}) [UnivLE.{u + 1, t}] :
    T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{t} := by
  sorry

/-- The scheme-test ringed-site pushforward admits tensor pullback as left adjoint.
This is a proof of existence of a universal construction, not a selected module or map.
Source: Stacks, stacks-cohomology, definition-flat-base-change; Modules on Sites,
tensor pullback (blueprint: lem-sfb-stack-lqc-coherator).
Proof: first construct the left adjoint on free module presheaves, sending the
free presheaf on an étale test to the free presheaf on its base change. Extend
along the free presentation of each module presheaf using coproducts and
cokernels. Compose with additive module sheafification. The continuous
pushforward preserves sheaves, so the two Hom adjunctions restrict to sheaves.
The ambient universe contains both étale sites, hence all these colimits exist. -/
@[instance] theorem moduliEtalePushforward_isRightAdjoint {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x) :
    (SheafOfModules.pushforward.{max (u + 1) v w}
      (moduliEtaleRingMap F hF a)).IsRightAdjoint := by
  sorry

/-- The canonical tensor comparison c_a is the adjoint of restriction. Mathlib's
pullback is inverse image followed by extension of scalars and sheafification.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: lem-sfb-stack-lqc-coherator). -/
noncomputable def moduliEtaleTensorComparison {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    {y x : F.obj} (a : y ⟶ x)
    (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF)) :
    (SheafOfModules.pullback (moduliEtaleRingMap F hF a)).obj
        ((moduliEtaleRestriction F hF x).obj H) ⟶
      (moduliEtaleRestriction F hF y).obj H :=
  ((SheafOfModules.pullbackPushforwardAdjunction (moduliEtaleRingMap F hF a)).homEquiv
    _ _).symm (moduliEtaleRestrictionMap F hF a H)

/-- Local quasi-coherence means quasi-coherence of every small étale restriction.
Equivalently, each is the associated étale sheaf of a quasi-coherent Zariski module,
with sections Γ(V,v^*M), as in the source's section-locally-quasi-coherent.
Source: Stacks, stacks-cohomology, section-locally-quasi-coherent
(blueprint: lem-sfb-stack-lqc-coherator). -/
def IsLocallyQuasicoherentModuliModule {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF)) : Prop :=
  ∀ x : F.obj, ((moduliEtaleRestriction F hF x).obj H).IsQuasicoherent

/-- Flat compatibility requires invertibility of the canonical comparison for every
arrow over a flat scheme map; it imposes no compatibility for nonflat arrows.
Source: Stacks, stacks-cohomology, definition-flat-base-change
(blueprint: lem-sfb-stack-lqc-coherator). -/
def IsFlatCompatibleModuliModule {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F)
    (H : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF)) : Prop :=
  ∀ {y x : F.obj} (a : y ⟶ x), Flat ((moduliSchemeForget F).map a) →
    IsIso (moduliEtaleTensorComparison F hF a H)

/-- The object predicate defining the full category L_Z of the node.
Source: Stacks, stacks-cohomology, Tag 0778
(blueprint: lem-sfb-stack-lqc-coherator). -/
def locallyQuasicoherentFlatCompatible {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsFibredInGroupoids F) :
    ObjectProperty (ringedSiteModules.{max (u + 1) v w} (moduliModuleRings F hF)) :=
  fun H ↦ IsLocallyQuasicoherentModuliModule F hF H ∧ IsFlatCompatibleModuliModule F hF H

/-- Quasi-coherent modules embed in L_Z, and this inclusion has the quasi-coherator
as right adjoint. The Hom bijection is composition with its natural module counit;
the unit is invertible, giving Q j isomorphic to the identity. There are no
quasi-compactness, quasi-separatedness, finiteness or Noetherian assumptions.
Source: Stacks, stacks-cohomology, Tag 0778 (lemma-adjoint)
(blueprint: lem-sfb-stack-lqc-coherator).

Proof:
1. The scheme-test restriction criterion
   (lem-sfb-stack-quasi-coherent-scheme-restriction) makes every quasi-coherent
   module locally quasi-coherent, with invertible comparisons for all arrows.
2. Choose a smooth surjective scheme atlas U to F. The chartwise calculus
   (lem-sfb-stack-chartwise-smooth-etale-calculus) makes it flat and locally
   finitely presented. The presentation theorem
   (lem-sfb-fppf-groupoid-stack-presentations) and module descent
   (lem-sfb-space-groupoid-module-descent) give an equivalence E from QCoh(F)
   to the quasi-coherent modules on its algebraic-space relation R, with inverse D.
3. Restrict H to U and define its descent map by c_s^{-1} b c_t. The small-étale
   comparison calculus (lem-sfb-stack-small-etale-comparison-calculus) makes both
   comparisons invertible. On triple overlaps their product is
   c_1^{-1} b_12 c_2 c_2^{-1} b_23 c_3 = c_1^{-1} b_13 c_3. The identity relation
   gives the unit condition. Naturality makes this construction a functor B.
4. Set Q = D B. Descent identifies Hom(G,QH) with Hom(EG,BH). The theorem on maps
   from quasi-coherent modules (lem-sfb-groupoid-maps-from-quasicoherent) identifies
   the latter with Hom(jG,H): cancelling the invertible comparisons makes its image
   equation precisely the groupoid-equivariance equation. Both identifications commute
   with precomposition and postcomposition, giving the adjunction.
5. Its counit q_H is the image of the identity of QH; naturality gives the displayed
   formula for every a. Fullness of j lifts q_{jG} to r:QjG to G. The triangle identity
   and faithfulness give r eta_G = 1; injectivity of the Hom bijection gives
   eta_G r = 1. Thus the unit is an isomorphism. None of these steps imposes any
   finiteness property on F. -/
theorem exists_moduliLqcCoherator {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F) :
    ∃ h : SheafOfModules.isQuasicoherent (moduliModuleRings F hF.1.1) ≤
        locallyQuasicoherentFlatCompatible F hF.1.1,
      ∃ Q : (locallyQuasicoherentFlatCompatible F hF.1.1).FullSubcategory ⥤
          (SheafOfModules.isQuasicoherent (moduliModuleRings F hF.1.1)).FullSubcategory,
        ∃ adj : ObjectProperty.ιOfLE h ⊣ Q,
          (∀ (G : (SheafOfModules.isQuasicoherent
                (moduliModuleRings F hF.1.1)).FullSubcategory)
              (H : (locallyQuasicoherentFlatCompatible F hF.1.1).FullSubcategory)
              (a : G ⟶ Q.obj H),
            (adj.homEquiv G H).symm a =
              (ObjectProperty.ιOfLE h).map a ≫ adj.counit.app H) ∧
          IsIso adj.unit := by
  sorry

end CategoryTheory
