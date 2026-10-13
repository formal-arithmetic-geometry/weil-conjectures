/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseModels
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition

/-! # Composition of the canonical termwise single map

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-single-map-composition)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The pinned single pullback map, retaining the tensor-pulled module as its target.
This is a real composite of the derived counit and canonical single comparisons.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-picard-termwise-single-map-composition) -/
def picardTermwiseSingleMap {W T : Scheme.{v}} (t : T ⟶ W) (M : W.Modules) :
    (derivedPullback t).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
          ((Modules.tensorPullback t).obj M)) :=
  Modules.canonicalSinglePullbackMap t M ≫
    (DerivedCategory.singleFunctor _ 0).map
      (((Classical.choose (Modules.exists_tensorPullbackAdjunction t)).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction t)).inv.app M)

/-- The canonical maps on arbitrary singles satisfy the composition counit equation.
No flatness, invertibility, or choice of a comparison family is asserted here.
Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-single-map-composition)

Proof: First take t' = i ≫ t and ht = rfl. Write S for the complex single,
q for the homotopy quotient, ε_b for the pinned homotopy counit, and
r_b(N) : T_b(S(N)) → S(T_b(N)) for singleMapHomologicalComplex.hom.
Expanding canonicalSinglePullbackMap and using functoriality cancels the
single images of leftAdjointUniq.hom and .inv. Thus the constructed map is
ε_b(q(S(N))) followed by Qh(q(r_b(N))).

Let δ : T_i T_t → T_(i≫t) be the tensor composition mate occurring in the
definition of the pinned derived composition. The defining leftDerivedLift
factorization, evaluated at q(S(M)), says
c.hom ; ε_(i≫t) = Li*(ε_t) ; ε_i(T_t(q(S(M)))) ; Qh(δ).
The inverse of δ is tensorPullbackCompositionIso(i,t,i≫t,rfl): both are the
mates of inverse pushforward composition maps under the same adjunctions.
The single-complex identity is
δ(S(M)) ; r_(i≫t)(M) ; S(δ(M).inv) ; r_i(T_t(M)).inv = T_i(r_t(M)).
Check it in degree zero using the single degree-zero identifications; in every
other degree the single is zero, so the components agree. The mate inverse
identity cancels δ(M) there. Mapping this equation by q and Qh, and substituting
it in the factorization, leaves Li*(ε_t) ; ε_i ; Qh(T_i(r_t)).
Naturality of ε_i for q(r_t) rewrites this as
Li*(ε_t ; Qh(q(r_t))) ; ε_i(q(S(T_t(M)))).

Expand picardTermwiseCounit at S(T_t(M)). The mapHomotopyCategoryFactors
components are identities. Naturality of quotientCompQhIso for r_i.inv
converts the final Qh-coordinate expression to the required complex-coordinate
expression. Its components at singles are identities, so no additional source
or target factors remain. Finally eliminate ht by equality induction to reduce
arbitrary t' to i ≫ t; proof irrelevance identifies the equality transports.
No comparison ε is inverted. In particular zero modules, empty schemes and
identity morphisms obey the same equations without any flatness hypothesis. -/
theorem picardTermwiseSingleMap_composition
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') (M : W.Modules) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    let u := (CochainComplex.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
        ((Modules.tensorPullbackCompositionIso i t t' ht).app M) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)).symm
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≫
        picardTermwiseSingleMap t' M ≫ DerivedCategory.Q.map u.hom =
      (derivedPullback i).map (picardTermwiseSingleMap t M) ≫
        (picardTermwiseCounit i).app ((CochainComplex.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
            ((Modules.tensorPullback t).obj M)) := by sorry

end
end AlgebraicGeometry.Scheme
