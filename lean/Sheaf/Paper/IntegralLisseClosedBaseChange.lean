/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.CategoryTheory.AdjunctionSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Sheaf.RingTheory.ProEtale.HenselianClosedLift
import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import Sheaf.AlgebraicGeometry.IntegralAlgebraDirectedColimitFinite
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import Sheaf.RingTheory.IndfiniteContractibleBaseWStrict
import Sheaf.RingTheory.HenselianWStrictLocalInvariance
import Sheaf.Topology.ContinuousMapCondensedRing
import Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Integral direct image and closed base change for lisse continuous coefficients

Source: blueprint main-20261015, direct-image proof paragraph (3), agent-formulated
integral closed-base-change input; Stacks 0EYP is only the discrete-etale analogue.
(blueprint: lem-sfb-integral-lisse-closed-base-change).

All derived categories are ordinary and unbounded. The pullback is exact and is applied
termwise; its adjunction is transported from the recorded total derived adjunction.
Coefficient compatibility uses restriction comparisons in their canonical direction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralLisseClosedBaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing exact module pullback on the ordinary derived category.
Source: sk-def-sfb-module-derived-pushpull, exact pullback identification
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- The recorded K-injective derived adjunction, with exact pullback as its left adjoint.
Source: sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def adj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull Λ f ⊣ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)

/-- The canonical composition constraint of exact module pullback.
Source: sk-def-sfb-module-derived-pushpull, composition identifications
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull Λ (f ≫ g) ≅ pull Λ g ⋙ pull Λ f :=
  Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The square comparison uses the actual composition identifications and commutativity.
Source: the adjunct formula in the node statement
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def square {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) :
    pull Λ s ⋙ pull Λ qZ ≅ pull Λ q ⋙ pull Λ h :=
  (pullComp Λ qZ s).symm ≪≫
    eqToIso (congrArg (fun f : T ⟶ U ↦ pull Λ f) w.w.symm) ≪≫ pullComp Λ h q

/-- The canonical exchange: the adjunct of the square comparison followed by h* counit.
No geometric property and no exactness of direct image is used in its construction.
Source: the displayed adjunct formula in the node statement
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def exchange {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) :
    CondensedRing.moduleObjectDerivedPushforward Λ q ⋙ pull Λ s ⟶
      pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ qZ :=
  Adjunction.squareExchange (adj Λ q) (adj Λ qZ) (pull Λ s) (pull Λ h) (square Λ w)

/-- Naturality in a module morphism, including the degree-zero embedding.
Source: the module-map naturality clause of the node
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def ModuleNaturality {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) : Prop :=
  ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsLisseCoefficientModule Λ M → IsLisseCoefficientModule Λ N → ∀ f : M ⟶ N,
      (pull Λ s).map ((CondensedRing.moduleObjectDerivedPushforward Λ q).map
          ((DerivedCategory.singleFunctor _ 0).map f)) ≫
        (exchange Λ w).app ((DerivedCategory.singleFunctor _ 0).obj N) =
      (exchange Λ w).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ qZ).map
          ((pull Λ h).map ((DerivedCategory.singleFunctor _ 0).map f))

/-- A cartesian cube gives the base-change naturality square, with all four canonical
comparison arrows retained. Taking the base arrow to be an isomorphism includes
isomorphisms of cartesian squares. Taking it to be U[Q] → U keeps whole profinite families.
Source: the square, pro-etale and profinite naturality clauses of the node
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def CubeNaturality {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsLisseCoefficientModule Λ M →
    ∀ (X' U' T' Z' : Scheme.{u}) (q' : X' ⟶ U') (s' : Z' ⟶ U')
      (h' : T' ⟶ X') (qZ' : T' ⟶ Z')
      (a : X' ⟶ X) (v : U' ⟶ U) (t : T' ⟶ T) (b : Z' ⟶ Z),
      WeaklyEtale v → ∀ (w' : IsPullback h' qZ' q' s')
      (wq : IsPullback a q' q v) (ws : IsPullback b s' s v)
      (wh : IsPullback t h' h a) (wz : IsPullback t qZ' qZ b),
      (pull Λ b).map ((exchange Λ w).app ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
          (exchange Λ wz.toCommSq).app
            ((pull Λ h).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
          (CondensedRing.moduleObjectDerivedPushforward Λ qZ').map
            ((square Λ wh.toCommSq).inv.app ((DerivedCategory.singleFunctor _ 0).obj M)) =
        (square Λ ws.toCommSq).inv.app
            ((CondensedRing.moduleObjectDerivedPushforward Λ q).obj
              ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
          (pull Λ s').map
            ((exchange Λ wq.toCommSq).app ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
          (exchange Λ w'.toCommSq).app
            ((pull Λ a).obj ((DerivedCategory.singleFunctor _ 0).obj M))

/-- All geometric assertions for one of the two allowed continuous coefficient rings.
Source: the displayed isomorphism and naturality clauses of the node
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def GeometricAssertions {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : IsPullback h qZ q s) : Prop :=
  (∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsLisseCoefficientModule Λ M →
      IsIso ((exchange Λ w.toCommSq).app ((DerivedCategory.singleFunctor _ 0).obj M))) ∧
    ModuleNaturality Λ w.toCommSq ∧ CubeNaturality Λ w.toCommSq

section Coefficients

variable {Λ}
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

/-- Exact restriction of scalars on the ordinary unbounded derived category.
Source: the scalar-restriction clause of the node
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def restrict (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (Mod.comap (coefficientMap c X)).mapDerivedCategory

/-- The canonical exact pullback/restriction comparison; no flatness is assumed.
Source: the coefficient identifications in the node's scalar clause
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def restrictPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull Λ' f ⋙ restrict c X ≅ restrict c Y ⋙ pull Λ f :=
  CondensedRing.derivedComapUpperStarIso c f

/-- The canonical right-derived coefficient comparison in its natural direction.
It is the mate of inverse pullback/restriction comparison, with no invertibility claim.
Source: the coefficient-map clause of the node's closed-test model
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def restrictPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward Λ' f ⋙ restrict c Y ⟶
      restrict c X ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  Adjunction.squareExchange (adj Λ' f) (adj Λ f)
    (restrict c Y) (restrict c X) (restrictPull c f).symm

/-- The actual x ↦ 1 ⊗ x map, embedded in degree zero and restricted to the source ring.
The last isomorphism only identifies restriction of a single complex with the single
complex of its restriction. No derived scalar extension is substituted for ordinary tensor.
Source: the last clause of the node
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def scalarUnit (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction (coefficientMap c X)).unit.app M) ≫
    ((Mod.comap (coefficientMap c X)).mapDerivedCategorySingleFunctor 0).inv.app
      ((Mod.extendScalars (coefficientMap c X)).obj M)

/-- The restriction comparison intertwines the two actual exchange arrows.
The equation is meaningful without any scalar/direct-image isomorphism.
Source: the scalar compatibility clause and the node proof, step 7
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def RestrictionExchange {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))) : Prop :=
  (restrictPull c s).inv.app ((CondensedRing.moduleObjectDerivedPushforward Λ' q).obj N) ≫
      (restrict c Z).map ((exchange Λ' w).app N) ≫
      (restrictPush c qZ).app ((pull Λ' h).obj N) =
    (pull Λ s).map ((restrictPush c q).app N) ≫
      (exchange Λ w).app ((restrict c X).obj N) ≫
      (CondensedRing.moduleObjectDerivedPushforward Λ qZ).map
        ((restrictPull c h).inv.app N)

/-- The exchange square for the actual coefficient unit, together with restriction exchange
on its ordinary tensor target. This records compatibility after restriction using canonical
comparison arrows; none of these right-derived comparisons is assumed invertible.
Source: the scalar compatibility clause and the node proof, step 7
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def ScalarAssertions {X U T Z : Scheme.{u}} {q : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {qZ : T ⟶ Z} (w : CommSq h qZ q s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsLisseCoefficientModule Λ M →
      RestrictionExchange c w
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (coefficientMap c X)).obj M)) ∧
      (pull Λ s).map
          ((CondensedRing.moduleObjectDerivedPushforward Λ q).map (scalarUnit c X M)) ≫
        (exchange Λ w).app
          ((restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj
            ((Mod.extendScalars (coefficientMap c X)).obj M))) =
        (exchange Λ w).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          (CondensedRing.moduleObjectDerivedPushforward Λ qZ).map
            ((pull Λ h).map (scalarUnit c X M))

end Coefficients

/-- The actual continuous coefficient inclusion induced by E → Ω, with every continuous
function retained. This is the dependency's postcomposition map, in the common universe.
Source: def-sfb-continuous-map-condensed-ring-map, postcomposition formula
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
def coefficientInclusion (E Ω : Type u) [NormedField E] [NormedField Ω]
    [NormedAlgebra E Ω] :
    Profinite.continuousCoefficientRingObj E ⟶ Profinite.continuousCoefficientRingObj Ω :=
  Profinite.continuousMapRingObjMapOfUniverse.{u, u} (algebraMap E Ω) (continuous_algebraMap E Ω)

/-- The coefficient inclusion respects the canonical sectionwise ring structures.
Source: def-sfb-continuous-map-condensed-ring-map, ring-object clause
(blueprint: lem-sfb-integral-lisse-closed-base-change). -/
instance coefficientInclusion_isMonHom (E Ω : Type u) [NormedField E] [NormedField Ω]
    [NormedAlgebra E Ω] : IsMonHom (coefficientInclusion E Ω) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
      (algebraMap E Ω) (continuous_algebraMap E Ω))

/-- Closed base change for integral direct images of finite-rank lisse modules over the
all-continuous E and Ω coefficients, with the specified mate and all naturalities.
Source: blueprint main-20261015, direct-image proof paragraph (3), agent-formulated
integral input (Stacks 0EYP is only the discrete-etale analogue)
(blueprint: lem-sfb-integral-lisse-closed-base-change).

Proof: (1) Cover the affine ind-etale basis of Z by w-contractible affine tests V.
The closed lifted-site functor gives W over U with W ×_U Z = V and a henselian
coordinate pair (C,IC). Henselian lisse rigidity makes W w-contractible.
(2) Write D = B tensor_A C for X ×_U W. Integrality is preserved by base change;
integral extension of a henselian pair makes (D,ID) henselian.
(3) On affine W, the integral-algebra approximation lemma gives a nonempty directed
system of finite, finitely presented C-algebras D_i with colimit D. Evaluation on W
preserves that colimit. The ind-finite contractible-base lemma makes D w-strictly local.
(4) Henselian invariance makes D/ID w-strictly local, and the actual component map
Spec(D/ID) → Spec D is a homeomorphism on pi_0. Pulling back a finite-free
trivialization makes the restricted supplied module lisse.
(5) The w-strict lisse component-cohomology lemma makes the actual restriction on
RΓ invertible, for every condensed coefficient ring, including incomplete Ω.
(6) The closed-test derived-exchange model identifies this restriction with RΓ(V,beta)
for the specified adjunction mate. Exact evaluation on these contractible tests and
conservativity of the ind-etale basis kill the cone's cohomology, so beta is invertible
in the ordinary unbounded derived category.
(7) Naturality of this identified arrow gives module, square and pro-etale naturality.
Apply it to entire objects U[Q] to retain arbitrary profinite families. For scalar
compatibility apply the coefficient-map clause of the closed-test model to the actual
map x ↦ 1 tensor x. Restriction comparisons have their canonical directions and are
not required to be invertible. No exactness of arbitrary integral direct image or
scalar-extension/direct-image isomorphism enters the statement. -/
theorem integral_lisse_closed_base_change
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E Ω : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [NormedField Ω] [NormedAlgebra E Ω]
    [IsAlgClosure E Ω]
    {X U T Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [T.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsAffine X] [IsAffine U]
    (q : X ⟶ U) [q.IsOver (Spec (.of k))] [IsIntegralHom q]
    (s : Z ⟶ U) [s.IsOver (Spec (.of k))] [IsClosedImmersion s]
    (h : T ⟶ X) [h.IsOver (Spec (.of k))]
    (qZ : T ⟶ Z) [qZ.IsOver (Spec (.of k))] (w : IsPullback h qZ q s) :
    GeometricAssertions (Profinite.continuousCoefficientRingObj E) w ∧
      GeometricAssertions (Profinite.continuousCoefficientRingObj Ω) w ∧
      ScalarAssertions (coefficientInclusion E Ω) w.toCommSq := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralLisseClosedBaseChange
