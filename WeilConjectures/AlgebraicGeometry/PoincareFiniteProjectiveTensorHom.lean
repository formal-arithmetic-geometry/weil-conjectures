/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PoincareDualityConventions
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocallyProjective
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided


/-!
# Finite projective tensor--Hom over pulled-back condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
lem-pod-finite-projective-tensor-hom.md and its proof; Stacks Project, Tag 08JJ
(blueprint: lem-pod-finite-projective-tensor-hom).

The dual and bidual are ordinary internal module Homs. The derived comparison is
constructed by applying the canonical derived-to-ordinary tensor comparison to
ordinary evaluation in degree zero, and then transposing under tensor--Hom.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The finite coefficient ring of the fixed setting, with its discrete topology,
as a condensed ring. Source: def-pod-conventions and condensed coefficients
(blueprint: lem-pod-finite-projective-tensor-hom). -/
def poincareFiniteCondensedRing (S : PoincareDualityConventions.{u}) :
    Profinite.CondensedRing.{u} := by
  letI : TopologicalSpace S.coefficientRing := ⊥
  letI : DiscreteTopology S.coefficientRing := ⟨rfl⟩
  exact Mon.mk (Profinite.continuousCoefficientRingObj S.coefficientRing)

/-- Exactly the four coefficient choices of the fixed setting, allowing isomorphic
presentations of condensed rings. A finite intermediate field in the standard closure
presents the fixed extension precisely when it is isomorphic over Q_l to that extension.
The algebraic-closure coefficient is the native finite-subextension-valued condensed ring.
Source: def-pod-conventions, the coefficient-family paragraph
(blueprint: lem-pod-finite-projective-tensor-hom). -/
def PoincareCondensedCoefficientChoice (S : PoincareDualityConventions.{u})
    (Λ : Profinite.CondensedRing.{u}) : Prop :=
  Nonempty (Λ ≅ poincareFiniteCondensedRing S) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField S.coefficients.l,
      Nonempty (S.extension.val ≃ₐ[Padic S.coefficients.l] E) ∧
        (Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj S.coefficients.l E)) ∨
          Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)))) ∨
    Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj S.coefficients.l))

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u})

/-- Ordinary sheaf dual in the internal-module presentation of module sheaves.
This is the same sheaf of local linear maps as the recorded SheafOfModules.homObj.
Source: def-pur-sheaf-hom, and Stacks 08JJ
(blueprint: lem-pod-finite-projective-tensor-hom). -/
abbrev poincareOrdinaryDual (P : supportModules Λ.X X) : supportModules Λ.X X :=
  (ihom P).obj (𝟙_ (supportModules Λ.X X))

/-- The canonical tensor comparison on two degree-zero module sheaves.
Source: the K-flat relative tensor of sk-def-sfb-derived-tensor-hom; Stacks 08JJ
(blueprint: lem-pod-finite-projective-tensor-hom).
The comparison is the lax tensor map of localization followed by the tensor/single
isomorphism. It exists without a flatness assumption on either module. -/
def poincareSingleTensorComparison (P Q : supportModules Λ.X X) :
    (DerivedCategory.singleFunctor _ 0).obj P ⊗
      (DerivedCategory.singleFunctor _ 0).obj Q ⟶
        (DerivedCategory.singleFunctor _ 0).obj (P ⊗ Q) :=
  (((DerivedCategory.singleFunctorIsoCompQ _ 0).app P).hom ⊗ₘ
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app Q).hom) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor _ 0).obj P)
      ((CochainComplex.singleFunctor _ 0).obj Q) ≫
    DerivedCategory.Q.map
      (((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor (supportModules Λ.X X)) Q).app
          ((CochainComplex.singleFunctor _ 0).obj P) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight Q) (.up ℤ) 0).app P).hom) ≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (P ⊗ Q)).inv

/-- Ordinary evaluation induces the derived evaluation P[0] tensor dual(P)[0] to the unit.
Source: tensor--Hom adjunction, Stacks 08JJ
(blueprint: lem-pod-finite-projective-tensor-hom). -/
def poincareDerivedEvaluation (P : supportModules Λ.X X) :
    (DerivedCategory.singleFunctor _ 0).obj P ⊗
      (DerivedCategory.singleFunctor _ 0).obj (poincareOrdinaryDual Λ X P) ⟶
        𝟙_ (DerivedCategory (supportModules Λ.X X)) :=
  poincareSingleTensorComparison Λ X P (poincareOrdinaryDual Λ X P) ≫
    (DerivedCategory.singleFunctor _ 0).map ((ihom.ev P).app (𝟙_ _)) ≫
    (DerivedCategory.singleFunctorObjUnitIso (supportModules Λ.X X)).hom

/-- The canonical map from the ordinary dual tensor N to derived internal Hom(P,N).
It is the adjoint transpose of evaluation tensored with N, so no unrelated choice of
an isomorphism enters the statement. Source: the displayed arrow of the current blueprint
(blueprint: lem-pod-finite-projective-tensor-hom). -/
def poincareFiniteProjectiveTensorHomMap (P : supportModules Λ.X X)
    (N : DerivedCategory (supportModules Λ.X X)) :
    ((derivedTensor Λ.X X).obj
      ((DerivedCategory.singleFunctor _ 0).obj (poincareOrdinaryDual Λ X P))).obj N ⟶
    ((derivedHom Λ.X X).obj (op ((DerivedCategory.singleFunctor _ 0).obj P))).obj N :=
  curry ((α_ ((DerivedCategory.singleFunctor _ 0).obj P)
      ((DerivedCategory.singleFunctor _ 0).obj (poincareOrdinaryDual Λ X P)) N).inv ≫
    poincareDerivedEvaluation Λ X P ▷ N ≫ (λ_ N).hom)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite projective tensor--Hom and ordinary biduality for all four condensed
coefficient choices of the Poincare setting, with naturality in both variables.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
lem-pod-finite-projective-tensor-hom.md; Stacks Project, Tag 08JJ
(blueprint: lem-pod-finite-projective-tensor-hom).

Proof: (1) Restriction to slices is exact and commutes with ordinary Hom, tensor,
K-flat tensor models and derived Hom. It preserves the canonical evaluation comparison.
Cohomology sheaves detect isomorphisms locally, by sheaf separatedness.
(2) For R^r the inverse sends h to the finite sum of e_j^* tensor h(e_j).
Ordinary bidual evaluation is the identity in double-dual coordinates. Both formulas
commute with restriction and all maps in both variables, including r=0.
(3) On each splitting slice choose i:P -> F and p:F -> P with p i=1. If
A(E)=dual(E) tensor B and H(E)=Hom(E,B), the inverse is A(i)c_F^{-1}H(p).
The inverse bidual map is p delta_F^{-1}D^2(i). The two inverse equations reduce
to p i=1. Local inverses glue since they invert the same canonical arrow.
(4) Tensor by P or its dual is locally a retract of a finite power functor, hence
is exact and preserves acyclic complexes. Their degree-zero complexes are K-flat,
and ordinary Hom(P,-), identified with dual(P) tensor -, is exact.
(5) Choose a flat-term K-flat model M of N and a K-injective resolution M -> I.
Termwise evaluation identifies dual(P) tensor M with Hom(P,M); exactness makes
Hom(P,M) -> Hom(P,I) a quasi-isomorphism. Uncurrying gives precisely evaluation,
with no degree-zero sign. The derived comparison defined above is therefore invertible.
The coordinate naturality identities descend through localization and give the last
two conjuncts. Ordinary biduality was already obtained in (3). -/
theorem poincareFiniteProjectiveTensorHom (S : PoincareDualityConventions.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ : PoincareCondensedCoefficientChoice S Λ) :
    (∀ (P : supportModules Λ.X S.X), IsFiniteLocallyProjective Λ.X S.X P →
      ∀ N : ConstantModelConstructibleFiniteTor Λ.X S.X,
        IsIso (poincareFiniteProjectiveTensorHomMap Λ S.X P N.obj)) ∧
    (∀ (P : supportModules Λ.X S.X), IsFiniteLocallyProjective Λ.X S.X P →
      IsIso (toIhomIhomUnit P)) ∧
    (∀ (P P' : supportModules Λ.X S.X), IsFiniteLocallyProjective Λ.X S.X P →
      IsFiniteLocallyProjective Λ.X S.X P' → ∀ (f : P ⟶ P')
      (N : ConstantModelConstructibleFiniteTor Λ.X S.X),
        (DerivedCategory.singleFunctor _ 0).map ((pre f).app (𝟙_ _)) ▷ N.obj ≫
            poincareFiniteProjectiveTensorHomMap Λ S.X P N.obj =
          poincareFiniteProjectiveTensorHomMap Λ S.X P' N.obj ≫
            (pre ((DerivedCategory.singleFunctor _ 0).map f)).app N.obj) ∧
    (∀ (P : supportModules Λ.X S.X), IsFiniteLocallyProjective Λ.X S.X P →
      ∀ (N N' : ConstantModelConstructibleFiniteTor Λ.X S.X) (g : N ⟶ N'),
        (DerivedCategory.singleFunctor _ 0).obj (poincareOrdinaryDual Λ S.X P) ◁ g.hom ≫
            poincareFiniteProjectiveTensorHomMap Λ S.X P N'.obj =
          poincareFiniteProjectiveTensorHomMap Λ S.X P N.obj ≫
            (ihom ((DerivedCategory.singleFunctor _ 0).obj P)).map g.hom) := by
  sorry

end WeilConjectures
