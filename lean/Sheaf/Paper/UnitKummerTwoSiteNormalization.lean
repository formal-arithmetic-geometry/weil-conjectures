/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
public import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import all Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero

/-! # Unit Kummer classes on the two small sites

Source: Stacks Project, etale-cohomology.tex, Tag 03PL, lemma-kummer-sequence;
proetale.tex, Tags 099W and 0GLZ; blueprint frame-independence, Unit multiples
(blueprint: lem-pur-unit-kummer-two-site-normalization).

All coefficient maps insert one in the actual balanced tensor. Scalar-forgetting
maps are adjunction mates, retaining the units of the published inverse images.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.proofsInPublic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UnitKummer
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Abelian.Ext.homEquiv

attribute [local irreducible] comparisonUpperStar Abelian.Ext.comp Abelian.Ext.mk₀
  Abelian.Ext.mapExactFunctor

/-- Underlying abelian pro-etale sheaf. Source: Stacks Tags 03CY and 03EK
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
abbrev forgetPro (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The etale root-tensor line, using the existing scalar extension.
Source: Stacks Tag 03EK (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
def etaleLine (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.RawModuleScalarComparison.forget A X).obj (finiteEtaleTateLine X m A hA)

/-- The pro-etale root-tensor line, using the existing scalar extension.
Source: Stacks Tag 03EK (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
def proLine (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (forgetPro A X).obj (finiteRootProTensor A m hm hA X)

section ScalarInsertion

attribute [local semireducible] finiteRootProModule finiteRootProTensor
  finiteRootProGenerator

set_option backward.isDefEq.respectTransparency.types false

/-- The scalar-extension unit is the unique abelian sheaf morphism sending every
local root to its tensor with one. Source: Stacks Tags 03EK and 03EL
(blueprint: lem-pur-unit-kummer-two-site-normalization).
Proof: on the published root module compose the scalar-extension adjunction unit
with the sheafification unit and forget scalars. Its section formula is exactly
finiteRootProGenerator at one. This defines an abelian sheaf morphism since both
units are natural and additive. Equality of the displayed section maps proves
uniqueness by extensionality of natural transformations. -/
theorem proInsertion_existsUnique (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) :
    ∃! f : proEtaleRootsOfUnitySheaf X m ⟶ proLine A m hm hA X,
      ∀ (W : X.ProEtᵒᵖ) (z : (proEtaleRootsOfUnitySheaf X m).obj.obj W),
        f.hom.app W z = finiteRootProGenerator A m hm hA X W 1 z := by
  let g : (finiteRootProModule X m hm).obj ⟶
      (finiteRootProTensor A m hm hA X).obj ⋙
        ModuleCat.restrictScalars (finiteEtaleTwistScalar m A hA) :=
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar m A hA)).whiskerRight X.ProEtᵒᵖ).homEquiv _ _)
        (toSheafify (ProEt.topology X) _)
  let f : proEtaleRootsOfUnitySheaf X m ⟶ proLine A m hm hA X :=
    ⟨{ app := fun W ↦ AddCommGrpCat.ofHom (g.app W).hom.toAddMonoidHom
       naturality := by
         intro U V k
         ext z
         exact ConcreteCategory.congr_hom (g.naturality k) z }⟩
  have hf (W : X.ProEtᵒᵖ) (z : (proEtaleRootsOfUnitySheaf X m).obj.obj W) :
      f.hom.app W z = finiteRootProGenerator A m hm hA X W 1 z := by
    rfl
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  ext W z
  exact (hf' W z).trans (hf W z).symm

end ScalarInsertion

/-- The uniquely specified scalar-extension unit z to z tensor one.
Source: Stacks Tags 03EK and 03EL
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def proInsertion (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) :
    proEtaleRootsOfUnitySheaf X m ⟶ proLine A m hm hA X :=
  (proInsertion_existsUnique A m hm hA X).exists.choose

/-- The coefficient comparison in modules, chosen from its published normalized
specification. Its values on all local tensor generators determine it uniquely.
Source: Stacks Tag 0GLZ (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def tensorComparison (A : Type (u + 1)) [CommRing A] [Finite A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj (finiteEtaleTateLine X m A hA) ≅
      finiteRootProTensor A m hm hA X :=
  (finiteRootSiteComparison A).choose m hm hA X hX

/-- The normalized geometric pullback of the pro-etale tensor, determined by its
adjunct on pure tensors. Source: Stacks Tag 03EL
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def tensorPullback (A : Type (u + 1)) [CommRing A] [Finite A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (v : Y ⟶ X) :
    (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).obj
      (finiteRootProTensor A m hm hA X) ⟶ finiteRootProTensor A m hm hA Y :=
  (finiteRootSiteComparison A).choose_spec.choose m hm hA v

/-- The unit-compatible scalar-forgetting comparison for the site comparison,
constructed by transposing the underlying module unit.
Source: Stacks Tag 00YV (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def comparisonForget (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} X).obj
        ((Etale.RawModuleScalarComparison.forget A X).obj M) ⟶
      (forgetPro A X).obj ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M) :=
  ((comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv _ _).symm
    ((Etale.RawModuleScalarComparison.forget A X).map
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M))

/-- The specified coefficient comparison as an abelian sheaf morphism.
Source: Stacks Tags 00YV and 0GLZ
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def comparison (A : Type (u + 1)) [CommRing A] [Finite A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} X).obj (etaleLine A m hA X) ⟶
      proLine A m hm hA X :=
  comparisonForget A X (finiteEtaleTateLine X m A hA) ≫
    (forgetPro A X).map (tensorComparison A m hm hA X hX).hom

/-- The underlying normalized etale coefficient pullback.
Source: Stacks Tag 03EL (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def etalePullback (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) {X Y : Scheme.{u}} (v : Y ⟶ X)
    (hX : IsUnit (m : Γ(X, ⊤))) (hY : IsUnit (m : Γ(Y, ⊤))) :
    (Etale.upperStar AddCommGrpCat.{u + 1} v).obj (etaleLine A m hA X) ⟶
      etaleLine A m hA Y :=
  (Etale.RawModuleScalarComparison.pullbackIso A v).inv.app
      (finiteEtaleTateLine X m A hA) ≫
    (Etale.RawModuleScalarComparison.forget A Y).map
      ((finiteEtaleTwistPullbackData A m hm hA).c v hX hY 1).hom

/-- Underlying pro-etale pullback, obtained by transposing the underlying module
adjunct. Source: Stacks Tags 00YV and 03EL
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def proPullback (A : Type (u + 1)) [CommRing A] [Finite A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X Y : Scheme.{u}} (v : Y ⟶ X) :
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).obj (proLine A m hm hA X) ⟶
      proLine A m hm hA Y :=
  ((proEtaleSheafAdjunction v AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    ((forgetPro A X).map
      ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _
        (tensorPullback A m hm hA v)))

/-- Canonical pro-etale cohomology pullback, before identifying coefficients.
Source: Stacks Tag 08J6 (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def proCohomologyPullback {X Y : Scheme.{u}} (v : Y ⟶ X)
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H F q →+ Sheaf.H
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} v).obj F) q :=
  Sheaf.H.mapFunctor (ProEtale.upperStar AddCommGrpCat.{u + 1} v)
    ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} v).symm.app
      (AddCommGrpCat.of (ULift ℤ))) F q

/-- The etale class H¹(z to z tensor one) delta(u).
Source: Stacks Tag 03PL (blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def etaleClass (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H (etaleLine A m hA X) 1 :=
  Etale.relativeKummerClass A m hA X hX u

/-- The pro-etale class H¹(phi_pro c_X) comp(delta(u)), extending coefficients
only after the ordinary Kummer boundary. Source: Stacks Tags 03PL and 099W
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def proClass (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤)))
    (u : Γ(X, ⊤)ˣ) : Sheaf.H (proLine A m hm hA X) 1 :=
  Sheaf.H.map
    ((ProEtale.cartierRootsIso X m hm hX).hom ≫ proInsertion A m hm hA X) 1
    (comparisonCohomologyMap X (X.rootsOfUnitySheaf m) 1
      (X.kummerδ₀ m hX (Additive.ofMul u)))

/-- The coefficient comparison on degree-one abelian cohomology.
Source: Stacks Tags 099W and 0GLZ
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def compareClass (A : Type (u + 1)) [CommRing A] [Finite A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) :
    Sheaf.H (etaleLine A m hA X) 1 →+ Sheaf.H (proLine A m hm hA X) 1 :=
  (Sheaf.H.map (comparison A m hm hA X hX) 1).comp
    (comparisonCohomologyMap X (etaleLine A m hA X) 1)

/-- The integer generator of the underlying constant module sheaf on the pro-etale
site, obtained from the etale generator and the two canonical comparison units.
Source: Stacks Tags 00YV and 03CY
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def frameIntegralGenerator (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (forgetPro P.Coefficient X).obj (P.constant X) :=
  (comparisonConstantSheafIso X).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} X).map (P.integerToConstant X) ≫
    comparisonForget P.Coefficient X (P.constantEtale X)

/-- Realize the published module Ext class as underlying abelian cohomology.
The integer generator is fixed above; scalar forgetting is its explicit left adjoint
in the coinduction adjunction, so is exact. Source: Stacks Tags 03CY and 099W
(blueprint: lem-pur-unit-kummer-two-site-normalization). -/
@[irreducible] def frameAbelianClass (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H ((forgetPro P.Coefficient X).obj (P.frameTwist X 1)) 1 :=
  letI : (forgetPro P.Coefficient X).IsLeftAdjoint :=
    (Sheaf.forget₂CoinduceAdj (ProEt.topology X) P.Coefficient).isLeftAdjoint
  (forgetPro P.Coefficient X).mapExtComp (frameIntegralGenerator P X)
    (P.frameTwist X 1) 1 (P.frameKummer X a u)


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The degree-one unit Kummer normalization on both small sites.
Source: Stacks Tag 03PL; proetale.tex Tags 099W and 0GLZ; blueprint
frame-independence, Unit multiples and Elementary shears
(blueprint: lem-pur-unit-kummer-two-site-normalization).

Proof:
1. The ordinary Kummer boundary is an additive homomorphism, by the universal
   right-derived delta-functor. Cohomology, coefficient insertion and the canonical
   etale-to-pro-etale comparison are homomorphisms. This proves both additive laws.
2. Pullback of units respects powers and restricts to the normalized root map.
   These maps give a morphism of ordinary Kummer sequences. The pullback long
   exact ladder and naturality of the universal delta-functor identify its boundary
   square; degree-zero pullback is actual pullback of units.
3. The coefficient square commutes on each local root: both sides give its
   pullback tensored with one. Naturality of cohomology pullback gives etale
   naturality. No tensor of the whole Kummer sequence is used.
4. The same-root comparison and balanced-tensor comparison take z tensor a to
   the same z tensor a. Their coefficient square therefore commutes. Coefficient
   naturality of canonical cohomology pullback gives the class comparison.
5. Compare the two composite site pullbacks through their common base-change
   functor and the unit-compatible composition isomorphisms. The two coefficient
   maps agree on the unit images of local tensors, hence on their sheafification.
   Composition and coefficient naturality of site cohomology pullback give the
   geometric comparison square, then pro-etale naturality and its coefficient square.
6. Specialization to ell^n and the projection-induced purity presentation is the
   second theorem below. This uses the same root map and scalar insertion at every
   level and imposes no flatness, Cartier, or ramification-divisibility condition. -/
theorem normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) :
    (∀ (X : Scheme.{u}) (W : X.ProEtᵒᵖ)
      (z : (proEtaleRootsOfUnitySheaf X m).obj.obj W),
      (proInsertion A m hm hA X).hom.app W z = finiteRootProGenerator A m hm hA X W 1 z) ∧
    (∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))),
      IsIso (comparison A m hm hA X hX)) ∧
    (∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (u w : Γ(X, ⊤)ˣ),
      etaleClass A m hA X hX (u * w) =
        etaleClass A m hA X hX u + etaleClass A m hA X hX w) ∧
    (∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (u w : Γ(X, ⊤)ˣ),
      proClass A m hm hA X hX (u * w) =
        proClass A m hm hA X hX u + proClass A m hm hA X hX w) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
      (hY : IsUnit (m : Γ(Y, ⊤))),
      IsIso (etalePullback A m hm hA v hX hY) ∧ IsIso (proPullback A m hm hA v)) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 X.gmSheaf)) ≫
          upperStarGmSheafToGmSheaf v =
        ((finiteEtaleTwistPullbackData A m hm hA).r v hX).hom ≫
          kernel.ι (m • 𝟙 Y.gmSheaf) ∧
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (m • 𝟙 X.gmSheaf) ≫
          upperStarGmSheafToGmSheaf v =
        upperStarGmSheafToGmSheaf v ≫ (m • 𝟙 Y.gmSheaf)) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
      (hY : IsUnit (m : Γ(Y, ⊤))) (u : Γ(X, ⊤)ˣ),
      Sheaf.H.map ((finiteEtaleTwistPullbackData A m hm hA).r v hX).hom 1
          (Etale.cohomologyMap v (X.rootsOfUnitySheaf m) 1
            (X.kummerδ₀ m hX (Additive.ofMul u))) =
        Y.kummerδ₀ m hY
          (Additive.ofMul (Units.map v.appTop.hom.toMonoidHom u))) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
      (hY : IsUnit (m : Γ(Y, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map
          (Etale.ordinaryFiniteRootMap A m hA X) ≫ etalePullback A m hm hA v hX hY =
        ((finiteEtaleTwistPullbackData A m hm hA).r v hX).hom ≫
          Etale.ordinaryFiniteRootMap A m hA Y) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X),
      (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
          (proInsertion A m hm hA X) ≫ proPullback A m hm hA v =
        proEtaleRootsOfUnityInverseImageMap v m ≫ proInsertion A m hm hA Y) ∧
    (∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))),
      (comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          (Etale.ordinaryFiniteRootMap A m hA X) ≫ comparison A m hm hA X hX =
        (ProEtale.cartierRootsIso X m hm hX).hom ≫ proInsertion A m hm hA X) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
      (hY : IsUnit (m : Γ(Y, ⊤))) (u : Γ(X, ⊤)ˣ),
      Sheaf.H.map (etalePullback A m hm hA v hX hY) 1
          (Etale.cohomologyMap v (etaleLine A m hA X) 1 (etaleClass A m hA X hX u)) =
        etaleClass A m hA Y hY (Units.map v.appTop.hom.toMonoidHom u)) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
      (hY : IsUnit (m : Γ(Y, ⊤))) (u : Γ(X, ⊤)ˣ),
      Sheaf.H.map (proPullback A m hm hA v) 1
          (proCohomologyPullback v (proLine A m hm hA X) 1 (proClass A m hm hA X hX u)) =
        proClass A m hm hA Y hY (Units.map v.appTop.hom.toMonoidHom u)) ∧
    (∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (u : Γ(X, ⊤)ˣ),
      compareClass A m hm hA X hX (etaleClass A m hA X hX u) =
        proClass A m hm hA X hX u) ∧
    (∀ {X Y : Scheme.{u}} (v : Y ⟶ X) (hX : IsUnit (m : Γ(X, ⊤)))
      (hY : IsUnit (m : Γ(Y, ⊤))) (x : Sheaf.H (etaleLine A m hA X) 1),
      Sheaf.H.map (proPullback A m hm hA v) 1
          (proCohomologyPullback v (proLine A m hm hA X) 1
            (compareClass A m hm hA X hX x)) =
        compareClass A m hm hA Y hY
          (Sheaf.H.map (etalePullback A m hm hA v hX hY) 1
            (Etale.cohomologyMap v (etaleLine A m hA X) 1 x))) := by
  sorry

/-- At every finite purity level the projection-induced root-tensor identification
sends the concrete published frame Kummer class to precisely the pro-etale unit class.
Source: blueprint def-pur-frame-class, concrete Kummer paragraph; Stacks Tag 03PL
(blueprint: lem-pur-unit-kummer-two-site-normalization).

Proof (Step 6 of the node): take m = ell^n. The projection from Z_ell(1) modulo m
identifies A(1) with mu_m tensor A by the defining tensor formula. The identical-root
adjunct rho is the same-root c_X. The definition of frameKummerEtale is exactly the
scalar insertion applied to delta, through the bijective module-to-abelian comparison.
Exact comparison inverse image and its unit-compatible scalar-forgetting mate give
frameAbelianClass. Applying the underlying tensorComparison is therefore precisely
H¹(phi_pro c_X) comp(delta). This includes every n >= 1, without e dividing n. -/
theorem frame_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ) :
    Sheaf.H.map ((forgetPro P.Coefficient X).map
      (tensorComparison P.Coefficient P.diagonalExponent
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
        P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit a)).hom) 1
      (frameAbelianClass P X a u) =
    proClass P.Coefficient P.diagonalExponent
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
      P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit a) u := by
  sorry

end AlgebraicGeometry.Scheme.UnitKummer
