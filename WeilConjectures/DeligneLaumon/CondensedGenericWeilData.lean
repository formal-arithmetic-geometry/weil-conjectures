/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.RepresentationTheory.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibreFunctoriality
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Generic fibres of condensed lisse Weil modules

Source: latest blueprint, rem-dl-a1-conventions, irreducible-lisse and geometric-constancy
paragraphs; Deligne, Weil II (1.1.10)--(1.1.12).
(blueprint: lem-dl-a1-condensed-weil-generic-representation).

All categories below use actual condensed modules. Component and profinite group coordinates
are supplied as conclusions, so geometric connectedness is never an additional assumption.

## Main definitions

* `Lisse`: actual lisse condensed Weil modules.
* `Group` and `Geometry`: the Weil group and its canonical open geometric subgroup.
* `Representations`: representations with continuous finite-field geometric restriction.
* `fibre` and `returnMap`: actual point sections and their Frobenius return operators.
* `Assertions`: the normalized exact tensor equivalence and subobject correspondence.

## Main statements

* `generic_fibre_equivalence`: existence of the specified generic-fibre equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

/-- The lisse full subcategory of the recorded category of actual Weil modules.
Source: rem-dl-a1-conventions, lisse Weil sheaf paragraph
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev Lisse (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X) :=
  ObjectProperty.FullSubcategory
    (fun M : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj ell) g ↦
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier)

/-- Forget only the Weil structure and the lisse proof.
Source: the underlying module in rem-dl-a1-conventions
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev forget (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (g : X ≅ X) :=
  ObjectProperty.ι
    (fun M : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj ell) g ↦
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier) ⋙
    Endofunctor.IsoAlgebra.forget (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) g.hom)

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (U₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [ConnectedSpace U₀.left]

/-- Projection from the actual geometric base change.
Source: def-weil-finite-field-fiber
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev projection : (D.geometricFiber U₀).left ⟶ U₀.left :=
  pullback.fst U₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
  (G : ProfiniteGrp.{u})
  [∀ Q, MulAction G ((FiniteEtale.fiber (t ≫ projection D U₀)).obj Q)]
  [PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber (t ≫ projection D U₀)) G]

/-- The constant-cover fibre product with the integer powers of geometric Frobenius.
The same existing group construction is used without assuming its degree map is onto.
The product with discrete integers gives its usual Weil topology.
Source: Weil II (1.1.10); def-wf-fundamental-representation, constant covers
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev Group :=
  (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).weilGroup
    (FiniteEtale.geometricFrobenius U₀.hom (t ≫ projection D U₀))

/-- The original, unrescaled integer degree.
Source: Weil II (1.1.10)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev degree : Group D U₀ t G →* Multiplicative ℤ :=
  (FiniteEtale.constantCoverAction U₀.hom (t ≫ projection D U₀) G).weilGroupDeg
    (FiniteEtale.geometricFrobenius U₀.hom (t ≫ projection D U₀))

/-- Coordinates on the component containing the specified geometric generic point.
The group inclusion is pinned on all finite arithmetic covers, and identifies precisely
its open geometric subgroup. All these are output data, not input hypotheses.
Source: rem-dl-a1-conventions and Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
structure Geometry where
  component : RealCondensedFibre.Context.{u}
  inclusion : component.X ⟶ (D.geometricFiber U₀).left
  openImmersion : IsOpenImmersion inclusion
  image : Set.range inclusion = connectedComponent (t (IsLocalRing.closedPoint Ω))
  point : Spec (.of Ω) ⟶ component.X
  point_eq : point ≫ inclusion = t
  P : ProfiniteGrp.{u}
  [action : ∀ Q, MulAction P ((FiniteEtale.fiber point).obj Q)]
  [fundamental : PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber point) P]
  geometric : P →* Group D U₀ t G
  geometric_degree : ∀ a : P, degree D U₀ t G (geometric a) = 1
  geometric_arithmetic : ∀ a : P,
    PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D U₀)) G
        (geometric a).val.1 =
      (eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc point inclusion (projection D U₀)).symm.trans
          (congrArg (fun z ↦ z ≫ projection D U₀) point_eq)))).symm ≪≫
        FiniteEtale.pullbackPathIso (inclusion ≫ projection D U₀)
          (PreGaloisCategory.toAut (FiniteEtale.fiber point) P a) ≪≫
        eqToIso (congrArg FiniteEtale.fiber
          ((Category.assoc point inclusion (projection D U₀)).symm.trans
            (congrArg (fun z ↦ z ≫ projection D U₀) point_eq)))
  injective : Function.Injective geometric
  geometric_image : geometric.range = (degree D U₀ t G).ker
  topology : Topology.IsOpenEmbedding geometric

attribute [instance] Geometry.action Geometry.fundamental

variable (ell : ℕ) [Fact ell.Prime]

/-- Exactly the finite-dimensional representations with continuous finite-field geometric
restriction. In particular this imposes no lattice condition on any nonzero-degree element.
Source: def-pod-l-adic-representations (3), and rem-dl-a1-conventions
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev Representations (A : Geometry D U₀ t G) :=
  ObjectProperty.FullSubcategory (fun V :
      Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G) ↦
    Representation.IsLAdic ell (CondensedLisseMonodromy.Coeff.{u} ell) A.P V.V
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv
        (CondensedLisseMonodromy.Coeff.{u} ell) V.V).toMonoidHom.comp
        (Representation.asGroupHom (V.ρ.comp A.geometric))))

/-- The specified generic fibre, retaining the scalar ring at the geometric point.
Source: the displayed V_F in the node; thm-lisse-qlbar-representations, Fibres
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev fibre :=
  forget ell (D.geometricFrobenius U₀) ⋙
    LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) t

/-- Natural identification with the specified actual additive generic fibre.
Source: the displayed V_F in rem-dl-a1-conventions
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev FibreComparison (A : Geometry D U₀ t G)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A) :=
  e.functor ⋙ ObjectProperty.ι _ ⋙
      forget₂ (Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G))
        (ModuleCat.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell)) ⋙
      forget₂ (ModuleCat.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell)) Ab.{u + 1} ≅
    fibre D U₀ t ell ⋙ forget₂ _ Ab.{u + 1}

/-- The canonical relative tensor of the underlying Weil pairs.
Source: sk-def-sf-weil-complexes, tensor of fixed pairs
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
def pairTensor {X : Scheme.{u}} (g : X ≅ X) (F H : Lisse ell g) :
    CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj ell) g :=
  Endofunctor.IsoAlgebra.mk (F.obj.carrier ⊗ H.obj.carrier)
    ((Functor.Monoidal.μIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) g.hom)
      F.obj.carrier H.obj.carrier).symm ≪≫ (F.obj.str ⊗ᵢ H.obj.str))

/-- The canonical unit pair with its coefficient pullback comparison.
Source: sk-def-sf-weil-complexes, tensor unit
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
def pairUnit {X : Scheme.{u}} (g : X ≅ X) :
    CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj ell) g :=
  Endofunctor.IsoAlgebra.mk (𝟙_ (RealCondensedFibre.Modules
    (Profinite.padicAlgClRingObj ell) X))
      (Functor.Monoidal.εIso
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) g.hom)).symm

/-- Restriction to the chosen component, compared on the actual point sections.
Source: the component restriction in proof steps 1--2 and the displayed V_F
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def restrictionComparison (A : Geometry D U₀ t G)
    (F : Lisse ell (D.geometricFrobenius U₀)) :
    (LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) A.point).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier) ≅ (fibre D U₀ t ell).obj F :=
  (RealCondensedFibre.pullback (Profinite.padicAlgClRingObj ell)
    A.inclusion A.point).app F.obj.carrier ≪≫
      eqToIso (congrArg (fun z ↦
        (LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) z).obj F.obj.carrier) A.point_eq)

/-- Geometric transport, compared in the category of the actual additive fibres.
Source: the geometric action in Weil II (1.1.12), normalized by finite fibres
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def geometricMap (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (F : Lisse ell (D.geometricFrobenius U₀)) (a : A.P)
    (hL : RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)) :
    AddCommGrpCat.of ((fibre D U₀ t ell).obj F) ≅
      AddCommGrpCat.of ((fibre D U₀ t ell).obj F) :=
  (forget₂ _ Ab.{u + 1}).mapIso (restrictionComparison D U₀ t G ell A F).symm ≪≫
    (S.paths A.component).algebraic.map A.point A.point
      (PreGaloisCategory.toAut (FiniteEtale.fiber A.point) A.P a) _ hL ≪≫
    (forget₂ _ Ab.{u + 1}).mapIso (restrictionComparison D U₀ t G ell A F)

/-- The specified return operator: inverse normalized path, pullback composition, then
iterate theta. Exponent n means n+1, including the first return when n=0.
Source: Weil II (1.1.10)--(1.1.12); proof steps 4 and 7
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def returnMap (A : Geometry D U₀ t G) (S : RealCondensedFibre.System.{u} ell)
    (F : Lisse ell (D.geometricFrobenius U₀)) (n : ℕ)
    (z : Spec (.of Ω) ⟶ A.component.X)
    (hz : z ≫ A.inclusion =
      t ≫ WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom n)
    (τ : FiniteEtale.fiber z ≅ FiniteEtale.fiber A.point)
    (hL : RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)) :
    AddCommGrpCat.of ((fibre D U₀ t ell).obj F) ≅
      AddCommGrpCat.of ((fibre D U₀ t ell).obj F) :=
  (forget₂ _ Ab.{u + 1}).mapIso (restrictionComparison D U₀ t G ell A F).symm ≪≫
    ((S.paths A.component).algebraic.map A.point z τ.symm _ hL) ≪≫
    (forget₂ _ Ab.{u + 1}).mapIso
      ((RealCondensedFibre.pullback (Profinite.padicAlgClRingObj ell)
        A.inclusion z).app F.obj.carrier) ≪≫
    eqToIso (congrArg (fun x ↦ AddCommGrpCat.of
      ((LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) x).obj F.obj.carrier)) hz) ≪≫
    (forget₂ _ Ab.{u + 1}).mapIso
      (((RealCondensedFibre.pullback (Profinite.padicAlgClRingObj ell)
        (WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom n) t).app
          F.obj.carrier).symm ≪≫
        (LisseQlbar.fibre (Profinite.padicAlgClRingObj ell) t).mapIso
          (WeilConjectures.CondensedModule.iterate ell (D.geometricFrobenius U₀).hom
            F.obj.carrier F.obj.str n))

/-- The usual diagonal tensor and the Frobenius tensor structure on actual module pairs.
Source: Weil II (1.1.1), (1.1.12), and the node's tensor assertion
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
def tensorCompatibility (A : Geometry D U₀ t G)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A) : Prop :=
  ∃ (mW : MonoidalCategory (Lisse ell (D.geometricFrobenius U₀)))
    (mR : MonoidalCategory (Representations D U₀ t G ell A)),
    ∃ (FW : @Functor.Monoidal _ _ mW _ _ _ (forget ell (D.geometricFrobenius U₀)))
      (FR : @Functor.Monoidal _ _ mR _ _ _ (ObjectProperty.ι _)),
    Nonempty (@Functor.Monoidal _ _ mW _ _ mR e.functor) ∧
    (∀ F H : Lisse ell (D.geometricFrobenius U₀),
      (mW.toMonoidalCategoryStruct.tensorObj F H).obj =
        pairTensor ell (D.geometricFrobenius U₀) F H) ∧
    mW.toMonoidalCategoryStruct.tensorUnit.obj = pairUnit ell (D.geometricFrobenius U₀) ∧
    (∀ V W : Representations D U₀ t G ell A,
      (mR.toMonoidalCategoryStruct.tensorObj V W).obj = V.obj ⊗ W.obj) ∧
    mR.toMonoidalCategoryStruct.tensorUnit.obj =
      𝟙_ (Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G)) ∧
    (∀ F H : Lisse ell (D.geometricFrobenius U₀),
      ∃ h : (mW.toMonoidalCategoryStruct.tensorObj F H).obj.carrier =
          F.obj.carrier ⊗ H.obj.carrier,
        @Functor.LaxMonoidal.μ _ _ mW _ _ _ (forget ell (D.geometricFrobenius U₀))
          FW.toLaxMonoidal F H = eqToHom h.symm) ∧
    (∃ h : mW.toMonoidalCategoryStruct.tensorUnit.obj.carrier =
        𝟙_ (RealCondensedFibre.Modules (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber U₀).left),
      @Functor.LaxMonoidal.ε _ _ mW _ _ _ (forget ell (D.geometricFrobenius U₀))
        FW.toLaxMonoidal = eqToHom h.symm) ∧
    (∀ V W : Representations D U₀ t G ell A,
      ∃ h : (mR.toMonoidalCategoryStruct.tensorObj V W).obj = V.obj ⊗ W.obj,
        @Functor.LaxMonoidal.μ _ _ mR _ _ _ (ObjectProperty.ι _)
          FR.toLaxMonoidal V W = eqToHom h.symm) ∧
    (∃ h : mR.toMonoidalCategoryStruct.tensorUnit.obj =
        𝟙_ (Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G)),
      @Functor.LaxMonoidal.ε _ _ mR _ _ _ (ObjectProperty.ι _)
        FR.toLaxMonoidal = eqToHom h.symm)

/-- The geometric-action formula, retaining the actual normalized path map.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def geometricCompatibility (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A)
    (β : FibreComparison D U₀ t G ell A e)
    (hL : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)) : Prop :=
  ∀ (F : Lisse ell (D.geometricFrobenius U₀)) (a : A.P)
    (v : (e.functor.obj F).obj.V),
    β.hom.app F ((e.functor.obj F).obj.ρ (A.geometric a) v) =
      (geometricMap D U₀ t G ell A S F a (hL F)).hom
        (β.hom.app F v)

/-- The return formula for every positive original integer degree.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def returnCompatibility (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A)
    (β : FibreComparison D U₀ t G ell A e)
    (hL : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)) : Prop :=
  ∀ (w : Group D U₀ t G) (n : ℕ),
    degree D U₀ t G w = Multiplicative.ofAdd (n + 1 : ℤ) →
    ∃ (z : Spec (.of Ω) ⟶ A.component.X)
      (hz : z ≫ A.inclusion =
        t ≫ WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom n)
      (τ : FiniteEtale.fiber z ≅ FiniteEtale.fiber A.point)
      (hpoint : z ≫ (A.inclusion ≫ projection D U₀) = t ≫ projection D U₀),
      (eqToIso (congrArg FiniteEtale.fiber hpoint)).symm ≪≫
        FiniteEtale.pullbackPathIso (A.inclusion ≫ projection D U₀) τ ≪≫
        eqToIso (congrArg FiniteEtale.fiber
          ((Category.assoc A.point A.inclusion (projection D U₀)).symm.trans
            (congrArg (fun z ↦ z ≫ projection D U₀) A.point_eq))) =
          (PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D U₀)) G w.val.1)⁻¹ ∧
      ∀ (F : Lisse ell (D.geometricFrobenius U₀))
        (v : (e.functor.obj F).obj.V),
        β.hom.app F ((e.functor.obj F).obj.ρ w v) =
          (returnMap D U₀ t G ell A S F n z hz τ (hL F)).hom
            (β.hom.app F v)

/-- The canonical pure-tensor fibre comparison and its Weil equivariance.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def tensorFibreCompatibility (A : Geometry D U₀ t G)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A)
    (β : FibreComparison D U₀ t G ell A e)
    (hTensor : ∀ F H : Lisse ell (D.geometricFrobenius U₀),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
      (pairTensor ell (D.geometricFrobenius U₀) F H).carrier) : Prop :=
  ∀ F H : Lisse ell (D.geometricFrobenius U₀),
    ∃ b : ((e.functor.obj F).obj.V ⊗[CondensedLisseMonodromy.Coeff.{u} ell]
        (e.functor.obj H).obj.V) ≃ₗ[CondensedLisseMonodromy.Coeff.{u} ell]
      (e.functor.obj
        ⟨pairTensor ell (D.geometricFrobenius U₀) F H, hTensor F H⟩).obj.V,
      (∀ v w, β.hom.app
          ⟨pairTensor ell (D.geometricFrobenius U₀) F H, hTensor F H⟩
            (b (v ⊗ₜ[CondensedLisseMonodromy.Coeff.{u} ell] w)) =
        LisseQlbar.tensorPair (Profinite.padicAlgClRingObj ell) t F.obj.carrier H.obj.carrier
          (β.hom.app F v) (β.hom.app H w)) ∧
      ∀ a v w, b ((e.functor.obj F).obj.ρ a v ⊗ₜ[CondensedLisseMonodromy.Coeff.{u} ell]
          (e.functor.obj H).obj.ρ a w) =
        (e.functor.obj
          ⟨pairTensor ell (D.geometricFrobenius U₀) F H, hTensor F H⟩).obj.ρ a
            (b (v ⊗ₜ[CondensedLisseMonodromy.Coeff.{u} ell] w))

/-- The subobject correspondence, fixed to the actual range of each inclusion.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def subobjectCompatibility (A : Geometry D U₀ t G)
    (e : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A) : Prop :=
  ∀ F : Lisse ell (D.geometricFrobenius U₀),
    ∃ k : Subobject F ≃o Subrepresentation (e.functor.obj F).obj.ρ,
      ∀ H : Subobject F, (k H : Set (e.functor.obj F).obj.V) =
        Set.range ((e.functor.map H.arrow).hom.hom)

/-- The exact tensor equivalence on the actual generic fibre, together with its subobject
correspondence. The fibre identification is additive and its scalar law is explicit, so
it is linear for the canonical identification of point coefficients with Qbar_ell.
Source: rem-dl-a1-conventions, irreducible-lisse and geometric-constancy paragraphs
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
structure Assertions (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell) where
  equivalence : Lisse ell (D.geometricFrobenius U₀) ≌ Representations D U₀ t G ell A
  comparison : FibreComparison D U₀ t G ell A equivalence
  linear : ∀ (F : Lisse ell (D.geometricFrobenius U₀)) (a : CondensedLisseMonodromy.Coeff.{u} ell)
    (v : (equivalence.functor.obj F).obj.V),
    comparison.hom.app F (a • v) =
      @id ((fibre D U₀ t ell).obj F)
        (CondensedRing.affineScalarSection (Profinite.padicAlgClRingObj ell) (Spec (.of Ω))
          (Profinite.PadicAlgCl.constSectionRingHom ell (op (⊤_ Profinite.{u})) a.down) •
            @id ((fibre D U₀ t ell).obj F) (comparison.hom.app F v))
  restriction_lisse : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)
  geometric_action :
    geometricCompatibility D U₀ t G ell A S equivalence comparison restriction_lisse
  return_action : returnCompatibility D U₀ t G ell A S equivalence comparison restriction_lisse
  sourceAbelian : Nonempty (Abelian (Lisse ell (D.geometricFrobenius U₀)))
  targetAbelian : Nonempty (Abelian (Representations D U₀ t G ell A))
  exact : PreservesFiniteLimits equivalence.functor ∧
    PreservesFiniteColimits equivalence.functor
  inverse_exact : PreservesFiniteLimits equivalence.inverse ∧
    PreservesFiniteColimits equivalence.inverse
  forget_exact : PreservesFiniteLimits (forget ell (D.geometricFrobenius U₀)) ∧
    PreservesFiniteColimits (forget ell (D.geometricFrobenius U₀))
  tensor : tensorCompatibility D U₀ t G ell A equivalence
  tensor_lisse : ∀ F H : Lisse ell (D.geometricFrobenius U₀),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
      (pairTensor ell (D.geometricFrobenius U₀) F H).carrier
  unit_lisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
    (pairUnit ell (D.geometricFrobenius U₀)).carrier
  unit_trivial : Nonempty
    ((equivalence.functor.obj ⟨pairUnit ell (D.geometricFrobenius U₀), unit_lisse⟩).obj ≅
      Rep.trivial (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G)
        (ULift.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell)))
  tensor_comparison : tensorFibreCompatibility D U₀ t G ell A equivalence comparison tensor_lisse
  subobjects : subobjectCompatibility D U₀ t G ell A equivalence
  zero : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    IsZero F ↔ Subsingleton (equivalence.functor.obj F).obj.V


/-- Natural identification with the specified actual additive generic fibre.
Source: the displayed V_F in rem-dl-a1-conventions
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
abbrev FunctorFibreComparison (A : Geometry D U₀ t G)
    (E : Lisse ell (D.geometricFrobenius U₀) ⥤ Representations D U₀ t G ell A) :=
  E ⋙ ObjectProperty.ι _ ⋙
      forget₂ (Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G))
        (ModuleCat.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell)) ⋙
      forget₂ (ModuleCat.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell)) Ab.{u + 1} ≅
    fibre D U₀ t ell ⋙ forget₂ _ Ab.{u + 1}

/-- The usual diagonal tensor and the Frobenius tensor structure on actual module pairs.
Source: Weil II (1.1.1), (1.1.12), and the node's tensor assertion
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
def functorTensorCompatibility (A : Geometry D U₀ t G)
    (E : Lisse ell (D.geometricFrobenius U₀) ⥤ Representations D U₀ t G ell A) : Prop :=
  ∃ (mW : MonoidalCategory (Lisse ell (D.geometricFrobenius U₀)))
    (mR : MonoidalCategory (Representations D U₀ t G ell A)),
    ∃ (FW : @Functor.Monoidal _ _ mW _ _ _ (forget ell (D.geometricFrobenius U₀)))
      (FR : @Functor.Monoidal _ _ mR _ _ _ (ObjectProperty.ι _)),
    Nonempty (@Functor.Monoidal _ _ mW _ _ mR E) ∧
    (∀ F H : Lisse ell (D.geometricFrobenius U₀),
      (mW.toMonoidalCategoryStruct.tensorObj F H).obj =
        pairTensor ell (D.geometricFrobenius U₀) F H) ∧
    mW.toMonoidalCategoryStruct.tensorUnit.obj = pairUnit ell (D.geometricFrobenius U₀) ∧
    (∀ V W : Representations D U₀ t G ell A,
      (mR.toMonoidalCategoryStruct.tensorObj V W).obj = V.obj ⊗ W.obj) ∧
    mR.toMonoidalCategoryStruct.tensorUnit.obj =
      𝟙_ (Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G)) ∧
    (∀ F H : Lisse ell (D.geometricFrobenius U₀),
      ∃ h : (mW.toMonoidalCategoryStruct.tensorObj F H).obj.carrier =
          F.obj.carrier ⊗ H.obj.carrier,
        @Functor.LaxMonoidal.μ _ _ mW _ _ _ (forget ell (D.geometricFrobenius U₀))
          FW.toLaxMonoidal F H = eqToHom h.symm) ∧
    (∃ h : mW.toMonoidalCategoryStruct.tensorUnit.obj.carrier =
        𝟙_ (RealCondensedFibre.Modules (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber U₀).left),
      @Functor.LaxMonoidal.ε _ _ mW _ _ _ (forget ell (D.geometricFrobenius U₀))
        FW.toLaxMonoidal = eqToHom h.symm) ∧
    (∀ V W : Representations D U₀ t G ell A,
      ∃ h : (mR.toMonoidalCategoryStruct.tensorObj V W).obj = V.obj ⊗ W.obj,
        @Functor.LaxMonoidal.μ _ _ mR _ _ _ (ObjectProperty.ι _)
          FR.toLaxMonoidal V W = eqToHom h.symm) ∧
    (∃ h : mR.toMonoidalCategoryStruct.tensorUnit.obj =
        𝟙_ (Rep.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G)),
      @Functor.LaxMonoidal.ε _ _ mR _ _ _ (ObjectProperty.ι _)
        FR.toLaxMonoidal = eqToHom h.symm)

/-- The geometric-action formula, retaining the actual normalized path map.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def functorGeometricCompatibility (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (E : Lisse ell (D.geometricFrobenius U₀) ⥤ Representations D U₀ t G ell A)
    (β : FunctorFibreComparison D U₀ t G ell A E)
    (hL : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)) : Prop :=
  ∀ (F : Lisse ell (D.geometricFrobenius U₀)) (a : A.P)
    (v : (E.obj F).obj.V),
    β.hom.app F ((E.obj F).obj.ρ (A.geometric a) v) =
      (geometricMap D U₀ t G ell A S F a (hL F)).hom
        (β.hom.app F v)

/-- The return formula for every positive original integer degree.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def functorReturnCompatibility (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell)
    (E : Lisse ell (D.geometricFrobenius U₀) ⥤ Representations D U₀ t G ell A)
    (β : FunctorFibreComparison D U₀ t G ell A E)
    (hL : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)) : Prop :=
  ∀ (w : Group D U₀ t G) (n : ℕ),
    degree D U₀ t G w = Multiplicative.ofAdd (n + 1 : ℤ) →
    ∃ (z : Spec (.of Ω) ⟶ A.component.X)
      (hz : z ≫ A.inclusion =
        t ≫ WeilConjectures.localPositivePower (D.geometricFrobenius U₀).hom n)
      (τ : FiniteEtale.fiber z ≅ FiniteEtale.fiber A.point)
      (hpoint : z ≫ (A.inclusion ≫ projection D U₀) = t ≫ projection D U₀),
      (eqToIso (congrArg FiniteEtale.fiber hpoint)).symm ≪≫
        FiniteEtale.pullbackPathIso (A.inclusion ≫ projection D U₀) τ ≪≫
        eqToIso (congrArg FiniteEtale.fiber
          ((Category.assoc A.point A.inclusion (projection D U₀)).symm.trans
            (congrArg (fun z ↦ z ≫ projection D U₀) A.point_eq))) =
          (PreGaloisCategory.toAut (FiniteEtale.fiber (t ≫ projection D U₀)) G w.val.1)⁻¹ ∧
      ∀ (F : Lisse ell (D.geometricFrobenius U₀))
        (v : (E.obj F).obj.V),
        β.hom.app F ((E.obj F).obj.ρ w v) =
          (returnMap D U₀ t G ell A S F n z hz τ (hL F)).hom
            (β.hom.app F v)

/-- The canonical pure-tensor fibre comparison and its Weil equivariance.
Source: rem-dl-a1-conventions; Weil II (1.1.10)--(1.1.12)
(blueprint: lem-dl-a1-condensed-weil-generic-representation). -/
@[irreducible] def functorTensorFibreCompatibility (A : Geometry D U₀ t G)
    (E : Lisse ell (D.geometricFrobenius U₀) ⥤ Representations D U₀ t G ell A)
    (β : FunctorFibreComparison D U₀ t G ell A E)
    (hTensor : ∀ F H : Lisse ell (D.geometricFrobenius U₀),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
      (pairTensor ell (D.geometricFrobenius U₀) F H).carrier) : Prop :=
  ∀ F H : Lisse ell (D.geometricFrobenius U₀),
    ∃ b : ((E.obj F).obj.V ⊗[CondensedLisseMonodromy.Coeff.{u} ell]
        (E.obj H).obj.V) ≃ₗ[CondensedLisseMonodromy.Coeff.{u} ell]
      (E.obj
        ⟨pairTensor ell (D.geometricFrobenius U₀) F H, hTensor F H⟩).obj.V,
      (∀ v w, β.hom.app
          ⟨pairTensor ell (D.geometricFrobenius U₀) F H, hTensor F H⟩
            (b (v ⊗ₜ[CondensedLisseMonodromy.Coeff.{u} ell] w)) =
        LisseQlbar.tensorPair (Profinite.padicAlgClRingObj ell) t F.obj.carrier H.obj.carrier
          (β.hom.app F v) (β.hom.app H w)) ∧
      ∀ a v w, b ((E.obj F).obj.ρ a v ⊗ₜ[CondensedLisseMonodromy.Coeff.{u} ell]
          (E.obj H).obj.ρ a w) =
        (E.obj
          ⟨pairTensor ell (D.geometricFrobenius U₀) F H, hTensor F H⟩).obj.ρ a
            (b (v ⊗ₜ[CondensedLisseMonodromy.Coeff.{u} ell] w))

/-- The normalized fibre action and tensor comparisons, before proving descent.
Source: Weil II (1.1.10)--(1.1.12), construction in proof steps 4 and 7--8.
(blueprint: def-dl-a1-condensed-generic-weil-data). -/
structure NormalizedFunctor (A : Geometry D U₀ t G)
    (S : RealCondensedFibre.System.{u} ell) where
  functor : Lisse ell (D.geometricFrobenius U₀) ⥤ Representations D U₀ t G ell A
  comparison : FunctorFibreComparison D U₀ t G ell A functor
  linear : ∀ (F : Lisse ell (D.geometricFrobenius U₀)) (a : CondensedLisseMonodromy.Coeff.{u} ell)
    (v : (functor.obj F).obj.V),
    comparison.hom.app F (a • v) =
      @id ((fibre D U₀ t ell).obj F)
        (CondensedRing.affineScalarSection (Profinite.padicAlgClRingObj ell) (Spec (.of Ω))
          (Profinite.PadicAlgCl.constSectionRingHom ell (op (⊤_ Profinite.{u})) a.down) •
            @id ((fibre D U₀ t ell).obj F) (comparison.hom.app F v))
  restriction_lisse : ∀ F : Lisse ell (D.geometricFrobenius U₀),
    RealCondensedFibre.Lisse (Profinite.padicAlgClRingObj ell)
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) A.inclusion).obj
        F.obj.carrier)
  geometric_action :
    functorGeometricCompatibility D U₀ t G ell A S functor comparison restriction_lisse
  return_action : functorReturnCompatibility D U₀ t G ell A S functor comparison restriction_lisse
  tensor : functorTensorCompatibility D U₀ t G ell A functor
  tensor_lisse : ∀ F H : Lisse ell (D.geometricFrobenius U₀),
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
      (pairTensor ell (D.geometricFrobenius U₀) F H).carrier
  unit_lisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell)
    (pairUnit ell (D.geometricFrobenius U₀)).carrier
  unit_trivial : Nonempty
    ((functor.obj ⟨pairUnit ell (D.geometricFrobenius U₀), unit_lisse⟩).obj ≅
      Rep.trivial (CondensedLisseMonodromy.Coeff.{u} ell) (Group D U₀ t G)
        (ULift.{u + 1} (CondensedLisseMonodromy.Coeff.{u} ell)))
  tensor_comparison : functorTensorFibreCompatibility D U₀ t G ell A functor comparison tensor_lisse

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
