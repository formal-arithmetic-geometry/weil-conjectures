/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.AlgebraicGeometry.CartierReductionData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Finite root comparison between the etale and pro-etale sites

Source: Stacks Project, proetale.tex, Tag 0GLZ, lemma-describe-pullback-from-etale;
sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback
(blueprint: lem-amb-finite-root-site-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The recorded root module in the fixed `ZMod m` coefficient presentation.
Restriction along constant sections retains exactly the original root sections.
Source: Stacks Tags 03CY and 03PK (blueprint: lem-amb-finite-root-site-comparison). -/
def finiteRootProModule (T : Scheme.{u}) (m : ℕ) (hm : 0 < m) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ZMod m)) :=
  (sheafCompose (ProEt.topology T)
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv.{0, u + 1} (R := ZMod m)).symm.toRingHom)).obj
      ((constantRingModuleRestriction (ProEt.topology T) (ULift.{u + 1} (ZMod m))).obj
        (proEtaleRootsOfUnityModule T m hm))

/-- The actual balanced scalar extension of the root sheaf, sheafified sectionwise.
This is `D_m,T`, with the `A` factor first, as in the recorded etale construction.
Source: Stacks Tags 03EK and 03EL (blueprint: lem-amb-finite-root-site-comparison). -/
def finiteRootProTensor (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A) :=
  (presheafToSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)).obj
    ((finiteRootProModule T m hm).obj ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))

/-- A local tensor `z ⊗ a`, written `a ⊗ z`, followed by the sheafification unit.
Source: Stacks Tags 03EK and 03EL (blueprint: lem-amb-finite-root-site-comparison). -/
def finiteRootProGenerator (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (T : Scheme.{u}) (W : T.ProEtᵒᵖ) (a : A)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W) :
    (finiteRootProTensor A m hm hA T).obj.obj W :=
  (toSheafify (ProEt.topology T)
    ((finiteRootProModule T m hm).obj ⋙
      ModuleCat.extendScalars (finiteEtaleTwistScalar m A hA))).app W
        (a ⊗ₜ[ZMod m, finiteEtaleTwistScalar m A hA] z)


attribute [irreducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

/-- The normalized comparison, with scalar, scheme, identity, composition and power laws.
The root comparison is the already constructed `ProEtale.cartierRootsIso`. Additive root
maps are linear for the unique constant `ZMod m` actions; the tensor arrows live in
`ModuleCat A` and hence are linear for the corresponding constant ring sheaves.
Source: Stacks Tags 0GLZ, 03CY and 03EL
(blueprint: lem-amb-finite-root-site-comparison). -/
def FiniteRootSiteComparisonSpec (A : Type (u + 1)) [CommRing A] : Prop :=
  ∃ (sigma : ∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (finiteEtaleTateLine T m A hA) ≅ finiteRootProTensor A m hm hA T)),
  ∃ (d : ∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T),
      (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).obj
        (finiteRootProTensor A m hm hA T) ⟶ finiteRootProTensor A m hm hA T'),
  /- root_sections: The section identification on every weakly etale test, through etale global
     sections. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (W : T.ProEt),
    ∃ e : ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        (T.rootsOfUnitySheaf m)).obj.obj (op W) ≃+
      ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj
        (T.rootsOfUnitySheaf m)).obj.obj (op (Etale.mk (𝟙 W.left))),
    ∀ x,
      ((proEtaleRootsOfUnityInclusion T m).hom.app (op W)
        ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app (op W) x)).down =
      ((kernel.ι (m • 𝟙 W.left.gmSheaf)).hom.app (op (Etale.mk (𝟙 W.left)))
        (((finiteEtaleTwistPullbackData A m hm hA).r W.hom hT).hom.hom.app
          (op (Etale.mk (𝟙 W.left))) (e x))).down) ∧
  /- root_unit: The root comparison takes a unit to the same unit after restriction. -/
  (∀ (m : ℕ) (hm : 0 < m) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (z : (T.rootsOfUnitySheaf m).obj.obj U),
    Additive.toMul (((proEtaleRootsOfUnityInclusion T m).hom.app W
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z)))).down) =
      Units.map f.left.appTop.hom.toMonoidHom
        (Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app U z).down))) ∧
  /- tensor_unit: Balanced-tensor normalization, including restriction to arbitrary pro-etale
     tests. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : A)
    (z : (T.rootsOfUnitySheaf m).obj.obj U),
    (sigma m hm hA T hT).hom.hom.app W
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (finiteEtaleTateLine T m A hA)).obj.map f.op
          (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
            (finiteEtaleTateLine T m A hA)).hom.app U
              (finiteEtaleTateOneGenerator A m T hA U a z))) =
    finiteRootProGenerator A m hm hA T W a
      ((ProEtale.cartierRootsIso T m hm hT).hom.hom.app W
        (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf m)).obj.map f.op
            (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
              (T.rootsOfUnitySheaf m)).hom.app U z)))) ∧
  /- d_unit: The adjunct of d is scalar extension of the recorded projection map on roots. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (W : T.ProEtᵒᵖ) (a : A)
    (z : (proEtaleRootsOfUnitySheaf T m).obj.obj W),
    ((proEtaleSheafAdjunction v (ModuleCat.{u + 1} A)).homEquiv _ _
      (d m hm hA v)).hom.app W (finiteRootProGenerator A m hm hA T W a z) =
    finiteRootProGenerator A m hm hA T' ((proEtaleBaseChange v).op.obj W) a
      ((proEtaleRootsOfUnityDirectImageMap v m).hom.app W z)) ∧
  /- scheme_square: The specified comparison square, with kappa the inverse of the recorded mate. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))),
    (proEtaleSheafInverseImage v (ModuleCat.{u + 1} A)).map
        (sigma m hm hA T hT).hom ≫ d m hm hA v =
    (ProEtale.comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) v).inv.app
        (finiteEtaleTateLine T m A hA) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map
        ((finiteEtaleTwistPullbackData A m hm hA).c v hT hT' 1).hom ≫
      (sigma m hm hA T' hT').hom) ∧
  /- d_isIso: Invertibility of d, for every scheme map. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T), IsUnit (m : Γ(T, ⊤)) → IsIso (d m hm hA v)) ∧
  /- root_square: The corresponding square before extending scalars. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))),
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
        (ProEtale.cartierRootsIso T m hm hT).hom ≫
      proEtaleRootsOfUnityInverseImageMap v m =
    (ProEtale.comparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} v).inv.app
        (T.rootsOfUnitySheaf m) ≫
      (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T').map
        ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom ≫
      (ProEtale.cartierRootsIso T' m hm hT').hom) ∧
  /- d_id: The identity law uses the canonical inverse-image identity comparison. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u}),
    IsUnit (m : Γ(T, ⊤)) →
    d m hm hA (𝟙 T) = (ProEtale.proEtaleComparisonId (ModuleCat.{u + 1} A) T).hom.app
      (finiteRootProTensor A m hm hA T)) ∧
  /- d_comp: The composition law uses the canonical inverse-image composition comparison. -/
  (∀ (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T'),
    IsUnit (m : Γ(T, ⊤)) →
    d m hm hA (w ≫ v) =
      (ProEtale.proEtaleComparisonComp (ModuleCat.{u + 1} A) w v).hom.app
        (finiteRootProTensor A m hm hA T) ≫
      (proEtaleSheafInverseImage w (ModuleCat.{u + 1} A)).map (d m hm hA v) ≫
      d m hm hA w) ∧
  /- root_id: Root pullback has the same identity normalization. -/
  (∀ (m : ℕ) (T : Scheme.{u}), 0 < m → IsUnit (m : Γ(T, ⊤)) →
    proEtaleRootsOfUnityInverseImageMap (𝟙 T) m =
      (ProEtale.proEtaleComparisonId AddCommGrpCat.{u + 1} T).hom.app
        (proEtaleRootsOfUnitySheaf T m)) ∧
  /- root_comp: Root pullback has the same composition normalization. -/
  (∀ (m : ℕ) {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T'),
    0 < m → IsUnit (m : Γ(T, ⊤)) →
    proEtaleRootsOfUnityInverseImageMap (w ≫ v) m =
      (ProEtale.proEtaleComparisonComp AddCommGrpCat.{u + 1} w v).hom.app
        (proEtaleRootsOfUnitySheaf T m) ≫
      (proEtaleSheafInverseImage w AddCommGrpCat.{u + 1}).map
        (proEtaleRootsOfUnityInverseImageMap v m) ≫
      proEtaleRootsOfUnityInverseImageMap w m) ∧
  /- powers: Power maps commute with root and tensor comparisons, with unchanged A scalars. -/
  (∀ (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (hdiv : m ∣ m')
    (hA : (m : A) = 0) (hA' : (m' : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m' : Γ(T, ⊤))),
    ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
      (tE : finiteEtaleTateLine T m' A hA' ⟶ finiteEtaleTateLine T m A hA)
      (tP : finiteRootProTensor A m' hm' hA' T ⟶ finiteRootProTensor A m hm hA T),
    q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
    (∀ (U : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj U),
      tE.hom.app U (finiteEtaleTateOneGenerator A m' T hA' U a z) =
        finiteEtaleTateOneGenerator A m T hA U a (q.hom.app U z)) ∧
    (∀ (W : T.ProEtᵒᵖ) (a : A) (z : (proEtaleRootsOfUnitySheaf T m').obj.obj W),
      tP.hom.app W (finiteRootProGenerator A m' hm' hA' T W a z) =
        finiteRootProGenerator A m hm hA T W a
          ((proEtaleRootsOfUnityTransition T m m' hm hm' hdiv).hom.app W z)) ∧
    ((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).map q ≫
        (ProEtale.cartierRootsIso T m hm hT).hom =
      (ProEtale.cartierRootsIso T m' hm' hT').hom ≫
        proEtaleRootsOfUnityTransition T m m' hm hm' hdiv) ∧
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map tE ≫
        (sigma m hm hA T hT).hom = (sigma m' hm' hA' T hT').hom ≫ tP))

/-- The finite root comparison with its specified scalar and scheme coherence exists.
Source: Stacks Project, proetale.tex, Tag 0GLZ; sites-modules.tex, Tag 03EL
(blueprint: lem-amb-finite-root-site-comparison).

Proof:
1. Apply lem-cbc-comparison-pullback-sections to the underlying set sheaf of etale
   roots. The normalized etale root pullback of lem-asd-etale-finite-twist-pullback
   identifies its sections on every weakly etale W with roots in Gamma(W,O).
   Restrictions act by pullback of units, so these identifications assemble into the
   existing cartierRootsIso. The unique torsion module action makes it Z/m-linear
   by lem-pur-torsion-sheaf-constant-module.
2. The comparison unit at an etale object is the same root section. Restriction along
   an arbitrary T-map W to U is pullback of that unit. Naturality in the root sheaf
   identifies the power transition with z to z^(m'/m) on every test.
3. Apply lem-weil-pbc-algebraic-inverse-image-tensor-comparison to roots and constant
   A. The constant-ring identifications of lem-sf-comparison-pullback-exact preserve
   constant sections. Tensor comparison followed by the root isomorphism gives sigma;
   the universal balanced tensor formula is exactly tensor_unit. No flatness is used.
4. For scheme pullback, the canonical comparison of lem-weil-pbc-comparison-pullback
   is the adjunction mate of the sectionwise equality of the composite direct images.
   Under composite adjunctions, both root-square arrows pull z back by the same
   fibre-product projection. Adjunction injectivity proves root_square.
5. The scalar map of prop-weil-pbc-proetale-constant-ring-map preserves constants.
   Define d by scalar extension of the recorded pro-etale root adjunct. Both adjuncts
   in scheme_square send z tensor a to its projection pullback tensor a. Scalars are
   locally constant and lem-pc-sites-sheaf-tensor-bilinear-universal determines maps
   on tensors, proving the square. Its other factors are invertible, hence so is d.
6. For identities all projection formulas are identities. For composites, successive
   pullbacks of units equal pullback along the composite under the canonical product
   comparison. The same adjunct calculation proves the identity and composition laws.
   For m dividing m', the transition z tensor a to z^(m'/m) tensor a is balanced over
   Z/m' because its action on A factors through Z/m. Naturality and tensor universality
   prove both power squares. These arguments also cover m=1, the zero ring and empty T.
-/
theorem finiteRootSiteComparison (A : Type (u + 1)) [CommRing A] [Finite A] :
    FiniteRootSiteComparisonSpec A := by
  sorry

end AlgebraicGeometry.Scheme
