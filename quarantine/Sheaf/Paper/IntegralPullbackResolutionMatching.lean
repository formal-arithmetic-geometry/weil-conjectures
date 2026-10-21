/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.IntegralTowerInverseImageUnit
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Paper.IntegralPullbackReductionCounit

/-!
# The counit identity for the integral inverse-image comparison

Source: blueprint Global powers in
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`;
Stacks Project, Tags 0FND, 0DVC, 03CZ, 06YY and 0941
(blueprint: lem-trf-integral-pullback-resolution-matching).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Translate invertibility of ell in the stalks into the residue-field instance
required by the recorded realization. This is the image of the same unit under
Scheme.residue, with no new hypothesis. Source: blueprint Global powers
(blueprint: lem-trf-integral-pullback-resolution-matching). -/
@[instance_reducible] def integralResolutionMatchingResidueInvertible (l : ℕ) (X : Scheme.{u})
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    ∀ x : X, Invertible (l : X.residueField x) :=
  fun x ↦
    ((map_natCast (X.residue x).hom l) ▸
      ((hX x).map (X.residue x).hom)).invertible

private theorem counitIdentity_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H F : A ⥤ B) (L : B ⥤ C) (T : A ⥤ C)
    (γ : F ⋙ L ⟶ T) (β : H ⋙ L ⟶ T)
    {X Y : A} (r : X ≅ Y) (aX : H.obj X ⟶ F.obj X) (aY : H.obj Y ⟶ F.obj Y)
    (ha : H.map r.hom ≫ aY = aX ≫ F.map r.hom)
    (hX : L.map aX ≫ γ.app X = β.app X) :
    L.map aY ≫ γ.app Y = β.app Y := by
  apply (cancel_epi (L.map (H.map r.hom))).1
  calc
    _ = L.map (H.map r.hom ≫ aY) ≫ γ.app Y := by
      rw [Functor.map_comp, Category.assoc]
    _ = L.map (aX ≫ F.map r.hom) ≫ γ.app Y := by rw [ha]
    _ = L.map aX ≫ γ.app X ≫ T.map r.hom := by
      rw [Functor.map_comp, Category.assoc, ← γ.naturality]
      rfl
    _ = (H ⋙ L).map r.hom ≫ β.app Y := by
      rw [← Category.assoc, hX, β.naturality]
    _ = _ := rfl

private theorem unit_map_counit
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {X : A} {Y : B} (f : X ⟶ G.obj Y) :
    adj.unit.app X ≫ G.map (F.map f ≫ adj.counit.app Y) = f := by
  rw [Functor.map_comp, ← Category.assoc, adj.unit_naturality f,
    Category.assoc, adj.right_triangle_components, Category.comp_id]

private theorem chosenResolution_formula
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (M : DerivedCategory (integralTowerModules l E W)) :
    ∃ (K : CochainComplex (integralTowerModules l E W) ℤ)
      (eK : DerivedCategory.Q.obj K ≅ M)
      (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (q : P.obj ⟶ K) (hq : QuasiIso q),
      let := hq
      inverseImagePullbackComparisonDerived l E h hZ hW M =
        (inverseImageIntegralDerived l E h).map eK.inv ≫
        (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (integralDerivedPullbackComparison l E h).inv.app P ≫
        (integralDerivedPullback l E h).map (DerivedCategory.Q.map q) ≫
        (integralDerivedPullback l E h).map eK.hom := by
  unfold inverseImagePullbackComparisonDerived
  extract_lets K e hp P q hq
  let P' : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory :=
    ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
      (@SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
        (P.X i)).symm (hq.2.1 i)⟩
  refine ⟨K, e, P', q, hq.2.2.1, ?_⟩
  simp only [inverseImagePullbackComparison, Category.assoc]
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : IntegralComparisonSystem.{u} l)
  {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)

/-- The first pullback's actual whole quotient diagram, in the normalized
presentation supplied by the recorded realization. Source: blueprint Global powers;
Stacks 0941 (blueprint: lem-trf-integral-pullback-resolution-matching). -/
abbrev integralResolutionMatchingTower (N : sfIntegralConstructibleCategory l E V) :=
  (integralComparisonDerivedSequencePullback l E k).obj
    (((D.coefficient E).system V).reduction.obj N.obj)

/-- The recorded eta, using the stalk formulation of ell invertibility.
The instances merely transport those units to the residue fields.
Source: blueprint Global powers; Stacks 0941
(blueprint: lem-trf-integral-pullback-resolution-matching). -/
def integralResolutionMatchingEta
    (hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (N : sfIntegralConstructibleCategory l E V) :
    (integralDerivedPullback l E h).obj ((integralDerivedPullback l E k).obj N.obj) ≅
      (coefficientSequenceLimit l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          (integralResolutionMatchingTower l E D k N)) := by
  letI := integralResolutionMatchingResidueInvertible l V hV
  letI := integralResolutionMatchingResidueInvertible l W hW
  letI := integralResolutionMatchingResidueInvertible l Z hZ
  exact integralComparisonEta l E D h k N

/-- The counit image of eta after kappa is exactly the termwise tensor-unit map
applied to the inverse image of the original counit. The equation lives in the
derived category of entire strict completed-coefficient towers. The defining
realization for k explicitly transports M to Rlim C; no levelwise reduction or
realization is applied to the asserted equality.

Source: blueprint Global powers in
sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md;
Stacks Project, Tags 0FND, 0DVC, 03CZ, 06YY and 0941
(blueprint: lem-trf-integral-pullback-resolution-matching).

Proof:
1. Put C=C_k, D=h-star C and H=h-inverse. Choose the separate flat-term K-flat
   resolution q:P' to M used by kappa. Its quotient tower is B and its pulled-back
   tower is C_h. The strict compatible family is theta=u_B after H(r), where r is
   the actual quotient map. The definition gives kappa=r_theta after H(q) inverse
   [def-pur-integral-derived-operations, def-weil-inverse-image-pullback-comparison].
2. The diagonal is exact by levelwise exactness of tower categories. Deriving the
   diagonal/limit adjunction by lem-pc-pre-derived-adjoint-functors-general gives
   the K-injective-normalized counit epsilon. Its naturality says epsilon_T' after
   Delta(Rlim psi)=psi after epsilon_T for every derived tower morphism psi,
   including roofs [lem-weil-pbc-ringed-strict-tower-homotopy-limit].
3. On the small diagram site, extension from the constant completed ring to the
   entire quotient-ring sheaf is left adjoint to exact coefficient restriction.
   Delta P' is K-flat with flat terms because tensor products and acyclicity are
   levelwise. Derived adjunction sends phi:B to C to U(phi) after r
   [lem-weil-pbc-diagram-site-realization, def-pc-sheaf-restrict-scalars,
   lem-pur-derived-change-of-rings, def-pc-kflat-complex, def-pur-sheaf-tensor-product].
4. Take phi adjunct to epsilon_C after Delta(q). The normalization of
   lem-trf-integral-pullback-comparison-realization identifies eta with Rlim(h-star
   phi); the adjunct identity is U(phi) after r=epsilon_C after Delta(q).
5. Exact countable products and lem-weil-strict-roos-comparison identify the cone
   used by kappa with the normalized Rlim C_h. Applying
   lem-trf-integral-cone-counit-realization to its compatible family gives
   epsilon_C_h after Delta(r_theta)=theta.
6. The finite unit is natural: both composites send x to phi(x) tensor 1.
   This commutes with quotient transitions and extends to roofs by exactness of
   H and finite pullback [lem-weil-tower-category-levelwise-abelian]. Therefore
   h-star(phi) after theta=u_C after H(epsilon_C) after Delta(H(q)).
7. Counit naturality, followed by steps 4--6, identifies the two sides after
   precomposition with Delta(H(q)). Exactness makes H(q) a quasi-isomorphism;
   cancel its invertible class to obtain the displayed whole-tower identity. -/
theorem integralPullbackResolutionMatching
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : IntegralComparisonSystem.{u} l) {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (N : sfIntegralConstructibleCategory l E V) :
    (integralComparisonConstantTower l E Z).map
        (inverseImagePullbackComparisonDerived l E h hZ hW
            ((integralDerivedPullback l E k).obj N.obj) ≫
          (integralResolutionMatchingEta l E D h k hV hW hZ N).hom) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj
              (integralResolutionMatchingTower l E D k N))) =
      (integralTowerInverseImageDiagonal l E h).hom.app
          ((integralDerivedPullback l E k).obj N.obj) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map
              (((D.coefficient E).pullback k).realization.hom.app N.obj) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj
                (integralResolutionMatchingTower l E D k N))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          (integralResolutionMatchingTower l E D k N) := by
  let := integralResolutionMatchingResidueInvertible l V hV
  let := integralResolutionMatchingResidueInvertible l W hW
  let := integralResolutionMatchingResidueInvertible l Z hZ
  let S := (D.coefficient E).system W
  let M := (integralDerivedPullback l E k).obj N.obj
  let C := integralResolutionMatchingTower l E D k N
  let v : S.reduction.obj M ⟶ C :=
    (integralComparisonPullbackCounit l E k ((D.coefficient E).system V)
      S ((D.coefficient E).roos W) ((D.coefficient E).pullback k)).app N.obj
  let a := inverseImagePullbackComparisonDerived l E h hZ hW M
  let e := ((D.coefficient E).pullback h).realization.hom.app M
  let δ := (integralComparisonConstantTower l E W).map (S.adjunction.unit.app M) ≫
    (integralComparisonTowerCounit l E W).app
      ((coefficientSequenceDerivedRestriction l E W).obj (S.reduction.obj M))
  have hbase :
      (integralComparisonConstantTower l E Z).map (a ≫ e) ≫
          (integralComparisonTowerCounit l E Z).app
            ((coefficientSequenceDerivedRestriction l E Z).obj
              ((integralComparisonDerivedSequencePullback l E h).obj (S.reduction.obj M))) =
        (integralTowerInverseImageDiagonal l E h).hom.app M ≫
          (integralDerivedTowerInverseImage l E h).map δ ≫
          (integralDerivedTowerInverseImageUnit l E h).hom.app (S.reduction.obj M) := by
    let F := ((D.coefficient E).pullback h)
    let H := inverseImageIntegralDerived l E h
    let ΔW := integralComparisonConstantTower l E W
    let ΔZ := integralComparisonConstantTower l E Z
    let U (X : Scheme.{u}) := coefficientSequenceDerivedRestriction.{u, u} l E X
    let B := integralComparisonDerivedSequencePullback l E h
    let Ht := integralDerivedTowerInverseImage l E h
    let d : ΔW ⟶ S.reduction ⋙ U W :=
      Functor.whiskerRight S.adjunction.unit ΔW ≫
        Functor.whiskerLeft (S.reduction ⋙ U W) (integralComparisonTowerCounit l E W)
    let γ : integralDerivedPullback l E h ⋙ ΔZ ⟶ S.reduction ⋙ B ⋙ U Z :=
      Functor.whiskerRight F.realization.hom ΔZ ≫
        Functor.whiskerLeft (S.reduction ⋙ B ⋙ U Z) (integralComparisonTowerCounit l E Z)
    let β : H ⋙ ΔZ ⟶ S.reduction ⋙ B ⋙ U Z :=
      (integralTowerInverseImageDiagonal l E h).hom ≫
        Functor.whiskerRight d Ht ≫
        Functor.whiskerLeft S.reduction (integralDerivedTowerInverseImageUnit l E h).hom
    obtain ⟨K, eK, P', q, hq, hformula⟩ :=
      chosenResolution_formula l E h hW hZ M
    let := hq
    let P := P'.obj
    let r : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map q) ≪≫ eK
    let aP := (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P) ≫
        (integralDerivedPullbackComparison l E h).inv.app P'
    have hP : ΔZ.map aP ≫ γ.app (DerivedCategory.Q.obj P) =
        β.app (DerivedCategory.Q.obj P) := by
      simpa only [γ, β, d, aP, P, F, H, ΔW, ΔZ, U, B, Ht, e, δ,
        Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatTrans.comp_app, Functor.map_comp, Category.assoc] using
        integralPullbackKFlatReductionCounit l E h S ((D.coefficient E).roos Z) F P'
    have ha : H.map r.hom ≫ a = aP ≫ (integralDerivedPullback l E h).map r.hom := by
      rw [show a = _ from hformula]
      simp only [r, Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc]
      rw [← Category.assoc (H.map eK.hom), ← H.map_comp,
        eK.hom_inv_id, H.map_id, Category.id_comp]
      erw [← Category.assoc (H.map (DerivedCategory.Q.map q)),
        (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.naturality q]
      simp only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc, aP, P]
    have ht := counitIdentity_transport H (integralDerivedPullback l E h) ΔZ
      (S.reduction ⋙ B ⋙ U Z) γ β r aP a ha hP
    simpa only [γ, β, d, F, H, ΔW, ΔZ, U, B, Ht, e, δ,
      Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.map_comp, Category.assoc] using ht
  have hv : S.adjunction.unit.app M ≫ (coefficientSequenceLimit l E W).map v =
      ((D.coefficient E).pullback k).realization.hom.app N.obj := by
    exact unit_map_counit S.adjunction
      (((D.coefficient E).pullback k).realization.hom.app N.obj)
  have hδ : δ ≫ (coefficientSequenceDerivedRestriction l E W).map v =
      (integralComparisonConstantTower l E W).map
          (((D.coefficient E).pullback k).realization.hom.app N.obj) ≫
        (integralComparisonTowerCounit l E W).app
          ((coefficientSequenceDerivedRestriction l E W).obj C) := by
    dsimp only [δ]
    erw [Category.assoc, ← (integralComparisonTowerCounit l E W).naturality
      ((coefficientSequenceDerivedRestriction l E W).map v)]
    change _ ≫ ((integralComparisonConstantTower l E W).map
      ((coefficientSequenceLimit l E W).map v) ≫ _) = _
    rw [← Category.assoc, ← Functor.map_comp, hv]
  change (integralComparisonConstantTower l E Z).map
      (a ≫ e ≫ (coefficientSequenceLimit l E Z).map
        ((integralComparisonDerivedSequencePullback l E h).map v)) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc]
  erw [(integralComparisonTowerCounit l E Z).naturality
    ((coefficientSequenceDerivedRestriction l E Z).map
      ((integralComparisonDerivedSequencePullback l E h).map v))]
  change _ ≫ ((integralComparisonConstantTower l E Z).map e ≫
    ((integralComparisonTowerCounit l E Z).app _ ≫
      (coefficientSequenceDerivedRestriction l E Z).map
        ((integralComparisonDerivedSequencePullback l E h).map v))) = _
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hbase]
  simp only [Category.assoc]
  erw [← (integralDerivedTowerInverseImageUnit l E h).hom.naturality v]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc ((integralDerivedTowerInverseImage l E h).map δ),
    ← Functor.map_comp, hδ]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end WeilConjectures
