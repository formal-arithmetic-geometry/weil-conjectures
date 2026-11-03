/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianDerivedExchangePlusCompatibility
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackIdentityNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsEtale
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData

/-!
# Finite affine right scalar composition coherence

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-affine-right-scalar-composition-coherence).

The statement records the canonical scalar/pullback comparison on the actual schemes and
coefficient rings of the node.  Its components are normalized on K-flat flat-term models,
are monoidal, commute with shifts, and compose with the inverse-image compositors.  The
finite Tate line maps are the balanced maps on the specified roots of unity; their source
maps use the same scalar comparison, and the displayed pullback and tensor-power equations
state the compatibility with the maps rho and with R(r) tensor R(s) = R(r+s).  The final
clause is the exact condensed chain-map package on small pro-etale sites.

Proof steps (the statement follows the seven chart calculations in the source).
1. Apply the K-flat scalar-comparison normalization to the identified coefficient rings.
   Its normalized comparison is gamma_f and its inverse is the scalar-adjunction mate;
   the K-flat representative equation fixes the comparison and gives identity and
   composition after the inverse-image compositors.
2. Resolve both inputs by flat-term K-flat complexes.  Pullback, scalar extension and
   the signed tensor model preserve these representatives, including for a non-flat
   coefficient map; equality on balanced generators descends through site tensor and
   derived localization.
3. On a homogeneous generator both tensor paths send
   f^-1((x tensor y) tensor b) to (f^-1 x tensor 1) tensor (f^-1 y tensor b).
   Bilinearity and the K-flat chain comparison give the displayed monoidal equation.
4. The cochain shift changes differentials by (-1)^a.  The scalar, tensor and pullback
   comparison maps have degree zero and use the same signed total-complex identification;
   hence they commute with shifts, in particular with the even shifts 2r in the chart.
5. For the Tate line, the balanced degree-zero map is
   (z tensor a) tensor b |-> z tensor phi(a)b, with inverse z tensor b |->
   (z tensor 1) tensor b.  Flatness of the finite-etale lines and induction on r give
   the tensor-power maps and their unit normalization.
6. For r=1, compare the two pullback squares on the inverse-image balancing generator;
   both paths give f^*z tensor phi(f^*a)b.  Induction, the monoidal equation, composition
   of pullbacks, and concatenation of the ordered Tate factors give all r,s equations.
7. Apply the condensed scalar-balancing-chain theorem on the small pro-etale sites.
   It supplies the coefficient square, the unique balanced tensor comparison, its degreewise
   differential equation and the signed-total chain map for every unbounded complex.

Source: Stacks Tags 03EL, 03PK, 07A4 and 0G7E; blueprint Charts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.Etale
open WeilConjectures.PurityFiniteSetting

private theorem assembleGammaFields {P Q R S : Prop}
    (hP : P) (hQ : Q) (hR : R) (hS : S) : P ∧ Q ∧ R ∧ S :=
  ⟨hP, hQ, hR, hS⟩

private theorem assembleCoherence
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ : Prop}
    {P₁₁ P₁₂ P₁₃ P₁₄ P₁₅ P₁₆ P₁₇ P₁₈ P₁₉ P₂₀ : Prop}
    (h₁ : P₁) (h₂ : P₂) (h₃ : P₃) (h₄ : P₄) (h₅ : P₅)
    (h₆ : P₆) (h₇ : P₇) (h₈ : P₈) (h₉ : P₉) (h₁₀ : P₁₀)
    (h₁₁ : P₁₁) (h₁₂ : P₁₂) (h₁₃ : P₁₃) (h₁₄ : P₁₄) (h₁₅ : P₁₅)
    (h₁₆ : P₁₆) (h₁₇ : P₁₇) (h₁₈ : P₁₈) (h₁₉ : P₁₉) (h₂₀ : P₂₀) :
    P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ∧ P₆ ∧ P₇ ∧ P₈ ∧ P₉ ∧ P₁₀ ∧
      P₁₁ ∧ P₁₂ ∧ P₁₃ ∧ P₁₄ ∧ P₁₅ ∧ P₁₆ ∧ P₁₇ ∧ P₁₈ ∧ P₁₉ ∧ P₂₀ :=
  ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀⟩

set_option maxHeartbeats 2000000 in
-- The statement and its K-flat comparison instances need a larger elaboration budget.
/-- Source: Charts in
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md`.
(blueprint: lem-sp-finite-affine-right-scalar-composition-coherence)

Proof: (1) identify the constant coefficients and apply K-flat scalar normalization;
the inverse mate is gamma and its balanced representative determines it uniquely.
(2) Choose flat-term K-flat models for both inputs; pullback and tensor preserve these
models, so localization detects the required equalities without coefficient flatness.
(3) Check the monoidal square on generators: both maps send the pulled-back balanced
tensor to the tensor of pulled-back generators with the same coefficient product.
(4) The degree-zero comparisons respect the signed shift identifications. This proves
the three canonical shift squares, including the even shifts of the Tate objects.
(5) The balanced Tate map sends (z tensor a) tensor b to z tensor phi(a)b; its inverse
sends z tensor b to (z tensor 1) tensor b. Tensor powers give all nonnegative r.
(6) Check the beta/rho square on roots of unity, then tensor the generators to obtain
all r,s. Pasting the u and v squares gives the displayed composite beta/rho square.
(7) Apply condensedScalarBalancingChain on the small pro-etale sites: its component
maps commute with every differential, hence define the required unbounded chain map. -/
theorem finiteAffineRightScalarCompositionCoherence
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (hZ : ∀ z : Z, IsUnit (N : Z.presheaf.stalk z))
    (u : X ⟶ Y) (v : Y ⟶ Z) :
    let globalUnit := fun (W : Scheme.{u})
      (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) ↦
        W.toRingedSpace.isUnit_of_isUnit_germ ⊤ (N : Γ(W, ⊤))
          (fun w _ ↦ by simpa only [map_natCast] using hW w)
    let line := fun (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (r : ℕ) ↦ Scheme.finiteEtaleTateTwist W N R hR r
    let single := fun (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (r : ℕ) ↦ (DerivedCategory.singleFunctor _ 0).obj (line R hR W r)
    let betaType := fun (W : Scheme.{u}) ↦
      ∀ r : ℕ, (purityScalarSheaf φ W).obj (line A hA W r) ≅ line B hB W r
    let betaMap := fun (W : Scheme.{u}) (β : betaType W) (r : ℕ) ↦
      purityScalarSingleMap φ W (line A hA W r) ≫
        (DerivedCategory.singleFunctor _ 0).map (β r).hom
    let rho := fun (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0)
      {S T : Scheme.{u}} (f : S ⟶ T)
      (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
      (hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s)) (r : ℕ) ↦
        singleFunctorPullbackMap f
          ((Scheme.finiteEtaleTwistPullbackData R N hN hR).c f
            (globalUnit T hT) (globalUnit S hS) (r : ℤ)).hom
    let tateTensor := fun (R : Type (u + 1)) [CommRing R] [Finite R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) (r s : ℕ) ↦
        finiteAffineTatePairing R N hN hR W hW r s
    let betaSquare := fun {S T : Scheme.{u}} (f : S ⟶ T)
      (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
      (hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
      (βT : betaType T) (βS : betaType S) ↦
      ∀ r : ℕ,
        L(upperStar (ModuleCat.{u + 1} B) f).map (betaMap T βT r) ≫
            rho B hB f hT hS r =
          (scalarPullbackIso φ f).hom.app (single A hA T r) ≫
            (scalarExtension φ S).map (rho A hA f hT hS r) ≫ betaMap S βS r
    let betaTensor := fun (W : Scheme.{u})
      (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) (β : betaType W) ↦
      ∀ r s : ℕ,
        (scalarExtension φ W).map (tateTensor A hA W hW r s) ≫ betaMap W β (r+s) =
          (ExceptionalCoefficients.tensorIso φ W).hom.app (single A hA W r, single A hA W s) ≫
            derivedTensorHom (ModuleCat.{u + 1} B) (betaMap W β r) (betaMap W β s) ≫
            tateTensor B hB W hW r s
    let gammaLaw := fun {S T : Scheme.{u}} (f : S ⟶ T) ↦
      ((scalarPullbackIso φ f).inv =
        ((mateEquiv
          (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
          (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars S.smallEtaleTopology φ))).symm
          (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)).natTrans) ∧
      (∀ (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
        (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
        (scalarPullbackIso φ f).hom.app (_root_.DerivedCategory.Q.obj P) ≫
            (scalarExtension φ S).map (scalarGeometricRepresentative A f P) ≫
            scalarExtensionRepresentative φ S
              (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
          L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ T P) ≫
            scalarGeometricRepresentative B f
              (((ProEtale.etaleSheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj P) ≫
            _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P)) ∧
      ScalarPullbackTensorLaw (scalarExtension φ T) (scalarExtension φ S)
        L(upperStar (ModuleCat.{u + 1} A) f) L(upperStar (ModuleCat.{u + 1} B) f)
        (scalarPullbackIso φ f) (ExceptionalCoefficients.tensorIso φ T)
        (ExceptionalCoefficients.tensorIso φ S)
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) f) ∧
      (∀ (K : DerivedCategoryModule A T) (n : ℤ),
        L(upperStar (ModuleCat.{u + 1} B) f).map
            ((FiniteSmoothPurity.scalarShiftIso φ T n).hom.app K) ≫
          (L(upperStar (ModuleCat.{u + 1} B) f).commShiftIso n).hom.app
            ((scalarExtension φ T).obj K) ≫
          ((scalarPullbackIso φ f).hom.app K)⟦n⟧' =
        (scalarPullbackIso φ f).hom.app (K⟦n⟧) ≫
          (scalarExtension φ S).map
            ((L(upperStar (ModuleCat.{u + 1} A) f).commShiftIso n).hom.app K) ≫
          (FiniteSmoothPurity.scalarShiftIso φ S n).hom.app
            (L(upperStar (ModuleCat.{u + 1} A) f).obj K))
    let muShift := fun (R : Type (u + 1)) [CommRing R]
      {S T : Scheme.{u}} (f : S ⟶ T) ↦
      ∀ (K M : DerivedCategoryModule R T) (a b : ℤ),
        L(upperStar (ModuleCat.{u + 1} R) f).map
            (derivedTensorShiftIso (ModuleCat.{u + 1} R) K M a b).hom ≫
          (L(upperStar (ModuleCat.{u + 1} R) f).commShiftIso (a+b)).hom.app _ ≫
          (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) f).app K).app M)⟦a+b⟧' =
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) f).app (K⟦a⟧)).app (M⟦b⟧) ≫
          derivedTensorHom (ModuleCat.{u + 1} R)
            ((L(upperStar (ModuleCat.{u + 1} R) f).commShiftIso a).hom.app K)
            ((L(upperStar (ModuleCat.{u + 1} R) f).commShiftIso b).hom.app M) ≫
          (derivedTensorShiftIso (ModuleCat.{u + 1} R)
            (L(upperStar (ModuleCat.{u + 1} R) f).obj K)
            (L(upperStar (ModuleCat.{u + 1} R) f).obj M) a b).hom
    let scalarTensorShift := fun (W : Scheme.{u}) ↦
      ∀ (K M : DerivedCategoryModule A W) (a b : ℤ),
        (scalarExtension φ W).map
            (derivedTensorShiftIso (ModuleCat.{u + 1} A) K M a b).hom ≫
          (FiniteSmoothPurity.scalarShiftIso φ W (a+b)).hom.app _ ≫
          ((ExceptionalCoefficients.tensorIso φ W).hom.app (K,M))⟦a+b⟧' =
        (ExceptionalCoefficients.tensorIso φ W).hom.app (K⟦a⟧, M⟦b⟧) ≫
          derivedTensorHom (ModuleCat.{u + 1} B)
            ((FiniteSmoothPurity.scalarShiftIso φ W a).hom.app K)
            ((FiniteSmoothPurity.scalarShiftIso φ W b).hom.app M) ≫
          (derivedTensorShiftIso (ModuleCat.{u + 1} B)
            ((scalarExtension φ W).obj K) ((scalarExtension φ W).obj M) a b).hom
    let gammaId := fun (W : Scheme.{u}) ↦ ∀ K : DerivedCategoryModule A W,
      (scalarPullbackIso φ (𝟙 W)).hom.app K ≫
          (scalarExtension φ W).map ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) W).hom.app K) =
        (leftDerivedUpperStarId (ModuleCat.{u + 1} B) W).hom.app ((scalarExtension φ W).obj K)
    let proetaleLaw := fun {S T : Scheme.{u}} (f : S ⟶ T) ↦
      ∀ {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
      [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
      (a : Λ ⟶ Λ') [IsMonHom a],
      ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).map
          (AlgebraicGeometry.ProEtale.coefficientMap a T) ≫
          AlgebraicGeometry.ProEtale.condensedPullbackHom Λ' f =
        AlgebraicGeometry.ProEtale.condensedPullbackHom Λ f ≫
          AlgebraicGeometry.ProEtale.coefficientMap a S) ∧
      (∀ N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (AlgebraicGeometry.ProEtale.condensedRingObj Λ' T),
        AlgebraicGeometry.ProEtale.CondensedRing.upperStarUnitHom Λ' f N ≫
          ((AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso a f).hom.app N).hom =
          AlgebraicGeometry.ProEtale.CondensedRing.upperStarUnitHom Λ f ((Mod.comap
            (AlgebraicGeometry.ProEtale.coefficientMap a T)).obj N)) ∧
      ∃ c : (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).obj
        (AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a T) ≅
        AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a S,
        AlgebraicGeometry.ProEtale.CondensedRing.upperStarUnitHom Λ f
          (AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a T) ≫ c.hom.hom =
          AlgebraicGeometry.ProEtale.condensedPullbackHom Λ' f ∧
      ∃ t : AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a T ⋙
        AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f ≅
        AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f ⋙
        AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a S,
        AlgebraicGeometry.ProEtale.CondensedRing.IsCondensedScalarBalancing a f t ∧
        (∀ t' : AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a T ⋙
          AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f ≅
          AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f ⋙
          AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a S,
          AlgebraicGeometry.ProEtale.CondensedRing.IsCondensedScalarBalancing a f t' → t' = t) ∧
        (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (AlgebraicGeometry.ProEtale.condensedRingObj Λ T),
          ∃ s : (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ' f).obj ((Mod.extendScalars
            (AlgebraicGeometry.ProEtale.coefficientMap a T)).obj M) ≅
              (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap a S)).obj
                ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).obj M),
            (Mod.comap (AlgebraicGeometry.ProEtale.coefficientMap a S)).map s.hom =
              (AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso a f).hom.app _ ≫
                (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).map
                  (AlgebraicGeometry.ProEtale.CondensedRing.balancingExtensionIso a T M).inv ≫
                  t.hom.app M ≫
                (AlgebraicGeometry.ProEtale.CondensedRing.balancingExtensionIso a S
                  ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).obj M)).hom) ∧
        ∃ C : (AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a T ⋙
          AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ) ≅
            (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f ⋙
              AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a S).mapHomologicalComplex
              (.up ℤ),
          (∀ (P : CochainComplex
              (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                (AlgebraicGeometry.ProEtale.condensedRingObj Λ T)) ℤ) (i : ℤ),
            (C.hom.app P).f i = t.hom.app (P.X i) ∧
              (C.inv.app P).f i = t.inv.app (P.X i)) ∧
          (∀ (P : CochainComplex
              (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                (AlgebraicGeometry.ProEtale.condensedRingObj Λ T)) ℤ) (i j : ℤ),
            (AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a T ⋙
              AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).map (P.d i j) ≫ t.hom.app (P.X
              j) =
              t.hom.app (P.X i) ≫ (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f ⋙
                AlgebraicGeometry.ProEtale.CondensedRing.balancingTensor a S).map (P.d i j)) ∧
          (∀ P : CochainComplex
              (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                (AlgebraicGeometry.ProEtale.condensedRingObj Λ T)) ℤ,
            ((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).mapHomologicalComplex (.up
              ℤ)).map
                (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
                  (AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a T) P).hom ≫
                    C.hom.app P =
              HomologicalComplex.mapBifunctorComparison
                  (Functor.OplaxMonoidal.δNatTrans
                    (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f)) (.up ℤ) P
                  ((HomologicalComplex.single _ (.up ℤ) 0).obj
                    (AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a T)) ≫
                HomologicalComplex.mapBifunctorMap
                  (𝟙 (((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ
                    f).mapHomologicalComplex (.up ℤ)).obj P))
                  (((HomologicalComplex.singleMapHomologicalComplex
                      (AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f) (.up ℤ) 0).hom.app
                        (AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a T)) ≫
                    (HomologicalComplex.single _ (.up ℤ) 0).map c.hom)
                  (curriedTensor _) (.up ℤ) ≫
                (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
                  (AlgebraicGeometry.ProEtale.CondensedRing.balancingCoefficient a S)
                  (((AlgebraicGeometry.ProEtale.CondensedRing.upperStar Λ f).mapHomologicalComplex
                    (.up ℤ)).obj P)).hom)
    gammaLaw u ∧ gammaLaw v ∧ gammaLaw (u ≫ v) ∧
    gammaId X ∧ gammaId Y ∧ gammaId Z ∧
    muShift A u ∧ muShift A v ∧ muShift A (u ≫ v) ∧
    muShift B u ∧ muShift B v ∧ muShift B (u ≫ v) ∧
    scalarTensorShift X ∧ scalarTensorShift Y ∧ scalarTensorShift Z ∧
    (∀ K : DerivedCategoryModule A Z,
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) u v).hom.app
          ((scalarExtension φ Z).obj K) ≫
        L(upperStar (ModuleCat.{u + 1} B) u).map ((scalarPullbackIso φ v).hom.app K) ≫
        (scalarPullbackIso φ u).hom.app (L(upperStar (ModuleCat.{u + 1} A) v).obj K) =
      (scalarPullbackIso φ (u ≫ v)).hom.app K ≫
        (scalarExtension φ X).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u v).hom.app K)) ∧
    (∃ (βX : betaType X) (βY : betaType Y) (βZ : betaType Z),
      IsFiniteTateScalarBalancing φ N hA hB X βX ∧
      IsFiniteTateScalarBalancing φ N hA hB Y βY ∧
      IsFiniteTateScalarBalancing φ N hA hB Z βZ ∧
      (∀ r : ℕ, IsIso (betaMap X βX r)) ∧
      (∀ r : ℕ, IsIso (betaMap Y βY r)) ∧
      (∀ r : ℕ, IsIso (betaMap Z βZ r)) ∧
      betaSquare u hY hX βY βX ∧ betaSquare v hZ hY βZ βY ∧
      betaSquare (u ≫ v) hZ hX βZ βX ∧
      betaTensor X hX βX ∧ betaTensor Y hY βY ∧ betaTensor Z hZ βZ ∧
      (∀ r : ℕ,
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) u v).hom.app
            ((scalarExtension φ Z).obj (single A hA Z r)) ≫
          L(upperStar (ModuleCat.{u + 1} B) u).map
            (L(upperStar (ModuleCat.{u + 1} B) v).map (betaMap Z βZ r) ≫ rho B hB v hZ hY r) ≫
          rho B hB u hY hX r =
        (scalarPullbackIso φ (u ≫ v)).hom.app (single A hA Z r) ≫
          (scalarExtension φ X).map (rho A hA (u ≫ v) hZ hX r) ≫ betaMap X βX r)) ∧
    proetaleLaw u ∧ proetaleLaw v ∧ proetaleLaw (u ≫ v) := by
  have hγ := finiteAffineRightScalarCompositionCoherenceGammaPackage φ u v
  have hu := hγ.1
  have hv := hγ.2.1
  have huv := hγ.2.2.1
  have hc := hγ.2.2.2
  refine assembleCoherence
    (assembleGammaFields (scalarPullbackIso_inv_mate_restriction φ u).1 ?_
      (etaleScalarPullback_tensor φ u) hu)
    (assembleGammaFields (scalarPullbackIso_inv_mate_restriction φ v).1 ?_
      (etaleScalarPullback_tensor φ v) hv)
    (assembleGammaFields (scalarPullbackIso_inv_mate_restriction φ (u ≫ v)).1 ?_
      (etaleScalarPullback_tensor φ (u ≫ v)) huv)
    (etaleScalarPullbackIdentityNormalization φ X).2.2
    (etaleScalarPullbackIdentityNormalization φ Y).2.2
    (etaleScalarPullbackIdentityNormalization φ Z).2.2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc ?_ ?_ ?_ ?_
  · intro P hP _
    exact (scalarPullbackIso_existsUnique φ u).choose_spec.1 P hP
  · intro P hP _
    exact (scalarPullbackIso_existsUnique φ v).choose_spec.1 P hP
  · intro P hP _
    exact (scalarPullbackIso_existsUnique φ (u ≫ v)).choose_spec.1 P hP
  · intro K M a b
    simpa only [derivedTensorHom, Category.assoc] using
      leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
        (ModuleCat.{u + 1} A) u K M a b
  · intro K M a b
    simpa only [derivedTensorHom, Category.assoc] using
      leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
        (ModuleCat.{u + 1} A) v K M a b
  · intro K M a b
    simpa only [derivedTensorHom, Category.assoc] using
      leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
        (ModuleCat.{u + 1} A) (u ≫ v) K M a b
  · intro K M a b
    simpa only [derivedTensorHom, Category.assoc] using
      leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
        (ModuleCat.{u + 1} B) u K M a b
  · intro K M a b
    simpa only [derivedTensorHom, Category.assoc] using
      leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
        (ModuleCat.{u + 1} B) v K M a b
  · intro K M a b
    simpa only [derivedTensorHom, Category.assoc] using
      leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
        (ModuleCat.{u + 1} B) (u ≫ v) K M a b
  · intro K M a b
    exact (normalizedScalarTensorShiftCoherence φ X K M a b (𝟙_ _) (𝟙_ _) 0).1
  · intro K M a b
    exact (normalizedScalarTensorShiftCoherence φ Y K M a b (𝟙_ _) (𝟙_ _) 0).1
  · intro K M a b
    exact (normalizedScalarTensorShiftCoherence φ Z K M a b (𝟙_ _) (𝟙_ _) 0).1
  · let βX := (finite_tate_scalar_source_normalization φ N hN hA hB X hX).2.choose
    have hβX :=
      (finite_tate_scalar_source_normalization φ N hN hA hB X hX).2.choose_spec.1
    let βY := (finite_tate_scalar_source_normalization φ N hN hA hB Y hY).2.choose
    have hβY :=
      (finite_tate_scalar_source_normalization φ N hN hA hB Y hY).2.choose_spec.1
    let βZ := (finite_tate_scalar_source_normalization φ N hN hA hB Z hZ).2.choose
    have hβZ :=
      (finite_tate_scalar_source_normalization φ N hN hA hB Z hZ).2.choose_spec.1
    have hsingle (W : Scheme.{u})
        (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) (r : ℕ) :
        IsIso (purityScalarSingleMap φ W (Scheme.finiteEtaleTateTwist W N A hA r)) := by
      have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateTwist W N A hA r) :=
        (ObjectProperty.flat_iff_preservesFiniteLimits _).2
          (Scheme.finite_etale_torsion_twist_line W N hN hW A hA r).2.2.1
      exact ((finite_tate_scalar_source_normalization φ N hN hA hB W hW).1 _ hflat.2).2
    refine ⟨βX, βY, βZ, hβX.1, hβY.1, hβZ.1, ?_, ?_, ?_, ?_⟩
    · intro r
      have := hsingle X hX r
      infer_instance
    · intro r
      have := hsingle Y hY r
      infer_instance
    · intro r
      have := hsingle Z hZ r
      infer_instance
    · exact finiteAffineRightScalarCompositionCoherenceTatePackage
        φ N hN hA hB hX hY hZ u v βX βY βZ hβX.1 hβY.1 hβZ.1
  · intro Λ Λ' _ _ _ _ a _
    exact AlgebraicGeometry.ProEtale.CondensedRing.condensedScalarBalancingChain a u
  · intro Λ Λ' _ _ _ _ a _
    exact AlgebraicGeometry.ProEtale.CondensedRing.condensedScalarBalancingChain a v
  · intro Λ Λ' _ _ _ _ a _
    exact AlgebraicGeometry.ProEtale.CondensedRing.condensedScalarBalancingChain a (u ≫ v)

end AlgebraicGeometry.Etale
