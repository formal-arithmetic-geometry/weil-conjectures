module

public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.ProEtaleOrderedIntegration
public import Sheaf.Paper.FiniteSiteTensorProjection
public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
public import Sheaf.Paper.AffineDiagonalTateCoordinates
public import Sheaf.Paper.TensorTraceTranspose

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import Sheaf.AlgebraicGeometry.ProEtaleFiniteCDComparison
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.Mathlib.CategoryTheory.NatIso

/-! # Diagonal affine trace and finite-level site comparison

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
cor-pur-dualizing-object-purity.md, Kummer normalization sentence
(blueprint: def-pur-diagonal-affine-trace-coordinates).

The auxiliary arrows only put the recorded ordered Kummer integrations in the
source coordinates of the actual diagonal purity map. The pro-etale integration
uses the independently constructed pro-etale coordinate counits. Every ordinary
presentation and every positive annihilating exponent is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
open AlgebraicGeometry.ProEtale.VectorIntegrationSite


/-- The coordinate affine projection has its stated smooth dimension.
Source: polynomial coordinate charts in the affine model
(blueprint: def-pur-diagonal-affine-trace-coordinates).
Proof: the zero tower is the identity. Each successor is an affine-line projection,
smooth of relative dimension one, and dimensions add under composition. -/
theorem projectionSmooth (S : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (affineTraceProjection S d) := by
  induction d with
  | zero =>
    change SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ d ih =>
    let := ih
    have hline : SmoothOfRelativeDimension 1
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) := by
      simpa using (AffineSpace.smoothOfRelativeDimension_over
        PUnit.{u + 1} (affineTraceTower S d))
    let := hline
    simpa only [affineTraceProjection, Nat.add_comm] using
      (smoothOfRelativeDimension_comp
        (f := AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d) (n := 1) (m := d))


/-- The shifted ordered root coefficient is bounded below.
Source: the finite Tate line in the affine model
(blueprint: def-pur-diagonal-affine-trace-coordinates).
Proof: a finite root line is locally free in degree zero; each shifted factor has
cohomology in degree -2. Its d-fold tensor is concentrated in degree -2d. -/
theorem coefficientPlus (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (_hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (_hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    DerivedCategory.TStructure.t.plus (Etale.affineLinearBaseCoefficient A N hA S d) := by
  let := Sheaf.monoidalCategory S.smallEtaleTopology (ModuleCat.{u + 1} A)
  let t := Scheme.finiteEtaleTwistPullbackData A N _hN hA
  let L := Scheme.finiteEtaleTateSheaf A N S hA 1
  have hf : ObjectProperty.flat L := by
    exact ObjectProperty.flat_of_tensorIso (t.p S _hS 1 (-1))
  let M := (DerivedCategory.singleFunctor _ 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf
  induction d with
  | zero =>
    exact ⟨0, inferInstanceAs
      (DerivedCategory.TStructure.t.IsGE (Etale.ordinaryFiniteUnit A S) 0)⟩
  | succ d ih =>
    obtain ⟨a, ha⟩ := ih
    let K := Etale.affineLinearBaseCoefficient A N hA S d
    have : K.IsGE a := ha
    have : (M ⊗ K).IsGE a := by
      simpa only [zero_add] using DerivedCategory.isGE_tensor_of_torAmplitudeIn ht K a
    let e : Etale.affineLinearBaseCoefficient A N hA S (d + 1) ≅ (M ⊗ K)⟦(2 : ℤ)⟧ :=
      (Etale.derivedTensorRightShiftIso (ModuleCat.{u + 1} A) M 2).app K ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso
          (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) S).app K).app M)
    apply DerivedCategory.TStructure.t.plus.prop_of_iso e.symm
    exact ⟨a - 2, DerivedCategory.TStructure.t.isGE_shift _ a 2 _ (by omega)⟩


/-- Positive powers of the invertible prime remain invertible on the base.
Source: the prime-to-characteristic coefficient convention
(blueprint: def-pur-diagonal-affine-trace-coordinates).
Proof: cast ell^(r+1) as the (r+1)-st power of cast ell and apply IsUnit.pow. -/
theorem powerUnit (l : ℕ) (S : Scheme.{u}) (_hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ) :
    IsUnit ((l ^ (r + 1) : ℕ) : Γ(S, ⊤)) := by
  simpa only [Nat.cast_pow] using _hS.pow (r + 1)


/-- The ordinary pulled-back coefficient tensor the shifted ordered Tate line.
Source: the common tensor source in the integration square
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def OrdinarySource (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) :=
  ((Etale.ordinaryFiniteTensor A (affineTraceTower S d)).obj
    ((Etale.ordinaryFinitePullback A (affineTraceProjection S d)).obj K)).obj
      (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d)

section Ordinary
variable (A : Type (u + 1)) [CommRing A] [Finite A]
  (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
  (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)


/-- The tensor/normalized-root identification of the ordered right coefficient.
Source: the affine integration source identification
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def coefficientIso :
    (Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S) ≅
      Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d :=
  Etale.affineLinearCoefficientDescent A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) S hS d ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) (affineTraceProjection S d) hS d


/-- Canonical source transport to the ordered left/right tower; no trace occurs here.
Source: the compact-support and Tate identifications of the affine model
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def ordinarySourceIso :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d) ≅
    (Etale.affineTraceLeft A S d).obj
      ((Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S)) :=
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).mapIso (coefficientIso A N hN hA S hS d).symm ≪≫
    (Etale.affineLinearCompactComparison N hN A hA S hS d).symm


/-- Ordered restriction of the normalized projective-line traces on the ordinary site.
Source: t_d^e in the affine-model statement
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def ordinaryTrace :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d) ⟶
      Etale.ordinaryFiniteUnit A S :=
  (ordinarySourceIso A N hN hA S hS d).hom ≫
    Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
      (fun T _ hT ↦ Etale.projectiveLineTraceDatum N hN A hA T hT) S hS d


/-- The ordinary coefficient-first inverse projection, tensor trace and right unitor.
Source: a^e_{d,K} in the affine-model statement
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def ordinaryIntegration (K : Etale.DerivedCategoryModule A S) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj
        (((Etale.ordinaryFiniteTensor A (affineTraceTower S d)).obj
          ((Etale.ordinaryFinitePullback A (affineTraceProjection S d)).obj K)).obj
          (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d)) ⟶ K :=
  Etale.tensorTraceProjection A (affineTraceProjection S d)
    (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d) K
      (ordinaryTrace A N hN hA S hS d ≫ (smoothPurityUnitIso A S).hom)


/-- The exceptional adjoint transpose of the actual ordinary integration arrow.
Source: eta^e_{d,K} in the affine-model statement
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def ordinaryTranspose (K : Etale.DerivedCategoryModule A S) :
    (((Etale.ordinaryFiniteTensor A (affineTraceTower S d)).obj
      ((Etale.ordinaryFinitePullback A (affineTraceProjection S d)).obj K)).obj
      (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d)) ⟶
    (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).obj K :=
  (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (affineTraceProjection S d)).homEquiv _ K
      (ordinaryIntegration A N hN hA S hS d K)
end Ordinary


/-- Compact support of the compared ordered Tate line.
Source: the source of t_d^p
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def TateSupport (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :=
  (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (HasCompactification.compactification (affineTraceProjection S d))).obj
      ((comparison A (affineTraceTower S d)).obj
        (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d))


/-- Compact support of the ordinary-source tensor realization.
Source: the source of a_d^p
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def IntegrationSupport (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) :=
  (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (HasCompactification.compactification (affineTraceProjection S d))).obj
      ((comparison A (affineTraceTower S d)).obj
        (((Etale.ordinaryFiniteTensor A (affineTraceTower S d)).obj
          ((Etale.ordinaryFinitePullback A (affineTraceProjection S d)).obj K)).obj
            (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d)))


/-- The inverse coefficient-first projection isomorphism type.
Source: the inverse projection formula
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def ProjectionIsoType (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) :=
  IntegrationSupport A N hA S d K ≅
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).obj
      ((comparison A S).obj K)).obj (TateSupport A N hA S d)


/-- Coefficient and support transport to the ordered counit's source.
Source: Tate descent and proper/open comparison
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def counitSource (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    TateSupport A N hA S d ⟶ (comparison A S).obj
      ((Etale.affineTraceLeft A S d).obj
        ((Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S))) :=
  (ProEtale.compactSupportSiteComparison A
    (HasCompactification.compactification (affineTraceProjection S d))).hom.app
      ⟨_, coefficientPlus A N hN hA (affineTraceTower S d)
        (affineTraceInvertible N S hS d) d⟩ ≫
    (comparison A S).map (ordinarySourceIso A N hN hA S hS d).hom


/-- Inverse projection followed by tensor trace and unitor, at generic coefficients.
Source: the coefficient-first integration composite
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def integrateWithTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) (e : ProjectionIsoType A N hA S d K)
    (t : TateSupport A N hA S d ⟶ unit A S) :
    IntegrationSupport A N hA S d K ⟶ (comparison A S).obj K :=
  proTensorIntegrate A S K _ _ e t


/-- The inverse of the desired isomorphism is the recorded coefficient-first map.
Source: normalization of the inverse projection
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def ProjectionIsoSpec (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (K : Etale.DerivedCategoryModule A S) (e : ProjectionIsoType A N hA S d K) : Prop :=
  HEq e.inv (comparedModuleProjection A
    (HasCompactification.compactification (affineTraceProjection S d))
    (Etale.affineLinearBaseCoefficient A N hA (affineTraceTower S d) d) K)

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true



private theorem proper_module_cohomological_bound
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] [CompactSpace Y] :
    ∃ d : ℕ, ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      d < q → IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerived q).obj M) := by
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound g
  refine ⟨2 * d, fun M q hq ↦ ?_⟩
  let U := sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M
  have hF : Scheme.IsTorsionAbelianSheaf F := by
    apply (Scheme.isTorsionAbelianSheaf_characterizations F).1.mpr
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro V
    exact IsAddTorsion.module_of_finite A (M.obj.obj V)
  have hz := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    g d hd F hF (q : ℤ) (by exact_mod_cast hq)
  obtain ⟨e⟩ := Etale.nonempty_higherDirectImage_forget_iso A g (q : ℤ) M
  have hzero := hz.of_iso e
  have hz' : IsZero (Etale.higherDirectImage A g (q : ℤ) M) := by
    rw [IsZero.iff_id_eq_zero]
    apply U.map_injective
    exact hzero.eq_of_src _ _
  exact hz'.of_iso
    ((Etale.lowerStar (ModuleCat.{u + 1} A) g)
      |>.homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm



/-- Formal projection transport, before specializing the coefficient category. Keeping
its functors abstract avoids expanding module-category tensor constructions in the
categorical mate calculation. -/
private theorem comparison_projection_transport
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [Etale.UpperStarPreservesFlat B] [ProEtale.UpperStarPreservesFlat B]
    [∀ T : Scheme.{u}, (ProEtale.comparisonUpperStar B T).PreservesFlat]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hβ : ∀ L : DerivedCategory (Sheaf X.smallEtaleTopology B),
      IsIso ((mateEquiv (Etale.derivedUpperStarLowerStarAdjunction B g)
        (ProEtale.derivedUpperStarLowerStarAdjunction B g)
        (ProEtale.leftDerivedComparisonUpperStarCompUpperStarIso B g).hom).app L))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    [hpf : IsIso (((Etale.rightDerivedLowerStarProjectionMap B g).app M).app K)] :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap B g).app
      ((ProEtale.comparisonUpperStar B X).leftDerivedFunctor.obj M)).app
      ((ProEtale.comparisonUpperStar B Y).leftDerivedFunctor.obj K)) := by
  dsimp only [Etale.rightDerivedLowerStarProjectionMap] at hpf
  have : IsIso ((((Etale.derivedUpperStarLowerStarAdjunction B g).rightAdjointProjectionMap
      (Etale.leftDerivedUpperStarTensorComparison B g)).app M).app K) := hpf
  have := hβ M
  have := hβ (((Etale.derivedTensor B X).obj M).obj
    ((Etale.upperStar B g).leftDerivedFunctor.obj K))
  exact Adjunction.isIso_rightAdjointProjectionMap_of_mateEquiv
    (Etale.derivedUpperStarLowerStarAdjunction B g)
    (ProEtale.derivedUpperStarLowerStarAdjunction B g)
    (ProEtale.comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso B g) M K



private theorem proper_projection_at_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g] [CompactSpace Y]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) g).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctor.obj M)).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctor.obj K)) := by
  have hcd := proper_module_cohomological_bound A g
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A g
  exact comparison_projection_transport (ModuleCat.{u + 1} A) g
    (fun L ↦ ProEtale.isIso_comparisonMate_of_finiteCohomologicalDimension A g hcd L) M K



private theorem compact_projection_transport
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [ProEtale.UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B))
    [hpf : IsIso (((ProEtale.rightDerivedLowerStarProjectionMap B c.g).app
      ((ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory.obj W)).app K)] :
    IsIso (((ProEtale.projectionMapOfCompactification B c).app W).app K) := by
  rw [ProEtale.projectionMapOfCompactification_app_app]
  refine IsIso.comp_isIso' hpf ?_
  refine IsIso.comp_isIso' ?_ ?_
  · exact ((ProEtale.lowerStar B c.g).rightDerivedFunctor.mapIso
      (((ProEtale.derivedOpenImmersionLowerShriekProjectionIso B c.i).app W).app
        ((ProEtale.upperStar B c.g).leftDerivedFunctor.obj K)).symm).isIso_hom
  · exact ((ProEtale.lowerStar B c.g).rightDerivedFunctor.mapIso
      ((ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory.mapIso
        (((ProEtale.derivedTensor B X).obj W).mapIso
          ((ProEtale.leftDerivedUpperStarCompactificationIso B c).app K)))).isIso_hom


private theorem coefficient_first_projection_transport
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [ProEtale.UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B))
    [hpf : IsIso (((ProEtale.projectionMapOfCompactification B c).app W).app K)] :
    IsIso (projection B c W K) := by
  unfold projection
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' hpf ?_)
  · exact (((symmetry B Y).app K).app _).isIso_hom
  · exact ((ProEtale.rightDerivedLowerShriekOfCompactification B c).mapIso
      (((symmetry B X).app W).app _)).isIso_hom



private theorem compact_projection_at_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) [CompactSpace Y]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      ((comparison A X).obj W)).app ((comparison A Y).obj K)) := by
  let M := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj W
  let eM : (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
      ((comparison A X).obj W) ≅
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).leftDerivedFunctor.obj M :=
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _).app W ≪≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) c.Z)
          |>.leftDerivedFunctorIsoMapDerivedCategory.app M).symm
  let eK : (comparison A Y).obj K ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctor.obj K :=
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      |>.leftDerivedFunctorIsoMapDerivedCategory.app K).symm
  have := proper_projection_at_comparison A c.g M K
  have hp := NatTrans.isIso_app_app_of_iso
    (ProEtale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) c.g) eM.symm eK.symm
  exact compact_projection_transport (ModuleCat.{u + 1} A) c
    ((comparison A X).obj W) ((comparison A Y).obj K)



private theorem compared_projection_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) [CompactSpace Y]
    (W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (comparedModuleProjection A c W K) := by
  have := compact_projection_at_comparison A c W K
  have := coefficient_first_projection_transport (ModuleCat.{u + 1} A) c
    ((comparison A X).obj W) ((comparison A Y).obj K)
  unfold comparedModuleProjection moduleProjection
  infer_instance

end

section Finite
variable (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (S : Scheme.{u}) [IsNoetherian S]
  (hS : IsUnit (C.l : Γ(S, ⊤))) (r : ℕ)
  (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0) (d : ℕ)


/-- The pro-etale trace from the actual ordered pro-etale counits. The preceding
maps contain only canonical compact-support and coefficient comparisons.
Source: t_d^p in the affine-model statement
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def proTrace :
    TateSupport (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1)) hA S d ⟶
      unit (Scheme.finiteTateCoefficient C.l E n) S :=
  counitSource (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1))
    (pow_pos C.prime.out.pos _) hA S
    (powerUnit C.l S hS r) d ≫
    orderedIntegration C.l E n S hS r hA d


/-- The inverse projection is uniquely specified by the actual projection map.
Source: the inverse projection in the affine-model integration formula
(blueprint: def-pur-diagonal-affine-trace-coordinates).
Proof: the proper part of the compactification has a uniform finite fibre-dimension
bound, hence a finite étale cohomological-dimension bound for finite coefficients.
Lower truncations extend the canonical comparison mate to unbounded complexes.
Transport the finite étale projection formula along this mate and extension by zero.
Tensor symmetry and the site source comparison are isomorphisms. Take the inverse
of this actual projection map; an isomorphism is uniquely determined by its inverse. -/
theorem projectionIso_existsUnique
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (_hK : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S K) :
    ∃! e : ProjectionIsoType (Scheme.finiteTateCoefficient C.l E n)
      (C.l ^ (r + 1)) hA S d K, ProjectionIsoSpec (Scheme.finiteTateCoefficient C.l E n)
        (C.l ^ (r + 1)) hA S d K e := by
  let A := Scheme.finiteTateCoefficient C.l E n
  let c := HasCompactification.compactification (affineTraceProjection S d)
  let W := Etale.affineLinearBaseCoefficient A (C.l ^ (r + 1)) hA
    (affineTraceTower S d) d
  let p := comparedModuleProjection A c W K
  have : IsIso p := compared_projection_isIso A c W K
  let e : ProjectionIsoType A (C.l ^ (r + 1)) hA S d K := (asIso p).symm
  refine ⟨e, ?_, ?_⟩
  · exact HEq.rfl
  · intro e' he'
    have he : e'.inv = e.inv := eq_of_heq he'
    exact Iso.ext ((Iso.inv_eq_inv e' e).mp he)


/-- The unique inverse of the actual coefficient-first projection.
Its defining theorem determines all of its data.
Source: the inverse projection in the affine-model integration formula
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def projectionIso
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (hK : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S K) :
    ProjectionIsoType (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1)) hA S d K :=
  uniqueValue (ProjectionIsoSpec (Scheme.finiteTateCoefficient C.l E n)
        (C.l ^ (r + 1)) hA S d K)
    (projectionIso_existsUnique F C E n S r hA d K hK)


/-- Coefficient-first pro-etale projection followed by tensor with the actual trace.
Source: a^p_{d,K} in ordinary-comparison source coordinates
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def proIntegration
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (hK : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S K) :
    IntegrationSupport (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1)) hA S d K ⟶
      (comparison (Scheme.finiteTateCoefficient C.l E n) S).obj K :=
  integrateWithTrace (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1)) hA S d K
    (projectionIso F C E n S r hA d K hK) (proTrace F C E n S hS r hA d)


/-- The canonical comparison of any annihilating exponent with the diagonal exponent.
Source: root-power transition and the coefficient conventions
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def exponentIso (T : Scheme.{u}) (hT : IsUnit (C.l : Γ(T, ⊤))) :
    Etale.affineLinearBaseCoefficient _ (C.l ^ (r + 1)) hA T d ≅
      (projectionSetting F C E n).diagonalTwistEtale T d :=
  if h : n ≤ r then
    baseExponentComparison C.l E n T hT n r h
      (projectionSetting F C E n).diagonalExponent_annihilates hA d
  else
    (baseExponentComparison C.l E n T hT r n (Nat.le_of_lt (Nat.lt_of_not_ge h))
      hA (projectionSetting F C E n).diagonalExponent_annihilates d).symm
end Finite


/-- Tensor, pullback and shift source coordinates at an arbitrary fixed finite datum.
Source: the specified Tate and source comparisons
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def sourceCoordinates (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) (d : ℕ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S)
      (ModuleCat.{u + 1} P.Coefficient)))
    (Ke : Etale.DerivedCategoryModule P.Coefficient S)
    (eK : (comparison P.Coefficient S).obj Ke ≅ K)
    (L : Etale.DerivedCategoryModule P.Coefficient (affineTraceTower S d))
    (eL : L ≅ P.diagonalTwistEtale (affineTraceTower S d) d) :
    (((smoothPurityTensor P.Coefficient (affineTraceTower S d)).obj
      ((P.smoothPurityPullback (affineTraceProjection S d)).obj K)).obj
      ((P.diagonalTwist (affineTraceTower S d) d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧ ≅
    (comparison P.Coefficient (affineTraceTower S d)).obj
      (((Etale.ordinaryFiniteTensor P.Coefficient (affineTraceTower S d)).obj
        ((Etale.ordinaryFinitePullback P.Coefficient
          (affineTraceProjection S d)).obj Ke)).obj L) :=
  P.smoothPurityReassociation (affineTraceTower S d) d
      ((P.smoothPurityPullback (affineTraceProjection S d)).obj K) ≪≫
    ((smoothPurityTensor P.Coefficient (affineTraceTower S d)).mapIso
      (P.smoothPurityPullbackComparison (affineTraceProjection S d) K Ke eK)).app
        (P.diagonalTwist (affineTraceTower S d) d) ≪≫
    ((smoothPurityTensor P.Coefficient (affineTraceTower S d)).obj
      ((comparison P.Coefficient (affineTraceTower S d)).obj
        ((Etale.ordinaryFinitePullback P.Coefficient
          (affineTraceProjection S d)).obj Ke))).mapIso
            ((comparison P.Coefficient (affineTraceTower S d)).mapIso eL.symm) ≪≫
    (smoothPurityComparisonTensor P.Coefficient (affineTraceTower S d)
      ((Etale.ordinaryFinitePullback P.Coefficient
        (affineTraceProjection S d)).obj Ke) L).symm



/-- Endpoint-retaining type of the intrinsic purity and coefficient-valued trace.
Source: gamma and s on the original coefficient object
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def MapPair (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (K : Scheme.proEtaleDerivedCategory S P.Ring) (d : ℕ) :=
  let hft : LocallyOfFiniteType aS := inferInstance
  let hqc : QuasiCompact aS := inferInstance
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : S.Over (Spec (.of P.field.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of P.field.k)) := hft
  letI : QuasiCompact (S ↘ Spec (.of P.field.k)) := hqc
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    @locallyOfFiniteType_comp _ _ _ f aS
      (affineTraceProjection_locallyOfFiniteType S d) hft
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  (Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N) ×
    (Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K)


/-- Equality of the two specified morphisms, retaining their computed endpoints.
Source: the two map equalities of the affine comparison
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def SameMaps (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (K : Scheme.proEtaleDerivedCategory S P.Ring) (d : ℕ)
    (lhs rhs : MapPair P S aS K d) : Prop :=
  HEq lhs.1.2.2 rhs.1.2.2 ∧ HEq lhs.2.2 rhs.2.2


/-- The specified ordinary exceptional transpose and pro-etale integration,
transported through intrinsic realization. The arguments are supplied by the
canonical constructions below, and the comparison maps themselves are fixed here.
Source: counit-preserving exceptional and compact-support comparison
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
@[irreducible]
def transportCoordinates (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
    (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsNoetherian S]
    (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
    (hSN : IsUnit (N : Γ(S, ⊤)))
    (K : Scheme.proEtaleDerivedCategory S P.Ring)
    (Ke : Etale.DerivedCategoryModule P.Coefficient S)
    (eK : (comparison P.Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S P.Ring).inverse.obj K) (d : ℕ)
    (eL : Etale.affineLinearBaseCoefficient P.Coefficient N hA (affineTraceTower S d) d ≅
      P.diagonalTwistEtale (affineTraceTower S d) d)
    (integration : IntegrationSupport P.Coefficient N hA S d Ke ⟶
      (comparison P.Coefficient S).obj Ke) : MapPair P S aS K d :=
  let hft : LocallyOfFiniteType aS := inferInstance
  let hqc : QuasiCompact aS := inferInstance
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : IsNoetherian X := affineTraceNoetherian S d
  letI : S.Over (Spec (.of P.field.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of P.field.k)) := hft
  letI : QuasiCompact (S ↘ Spec (.of P.field.k)) := hqc
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    @locallyOfFiniteType_comp _ _ _ f aS
      (affineTraceProjection_locallyOfFiniteType S d) hft
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let e := sourceCoordinates P S d
    ((Scheme.sfIntrinsicDerivedEquivalence S P.Ring).inverse.obj K) Ke eK _ eL
  let ES := Scheme.sfIntrinsicDerivedEquivalence S P.Ring
  let EX := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let η := e.hom ≫
    (comparison P.Coefficient X).map
      (ordinaryTranspose P.Coefficient N hN hA S hSN d Ke) ≫
    ProEtale.boundedSiteRho P.Coefficient
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f) Ke ≫
    (P.smoothPurityExceptionalOver f aS).map eK.hom
  let a := (P.smoothCompactSupport f).map (EX.functor.map e.hom) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification f)).hom.app _ ≫
    ES.functor.map integration ≫
    ES.functor.map eK.hom ≫ ES.counitIso.hom.app K
  ((⟨_, _, EX.functor.map η⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N),
    (⟨_, a⟩ :
      Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K))


/-- The proper-mate/open-extension compact-support comparison on the tensor source.
Source: beta and the displayed ordinary/pro-etale integration square
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def IntegrationSiteSquare (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (K : Etale.DerivedCategoryModule A S)
    (hPlus : DerivedCategory.TStructure.t.plus (OrdinarySource A N hA S d K))
    (integration : IntegrationSupport A N hA S d K ⟶ (comparison A S).obj K) : Prop :=
  (ProEtale.compactSupportSiteComparison A
    (HasCompactification.compactification (affineTraceProjection S d))).inv.app
      ⟨_, hPlus⟩ ≫ integration =
    (comparison A S).map (ordinaryIntegration A N hN hA S hS d K)


/-- The integration arrow type in the purity datum's fixed scalar presentation.
Source: coefficient-source identification for a_d^p
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def IntegrationInput (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) [IsNoetherian S]
    (N : ℕ) (hA : (N : P.Coefficient) = 0) (d : ℕ)
    (K : Etale.DerivedCategoryModule P.Coefficient S) :=
  IntegrationSupport P.Coefficient N hA S d K ⟶ (comparison P.Coefficient S).obj K



/-- Projective-line normalization in the published finite coefficient coordinates.
Source: t_q^p h_q^p = 1
(blueprint: def-pur-diagonal-affine-trace-coordinates). -/
def ProjectiveNormalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  projectiveH l E n S hS (infinityCartier S) r hA ≫
    projectiveTrace l E n S hS (infinityCartier S) r hA =
      𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)

end WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace

