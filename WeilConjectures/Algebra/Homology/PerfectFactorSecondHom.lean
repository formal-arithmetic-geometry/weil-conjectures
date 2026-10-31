/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
public import WeilConjectures.Algebra.Homology.RingedSliceEvaluationModels
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.Algebra.Homology.RingedSliceEvaluationTranspose
import WeilConjectures.Algebra.Homology.RingedSliceTensorConstraints
import WeilConjectures.Algebra.Homology.RingedInternalHomCovariantExact
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-! # A perfect tensor factor in the second argument of derived Hom

Source: latest blueprint, lem-fix-operation-reduction.proof.md, paragraph 2;
Stacks Project, sites-cohomology.tex, Tags 08JD, 08JJ, 08JB and 08JC
(blueprint: lem-fix-perfect-factor-second-hom).
The exchange is defined by tensoring evaluation and transposing, including its symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe a b c v r w w'
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Transpose of evaluation tensored with the identity of the last factor.
The right-tensor adjunction is used after moving K past the last factor.
Symmetry identifies this with the left-tensor evaluation pairing in the node.
Source: Stacks 08JD, 08JJ; latest blueprint, operation reduction, paragraph 2
(blueprint: lem-fix-perfect-factor-second-hom). -/
def perfectFactorSecondHomMap
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H)
    (σ : ∀ X Y : D, S.tensor.obj (X, Y) ≅ S.tensor.obj (Y, X))
    (K L Q : D) :
    S.tensor.obj (H.obj (op K, L), Q) ⟶ H.obj (op K, S.tensor.obj (L, Q)) :=
  S.transpose (S.tensor.obj (H.obj (op K, L), Q)) K (S.tensor.obj (L, Q))
    ((S.monoidal.associator (H.obj (op K, L)) Q K).hom ≫
      S.tensor.map (Prod.mkHom (𝟙 _) (σ Q K).hom) ≫
      (S.monoidal.associator (H.obj (op K, L)) K Q).inv ≫
      S.tensor.map (Prod.mkHom (S.evaluation K L) (𝟙 Q)))

private theorem factorTranspose_left
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T T' P Q : D} (f : T' ⟶ T)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T' P Q (S.tensor.map (f, 𝟙 P) ≫ g) =
      f ≫ S.transpose T P Q g := by
  let := S.monoidal
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor]
  rw [tensorHom_id]
  exact (S.adjunction P).homEquiv_naturality_left f g

private theorem factorTranspose_target
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P : D) {Q Q' : D} (f : Q ⟶ Q')
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P Q' (g ≫ f) =
      S.transpose T P Q g ≫ H.map (𝟙 (op P), f) :=
  (S.adjunction P).homEquiv_naturality_right g f

private theorem factorRestriction
    {D : Type a} [Category.{b} D] {E : Type c} [Category.{v} E]
    {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} {F : D ⥤ E}
    (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
    {B : Prop} (d : RingedSliceEvaluationComparisons H HU F S SU B)
    (he : ∀ P N, (d.rho (H.obj (op P, N)) P).inv ≫ F.map (S.evaluation P N) =
      SU.tensor.map ((d.eta P N).hom, 𝟙 (F.obj P)) ≫
        SU.evaluation (F.obj P) (F.obj N))
    (ht : ∀ V P N (f : S.tensor.obj (V, P) ⟶ N),
      SU.transpose _ _ _ ((d.rho V P).inv ≫ F.map f) =
        F.map (S.transpose V P N f) ≫ (d.eta P N).hom)
    (hs : ∀ P N, F.map (d.sigma P N).hom ≫ (d.rho N P).hom =
      (d.rho P N).hom ≫ (d.sigmaU (F.obj P) (F.obj N)).hom)
    (ha : ∀ X Y Z,
      F.map (S.monoidal.associator X Y Z).hom ≫
        (d.rho X (S.tensor.obj (Y, Z))).hom ≫
        SU.tensor.map (X := (F.obj X, F.obj (S.tensor.obj (Y, Z))))
          (Y := (F.obj X, SU.tensor.obj (F.obj Y, F.obj Z)))
          (Prod.mkHom (𝟙 (F.obj X)) (d.rho Y Z).hom) =
      (d.rho (S.tensor.obj (X, Y)) Z).hom ≫
        SU.tensor.map (X := (F.obj (S.tensor.obj (X, Y)), F.obj Z))
          (Y := (SU.tensor.obj (F.obj X, F.obj Y), F.obj Z))
          (Prod.mkHom (d.rho X Y).hom (𝟙 (F.obj Z))) ≫
        (SU.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom)
    (K L Q : D) :
    F.map (perfectFactorSecondHomMap S d.sigma K L Q) ≫
        (d.eta K (S.tensor.obj (L, Q))).hom ≫
        HU.map (𝟙 (op (F.obj K)), (d.rho L Q).hom) =
      (d.rho (H.obj (op K, L)) Q).hom ≫
        SU.tensor.map ((d.eta K L).hom, 𝟙 (F.obj Q)) ≫
        perfectFactorSecondHomMap SU d.sigmaU (F.obj K) (F.obj L) (F.obj Q) := by
  let := S.monoidal
  let := SU.monoidal
  let A := H.obj (op K, L)
  have hev : F.map (S.evaluation K L) = (d.rho A K).hom ≫
      SU.tensor.map ((d.eta K L).hom, 𝟙 (F.obj K)) ≫
        SU.evaluation (F.obj K) (F.obj L) := by
    have h := he K L
    rw [← h, Iso.hom_inv_id_assoc]
  -- Associator preservation in the inverse direction used by the exchange.
  have hai :
      F.map (S.monoidal.associator A K Q).inv ≫ (d.rho (S.tensor.obj (A, K)) Q).hom ≫
        SU.tensor.map (X := (F.obj (S.tensor.obj (A, K)), F.obj Q))
          (Y := (SU.tensor.obj (F.obj A, F.obj K), F.obj Q))
          (Prod.mkHom (d.rho A K).hom (𝟙 (F.obj Q))) =
      (d.rho A (S.tensor.obj (K, Q))).hom ≫
        SU.tensor.map (X := (F.obj A, F.obj (S.tensor.obj (K, Q))))
          (Y := (F.obj A, SU.tensor.obj (F.obj K, F.obj Q)))
          (Prod.mkHom (𝟙 (F.obj A)) (d.rho K Q).hom) ≫
          (SU.monoidal.associator (F.obj A) (F.obj K) (F.obj Q)).inv := by
    apply (cancel_epi (F.map (S.monoidal.associator A K Q).hom)).mp
    simpa only [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp,
      Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using
      congrArg (fun f ↦ f ≫
        (SU.monoidal.associator (F.obj A) (F.obj K) (F.obj Q)).inv) (ha A K Q).symm
  -- Undo the transpose on both sides, including its source and target maps.
  unfold perfectFactorSecondHomMap
  erw [← reassoc_of% ht]
  erw [← factorTranspose_target SU, ← factorTranspose_left SU, ← factorTranspose_left SU]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (d.rho (S.tensor.obj (A, Q)) K).hom).mp
  erw [Iso.hom_inv_id_assoc]
  -- Transport the evaluation and symmetry through the tensor comparison.
  have hn := d.rho_naturality (S.tensor.obj (A, K)) Q L Q (S.evaluation K L) (𝟙 Q)
  have hn' := d.rho_naturality A (S.tensor.obj (Q, K)) A (S.tensor.obj (K, Q))
    (𝟙 A) (d.sigma Q K).hom
  simp only [Functor.map_id] at hn hn'
  erw [hn, hev]
  simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom,
    comp_whiskerRight] at hn' hai ⊢
  erw [reassoc_of% hai, reassoc_of% hn']
  erw [← whiskerLeft_comp_assoc, hs]
  erw [whiskerLeft_comp_assoc]
  -- The remaining equality is naturality of reassociation in the Hom factor.
  have ha' := ha A Q K
  simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom]
    at ha'
  erw [reassoc_of% ha']
  erw [← associator_inv_naturality_left_assoc, associator_naturality_left_assoc,
    whisker_exchange_assoc]
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor]

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]

/-- The evaluation-normalized exchange is invertible for a site-perfect tensor factor,
natural in both Hom inputs and in all morphisms of perfect factors. The final clause
specializes the very same map to the free two-term cone, with no regularity condition.
Source: latest blueprint, operation reduction, paragraph 2; Stacks 08JD, 08JJ, 08JC
(blueprint: lem-fix-perfect-factor-second-hom).

Proof:
1. Define d by transposing evaluation tensored with Q, using the closed symmetric
   monoidal structure of lem-sf-ringed-derived-closed-symmetric-monoidal.
2. Put D = Hom(Q,R). By lem-sfb-ringed-site-perfect-duality, D is perfect and
   Q maps isomorphically to Hom(D,R). Perfect duality for D gives the adjunction
   D tensor - left adjoint to - tensor Q. The evaluation normalization in
   lem-sfb-ringed-site-duality-maps identifies its counit with contraction.
3. Compose the five Hom bijections from the node: move D across Hom(K,L),
   transpose K, interchange D and K, contract D, and transpose K back.
4. Uncurrying both this bijection and postcomposition by d yields the same
   evaluation followed by contraction; naturality, the hexagon and tensor
   functoriality identify the two reorders of D,K,Hom(K,L),Q.
5. Postcomposition by d is therefore bijective for every test object. The
   preimage of the identity gives a right inverse; injectivity gives a left inverse.
6. Transpose each naturality square. Both sides apply the input map, evaluate,
   and apply the two output maps. This proves all three naturalities.
7. For [R --a--> R], bounded finite free terms give perfectness, including
   a=0 and zero divisors. Total tensor gives the scalar cone on each object;
   lem-weil-pbc-ringed-internal-hom-covariant-exact gives the same cone in the
   second Hom variable. The defining evaluation pairing is unchanged. -/
theorem perfectFactorSecondHom
    (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    (∀ K L Q : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)),
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R Q →
      IsIso (perfectFactorSecondHomMap M.closed M.symmetric.braiding K L Q)) ∧
    (∀ (K K' L L' Q Q' : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
      (f : K' ⟶ K) (g : L ⟶ L') (h : Q ⟶ Q'),
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R Q →
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R Q' →
      M.closed.tensor.map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (f.op, g), h) ≫
        perfectFactorSecondHomMap M.closed M.symmetric.braiding K' L' Q' =
      perfectFactorSecondHomMap M.closed M.symmetric.braiding K L Q ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (f.op, M.closed.tensor.map (g, h))) ∧
    (∀ (K L : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
      (a : SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⟶
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)),
      IsIso (perfectFactorSecondHomMap M.closed M.symmetric.braiding K L
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map a))))) := by
  sorry

/-- The canonical slice tensor and Hom comparisons intertwine the actual exchanges.
Source: Stacks 08JB, 08JD, 08JJ; latest blueprint, operation reduction, paragraph 2
(blueprint: lem-fix-perfect-factor-second-hom).

Proof: step 6 of the node. The theorem lem-weil-pbc-ringed-slice-evaluation-transpose
preserves evaluation, transposition and symmetry. The theorem
lem-sfb-ringed-slice-tensor-constraints preserves reassociation; it uses the
associator normalizations K and KU of lem-sf-ringed-derived-closed-symmetric-monoidal
on both sites, so that the associators in the exchange are the canonical ones. Consequently
restriction carries the defining pairing to precisely the localized pairing.
Transpose to obtain the displayed square. Perfectness remains local on the slice,
by restricting the local bounded finite-free-retract models, with varying bounds. -/
theorem perfectFactorSecondHom_restriction
    (U : C)
    [HasDerivedCategory.{w'} (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (T : CoefficientTensorModels.{r, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal)
    (_K : RingedDerivedTensorCoherence.{c, v, r, w} J R S T s)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)))
    (TU : CoefficientTensorModels.{r, max c v, v, w'} (J.over U) (R.over U) SU)
    (sU : @SymmetricCategory
      (DerivedCategory (RingedTensorModules.{max c v, v, r} (J.over U) (R.over U)))
      _ SU.monoidal)
    (_KU : RingedDerivedTensorCoherence.{max c v, v, r, w'} (J.over U) (R.over U) SU TU sU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, r, w} J R)
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U) S SU
      (RingedSliceFlatRestriction.{c, v, r} J R U))
    (_hd : RingedSliceEvaluationNormalized.{c, v, r, w, w'} J R U S T SU TU d)
    (K L Q : DerivedCategory (RingedTensorModules.{c, v, r} J R))
    (_hQ : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R Q) :
    (ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).map
        (perfectFactorSecondHomMap S d.sigma K L Q) ≫
      (d.eta K (S.tensor.obj (L, Q))).hom ≫
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map
        (Prod.mkHom
          (𝟙 (op ((ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).obj K)))
          (d.rho L Q).hom) =
    (d.rho ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) Q).hom ≫
      SU.tensor.map (Prod.mkHom (d.eta K L).hom
        (𝟙 ((ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).obj Q))) ≫
      perfectFactorSecondHomMap SU d.sigmaU
        ((ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).obj K)
        ((ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).obj L)
        ((ringedSliceDerivedRestriction.{c, v, r, w, w'} J R U).obj Q) := by
  have rules := (ringedSlice_evaluation_transpose.{c, v, r, w, w'}
    J R U S T SU TU).2 d _hd
  exact factorRestriction S SU d
    (fun P N ↦ (rules _ P N (S.evaluation P N)).1)
    (fun V P N f ↦ (rules V P N f).2.1)
    (fun P N ↦ (rules _ P N (S.evaluation P N)).2.2)
    (ringedSlice_tensor_associator.{c, v, r, w, w'}
      J R U S T s _K SU TU sU _KU d _hd) K L Q

end CategoryTheory
