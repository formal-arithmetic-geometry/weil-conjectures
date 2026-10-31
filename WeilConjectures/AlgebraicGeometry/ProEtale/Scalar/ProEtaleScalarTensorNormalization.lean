/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarChainCounitSquare
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarTensorRepresentativeSquare
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Underlying tensor normalization of pro-etale scalar pullback

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, proof on flat K-flat
representatives; sites-modules.tex, Tag 03EL, coefficient-action normalization
(blueprint: lem-sp-proetale-scalar-tensor-normalization).

The scalar-to-tensor identifications and the coefficient-factor identification are
those already normalized in `ProEtaleScalarMateNormalization`. Tensor models are
presentations of the ordinary unbounded derived tensor, not additional assumptions
on schemes, coefficients, or complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem tensorIso_section
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEtᵒᵖ)
    (b : (proEtaleConstantRing Y B).obj.obj U) (x : M.val.obj U) :
    ((scalarMateOrdinaryTensorIso φ Y).hom.app M).val.app U
      (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ) M U b x) =
        proEtaleTensorPair Y (proEtaleConstantRing Y A) M
          (scalarMateCoefficient φ Y) U x b := by
  have h := (scalarMateOrdinaryTensorIso_existsUnique φ Y).exists.choose_spec M U b x
  with_unfolding_all exact h

private theorem scalarTensorChainIso_section
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (ht : IsScalarBalancing φ f t)
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (i : ℤ) (V : Y.ProEt) (x : (P.X i).val.obj (Opposite.op V))
    (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)) :
    ((scalarTensorChainIso φ f t P).hom.f i).val.app
      (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleConstantRingAdjunction A f).unit.app
        ((scalarMateRestriction φ Y).obj
          ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj
            (P.X i)))).val.app (Opposite.op V)
              (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
                (P.X i) (Opposite.op V) s x)) =
    reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
      ((proEtaleConstantRingPullback A f).obj (P.X i))
      (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
          (Opposite.op V)) s)
      (((proEtaleConstantRingAdjunction A f).unit.app (P.X i)).val.app
        (Opposite.op V) x) := by
  let M := P.X i
  let W := Opposite.op ((proEtaleBaseChange f).obj V)
  let v := (scalarMateOrdinaryTensorIso φ X).app
    ((proEtaleConstantRingPullback A f).obj M)
  apply (Iso.toLinearEquiv ((SheafOfModules.evaluation _ W).mapIso v)).injective
  change v.hom.val.app W
    (((scalarTensorChainIso φ f t P).hom.f i).val.app W _) = _
  have he : (scalarTensorChainIso φ f t P).hom.f i ≫ v.hom =
      (proEtaleConstantRingPullback A f).map
        ((scalarMateOrdinaryTensorIso φ Y).hom.app M) ≫ t.hom.app M := by
    change ((proEtaleConstantRingPullback A f).map
      ((scalarMateOrdinaryTensorIso φ Y).hom.app M) ≫ t.hom.app M ≫ v.inv) ≫
        v.hom = _
    simp only [Category.assoc, v.inv_hom_id]
    exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)
  have hn := congrArg (fun a ↦ a.val.app (Opposite.op V)
    (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
      M (Opposite.op V) s x))
    ((proEtaleConstantRingAdjunction A f).unit.naturality
      ((scalarMateOrdinaryTensorIso φ Y).hom.app M)).symm
  change ((proEtaleConstantRingPullback A f).map
      ((scalarMateOrdinaryTensorIso φ Y).hom.app M)).val.app W
      (((proEtaleConstantRingAdjunction A f).unit.app _).val.app (Opposite.op V) _) =
    ((proEtaleConstantRingAdjunction A f).unit.app _).val.app (Opposite.op V)
      (((scalarMateOrdinaryTensorIso φ Y).hom.app M).val.app (Opposite.op V)
        (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
          M (Opposite.op V) s x)) at hn
  rw [tensorIso_section] at hn
  have he' := congrArg (fun a ↦ a.val.app W
    (((proEtaleConstantRingAdjunction A f).unit.app _).val.app (Opposite.op V)
      (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
        M (Opposite.op V) s x))) he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at he'
  refine he'.trans ?_
  exact (congrArg (fun z ↦ (t.hom.app M).val.app W z) hn).trans
    ((ht M V x s).trans (tensorIso_section φ X _ W _ _).symm)

attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarTensorChainIso scalarMateDerivedTensorIso
  proEtaleCanonicalTensorComparison scalarExtensionFunctorCounit

section

private local instance siteEssentiallySmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0} Y.ProEt

private theorem flatFromMonoidal
    {A : Type u} [CommRing A] (Y : Scheme.{u})
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (h : exactFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A))
      (proEtaleRingModules Y (proEtaleConstantRing Y A))
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (proEtaleConstantRing Y A)) M)) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) M := by
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
      (proEtaleConstantRing Y A) M).symm h

end

/-- Forgetting the target coefficient action identifies the actual scalar/pullback
comparison with the canonical tensor/pullback comparison, including its chain model.
The first equality is written through the normalized scalar-to-tensor isomorphisms;
the final coefficient map is the canonical constant-section identification `c_B`.
The second conjunct gives an actual chain isomorphism, its degreewise pure-tensor
formula, and its localization square using the scalar counits and exact factors.

Source: Stacks Tags 03EL, 06YS, 06YY, 07A2 and 07A4
(blueprint: lem-sp-proetale-scalar-tensor-normalization).

Proof:
1. The constant coefficient square commutes since both routes send a to phi(a),
   first on constants, then by restrictions, gluing and sheafification. The recorded
   restriction comparison b is identity on the underlying inverse-image sheaf with
   its transported A-action (prop-weil-pbc-proetale-constant-ring-map and
   lem-weil-pbc-ring-sheaf-change-adjunction).
2. Apply lem-pur-proetale-inverse-image-tensor-comparison to (M,B_Y), and transport
   along c_A and c_B. This gives the ordinary balancing isomorphism sending the
   inverse-image unit of x tensor s to inverse-image x tensor c_B(inverse-image s).
   The coefficient square preserves balancing. Locally a B_X-section is constant;
   multiplying that constant through the formula proves B-linearity and glues.
   Sheaf tensor universality proves naturality, without claiming every section of
   the sheafified tensor is a tensor of sections.
3. Apply this natural ordinary isomorphism to P in every degree. Naturality for
   each differential gives the chain equation and inverse chain equation. There
   is no infinite totalization issue because the coefficient is in degree zero.
4. For flat-term K-flat P, scalar-derived counits compute extension on P and its
   pullback. Exact inverse image and restriction have their localization factors
   on every complex, even when P tensor B is not K-flat over A. The defining
   balancing normalization of def-sp-constant-scalar-pullback-comparison identifies
   b inverse followed by restriction of theta with Q(t_P) in these coordinates.
5. Resolve B_Y[0] by a flat-term K-flat H. Tensoring H -> B_Y[0] with P, or its
   pullback, is a quasi-isomorphism: use the acyclic-cone criterion, K-flatness,
   tensor/mapping-cone identification and the signed tensor symmetry. Exact
   pullback preserves these quasi-isomorphisms. Simultaneous naturality of the
   ordinary comparison gives the commuting tensor/pullback square before Q.
6. On (P,H), lem-pur-kflat-total-tensor-model and pullback preservation give flat
   K-flat representatives for all total tensors. The fully faithful two-variable
   resolving restriction of lem-weil-pbc-site-derived-tensor-descent and
   lem-weil-pbc-tensor-comparison-descent-representatives identifies the top map
   with the canonical Tag 07A4 comparison. Cancel the invertible vertical arrows
   of step 5 to identify its specialization at B_Y with Q(t_P).
7. Both comparisons thus equal Q(t_P). Resolve any unbounded K by flat-term
   K-flat P using lem-pc-kflat-resolution. Naturality and cancellation of the
   localized resolution extend the equality to every K, independently of choices.
   No boundedness, flatness of B/A, or finite Tor dimension enters the argument.
-/
theorem proEtaleScalarTensorNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y A))
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X A)) :
    (∀ K : proEtaleDerivedCategory Y A,
      (proEtaleConstantRingDerivedPullback A f).map
          ((scalarMateDerivedTensorIso φ Y aY).inv.app K) ≫
        (proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv.app
              ((directImageScalarExtension φ Y).obj K) ≫
        (scalarMateRestriction φ X).mapDerivedCategory.map
          ((directImageScalarPullbackIso φ f).hom.app K) ≫
        (scalarMateDerivedTensorIso φ X aX).hom.app
          ((proEtaleConstantRingDerivedPullback A f).obj K) =
      (proEtaleCanonicalTensorComparison f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
        (proEtaleConstantRingComparison f A) aY aX).hom.app
          (K, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y)) ≫
        aX.tensor.map (Prod.mkHom
          (𝟙 ((proEtaleConstantRingDerivedPullback A f).obj K))
          (scalarMateDerivedCoefficientPullback φ f).hom)) ∧
    (∀ P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
        (R := proEtaleConstantRing Y A) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) →
      ∃ t :
        ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj
          (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
            ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≅
        ((scalarMateRestriction φ X).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)),
        (∀ (i : ℤ) (V : Y.ProEt)
          (x : (P.X i).val.obj (Opposite.op V))
          (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)),
          (t.hom.f i).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleConstantRingAdjunction A f).unit.app
              ((scalarMateRestriction φ Y).obj
                ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj
                  (P.X i)))).val.app (Opposite.op V)
                    (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
                      (P.X i) (Opposite.op V) s x)) =
          reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
            ((proEtaleConstantRingPullback A f).obj (P.X i))
            (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
              (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
                (Opposite.op V)) s)
            (((proEtaleConstantRingAdjunction A f).unit.app (P.X i)).val.app
              (Opposite.op V) x)) ∧
        (proEtaleConstantRingDerivedPullback A f).map
          ((scalarMateRestriction φ Y).mapDerivedCategory.map
              (scalarExtensionFunctorCounit φ Y P) ≫
            (scalarMateRestriction φ Y).mapDerivedCategoryFactors.hom.app
              ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
          (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
            (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
              ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
          DerivedCategory.Q.map t.hom =
        (proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv.app
              ((directImageScalarExtension φ Y).obj (DerivedCategory.Q.obj P)) ≫
          (scalarMateRestriction φ X).mapDerivedCategory.map
            ((directImageScalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
              (directImageScalarExtension φ X).map
                ((proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
              scalarExtensionFunctorCounit φ X
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
            ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
              (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} Y.ProEt
  obtain ⟨_, _, t, ht, _, _, _⟩ := proEtaleScalarBalancingChain φ f
  let F := proEtaleConstantRingDerivedPullback A f
  let E := directImageScalarExtension φ X
  let r := (scalarMateRestriction φ X).mapDerivedCategory
  let hY := scalarMateDerivedTensorIso φ Y aY
  let hX := scalarMateDerivedTensorIso φ X aX
  let b := proEtaleRingRestrictionDerivedPullback f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  let θ := directImageScalarPullbackIso φ f
  let GY := (Functor.curryObj aY.tensor).flip.obj
    (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y))
  let GX := (Functor.curryObj aX.tensor).flip.obj
    (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ X))
  let τ := proEtaleCanonicalTensorComparison f
    (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (proEtaleConstantRingComparison f A) aY aX
  let v := scalarMateDerivedCoefficientPullback φ f
  let L : GY ⋙ F ≅ F ⋙ GX :=
    Functor.isoWhiskerRight hY.symm F ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (directImageScalarExtension φ Y) b.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight θ r ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F hX
  let R : GY ⋙ F ≅ F ⋙ GX := NatIso.ofComponents
    (fun K ↦ τ.app (K, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y)) ≪≫
      aX.tensor.mapIso (Iso.prod (Iso.refl (F.obj K)) v)) (by
        intro K K' g
        have hn := τ.hom.naturality
          (Prod.mkHom g (𝟙 (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y))))
        change F.map (aY.tensor.map (Prod.mkHom g (𝟙 _))) ≫ τ.hom.app _ =
          τ.hom.app _ ≫ aX.tensor.map (Prod.mkHom (F.map g) (F.map (𝟙 _))) at hn
        change F.map (aY.tensor.map (Prod.mkHom g (𝟙 _))) ≫
            (τ.hom.app _ ≫ aX.tensor.map (Prod.mkHom (𝟙 _) v.hom)) =
          (τ.hom.app _ ≫ aX.tensor.map (Prod.mkHom (𝟙 _) v.hom)) ≫
            aX.tensor.map (Prod.mkHom (F.map g) (𝟙 _))
        rw [← Category.assoc, hn, Category.assoc, Category.assoc,
          ← aX.tensor.map_comp, ← aX.tensor.map_comp]
        congr 2
        apply Prod.hom_ext
        · change F.map g ≫ 𝟙 _ = 𝟙 _ ≫ F.map g
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        · change F.map (𝟙 _) ≫ v.hom = v.hom ≫ 𝟙 _
          rw [F.map_id]
          exact (Category.id_comp _).trans (Category.comp_id _).symm)
  have hgood (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
      (hp : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
        (R := proEtaleConstantRing Y A) P)
      (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) :
      L.hom.app (DerivedCategory.Q.obj P) = R.hom.app (DerivedCategory.Q.obj P) := by
    let FP := ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P
    have hpX := (proEtaleCanonicalTensorPullback f
      (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (proEtaleConstantRingComparison f A) aY aX).1 P ⟨hp, hf⟩
    have hc : IsIso (scalarExtensionFunctorCounit φ X FP) :=
      scalarExtensionFunctor_kflat_representation φ X FP hpX.1
    let e := r.map
      (E.map ((proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
        scalarExtensionFunctorCounit φ X FP) ≫
      (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
        ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj FP)
    have : IsIso e := by dsimp only [e]; infer_instance
    have hs := scalarTensorChainCounitSquare φ f t ht P
    have htensor := scalarTensorRepresentativeSquare φ f aY aX t ht P hp hf
    have h := (congrArg (fun z ↦ F.map (hY.inv.app (DerivedCategory.Q.obj P)) ≫ z)
      hs).symm.trans (by
        simpa only [Functor.map_comp, Category.assoc] using htensor)
    apply (cancel_mono (hX.inv.app (F.obj (DerivedCategory.Q.obj P)) ≫ e)).mp
    simpa only [L, R, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      NatIso.ofComponents_hom_app, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Category.assoc, Category.id_comp,
      Category.comp_id, hX.hom_inv_id_app_assoc, Functor.map_comp, e, FP, r, E] using h
  constructor
  · intro K
    have heq : L.hom.app K = R.hom.app K := by
      let G : CochainComplex
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ :=
        DerivedCategory.Q.objPreimage K
      obtain ⟨P, q, hp, hf, hq, _⟩ :=
        CochainComplex.exists_isKFlatResolutionGeneral.{u + 1, u}
          (C := Y.ProEt) (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) G
      have : QuasiIso q := hq
      let u := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
      apply (cancel_epi ((GY ⋙ F).map u.hom)).mp
      rw [L.hom.naturality, R.hom.naturality]
      rw [hgood P hp (fun n ↦ flatFromMonoidal Y (P.X n) (hf n))]
    simpa only [L, R, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      NatIso.ofComponents_hom_app, Iso.app_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, Category.assoc, Category.id_comp,
      Category.comp_id] using heq
  · intro P _ _
    exact ⟨scalarTensorChainIso φ f t P, scalarTensorChainIso_section φ f t ht P,
      scalarTensorChainCounitSquare φ f t ht P⟩

end AlgebraicGeometry.ProEtale
