/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.ProEtaleScalarMateNormalization
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.TensorPullbackRepresentativeDescent

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

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
    (ℓ : ℕ) [Fact ℓ.Prime]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
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
  sorry

end AlgebraicGeometry.ProEtale
