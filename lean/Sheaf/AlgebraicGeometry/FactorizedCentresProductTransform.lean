/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

import Sheaf.AlgebraicGeometry.ModuleStrictTransformFlatPullback
import Sheaf.AlgebraicGeometry.StrictTransformComparisonEpimorphism
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Blowup.Gluing

/-!
# A product of factorized centres dominates the local flatifications

Source: Stacks Project, Flatness, Tag 0814, proof paragraph 2; Divisors,
Tags 0805, 080A, 080I and 080F
(blueprint: lem-trf-factorized-centres-product-transform).

The local assertion is written on the iterated fibre product. Its isomorphism
with `Y_r ×[S] Sᵇ` is specified by both projections. Strict transforms of
pulled-back modules are written as their defining cokernels, avoiding any extra
quasi-coherence or finite-type hypotheses for intermediate objects.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The finite product of the base centres, with the unit ideal for the empty family.
Source: Stacks, Tag 0814, proof paragraph 2
(blueprint: lem-trf-factorized-centres-product-transform). -/
noncomputable def factorizedProductCentre {S : Scheme.{u}} {R : Type v} [Fintype R]
    (I : R → S.IdealSheafData) : S.IdealSheafData :=
  ∏ r, I r

/-- The residual centre `J'_r` times all the extended base factors except `I_r`.
Source: Stacks, Tag 0814, proof paragraph 2
(blueprint: lem-trf-factorized-centres-product-transform). -/
noncomputable def factorizedResidualCentre {S : Scheme.{u}} {R : Type v} [Fintype R]
    (T : R → Scheme.{u}) (e : ∀ r, T r ⟶ S) (I : R → S.IdealSheafData)
    (J' : ∀ r, (T r).IdealSheafData) (r : R) : (T r).IdealSheafData :=
  by
    classical
    exact J' r * ∏ t : {t : R // t ≠ r}, (I t.1).comap (e r)

/-- The ordinary-pullback comparison, with the section-normalized compositors.
The equality `h` identifies the two maps to `X`, so this contains no arbitrary
module isomorphism.
Source: Stacks, Tag 0814, proof paragraph 1; Sheaves, Tag 0097
(blueprint: lem-trf-factorized-centres-product-transform). -/
noncomputable def factorizedTransformSourceIso {W V Y X B : Scheme.{u}}
    (p : W ⟶ V) (q : V ⟶ Y) (j : Y ⟶ X) (z : W ⟶ B) (b : B ⟶ X)
    (h : (p ≫ q) ≫ j = z ≫ b) (F : X.Modules) :
    (tensorPullback p).obj ((tensorPullback q).obj ((tensorPullback j).obj F)) ≅
      (tensorPullback z).obj ((tensorPullback b).obj F) :=
  (tensorPullbackSectionComp p q).symm.app ((tensorPullback j).obj F) ≪≫
    (tensorPullbackSectionComp (p ≫ q) j).symm.app F ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) h) ≪≫
    (tensorPullbackSectionComp z b).app F

/-- A product of factorized base centres dominates every local flatification,
including the canonical comparison of successive module transforms and their quotients.
Source: Stacks, Tag 0814, proof paragraph 2, using Tags 0805, 080A, 080I and 080F
(blueprint: lem-trf-factorized-centres-product-transform).

Proof:
1. Tensor-product and image quasi-coherence and the affine finite generating sets
show that finite products and extensions of the given ideals are finite type.
In a local ring a product is the unit ideal exactly when all factors are; hence
its support is the union of the factor supports and misses U. This gives the
admissible datum, including the unit ideal for the empty index set. The inputs are
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections,
lem-weil-pbc-quasi-coherent-module-cokernel-image,
lem-weil-pbc-module-pullback-quasi-coherent,
lem-pc-closed-subscheme-base-change-ideal-image and def-nagata-extended-ideal.
2. For fixed r, extension preserves products, so the total centre extends to
J_r K_r. Flat blowup base change (0805) gives a, and the product-ideal blowup
comparison (080A) gives d, both over T_r. Use
 def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change,
 def-nagata-blowup-product-comparison and thm-nagata-blowup-product-ideal.
3. The extended residual support is the inverse image of V(K_r). Off V(J_r),
the first blowup is an isomorphism, so every point of V(K_r) outside V(J_r)
is in the image of that extended support. This proves the displayed support
identity without assuming surjectivity over V(J_r), using
thm-nagata-global-blowup-complement and def-nagata-extended-ideal.
4. The strict-transform comparison epimorphism (080I) maps the successive
transform onto the single product-centre transform, commuting with the ordinary
quotient. Its kernel is supported on the inverse image of the total centre.
This is lem-trf-strict-transform-comparison-epimorphism.
5. The iterated-transform exceptional-support lemma says the successive transform
has no nonzero sections with precisely that support. Thus the epimorphism is
an isomorphism, uniquely specified by its quotient identity. Use
lem-trf-iterated-transform-exceptional-support and the preceding epimorphism.
6. The flat-pullback comparison for e_r and j_r identifies the pullback of the
global transform with this single local transform, with the same quotient
normalization. Fibre-product universal properties give phi and z with the
stated projection identities. Composing the comparisons gives theta. Use
lem-trf-module-strict-transform-flat-pullback and def-pc-fibre-product.
7. Pull back the assumed first flat transform along the second blowup. Relative
flatness is preserved. The extended second centre is Cartier by principalization;
relative-flat Cartier-support vanishing and the strict-transform sheaf-kernel
formula show its supported-section kernel is zero. Thus the second quotient
is an isomorphism and both identified modules are flat over the new base. Use
lem-pc-relatively-flat-module-pullback, thm-nagata-blowup-principalizes-center,
lem-trf-relative-flat-cartier-support and lem-trf-strict-transform-sheaf-kernel.
The proof uses the proof dependencies recorded on the node; no descent or
covering hypothesis is needed for this local domination assertion. -/
theorem factorizedCentres_product_transform
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (hU : IsCompact (U : Set S)) (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent]
    {R : Type v} [Fintype R] (T Y : R → Scheme.{u})
    [∀ r, CompactSpace (T r)] [∀ r, QuasiSeparatedSpace (T r)]
    (g : ∀ r, Y r ⟶ T r) (e : ∀ r, T r ⟶ S) (j : ∀ r, Y r ⟶ X)
    (h : ∀ r, j r ≫ f = g r ≫ e r)
    [∀ r, QuasiCompact (e r)] [∀ r, Flat (e r)] [∀ r, Flat (j r)]
    (J J' : ∀ r, (T r).IdealSheafData) (I : R → S.IdealSheafData)
    [∀ r, (J r).toModules.IsFiniteType] [∀ r, (J' r).toModules.IsFiniteType]
    [∀ r, (I r).toModules.IsFiniteType]
    (hIU : ∀ r, (I r).comap U.ι = ⊤)
    (hfactor : ∀ r, (I r).comap (e r) = J r * J' r)
    (hflat : ∀ r,
      (cokernel (kernel.ι (moduleStrictTransformRestriction (g r) (J r) ((tensorPullback (j r)).obj
        F)))).IsFlatOver (pullback.snd (g r) (J r).blowupMap)) :
    ∃ hI : (factorizedProductCentre I).toModules.IsFiniteType,
      ((factorizedProductCentre I).support : Set S) = ⋃ r, ((I r).support : Set S) ∧
      ((factorizedProductCentre I).support : Set S) ⊆ (U : Set S)ᶜ ∧
      (∃ B : IsAdmissible S U, B.I = factorizedProductCentre I) ∧
      ∀ r,
        ∃ a : Limits.pullback (e r) (factorizedProductCentre I).blowupMap ≅ (J r *
          factorizedResidualCentre T e I J' r).blowup,
          a.hom ≫ (J r * factorizedResidualCentre T e I J' r).blowupMap =
            pullback.fst (e r) (factorizedProductCentre I).blowupMap ∧
        ∃ d : ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap).blowup ≅ (J r *
          factorizedResidualCentre T e I J' r).blowup,
          d.hom ≫ (J r * factorizedResidualCentre T e I J' r).blowupMap =
            ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap).blowupMap ≫ (J
              r).blowupMap ∧
          ((J r * factorizedResidualCentre T e I J' r).support : Set (T r)) =
            ((J r).support : Set (T r)) ∪
              (J r).blowupMap '' (((factorizedResidualCentre T e I J' r).comap (J
                r).blowupMap).support : Set (J r).blowup) ∧
        ∃ phi : Limits.pullback (pullback.snd (g r) (J r).blowupMap) ((factorizedResidualCentre T e
          I J' r).comap (J r).blowupMap).blowupMap ≅
            Limits.pullback (g r ≫ e r) (factorizedProductCentre I).blowupMap,
          phi.hom ≫ pullback.fst (g r ≫ e r) (factorizedProductCentre I).blowupMap =
            pullback.fst (pullback.snd (g r) (J r).blowupMap) ((factorizedResidualCentre T e I J'
              r).comap (J r).blowupMap).blowupMap ≫ pullback.fst (g r) (J r).blowupMap ∧
          phi.hom ≫ pullback.snd (g r ≫ e r) (factorizedProductCentre I).blowupMap =
            pullback.snd (pullback.snd (g r) (J r).blowupMap) ((factorizedResidualCentre T e I J'
              r).comap (J r).blowupMap).blowupMap ≫ d.hom ≫ a.inv ≫
              pullback.snd (e r) (factorizedProductCentre I).blowupMap ∧
        ∃ z : Limits.pullback (pullback.snd (g r) (J r).blowupMap) ((factorizedResidualCentre T e I
          J' r).comap (J r).blowupMap).blowupMap ⟶
            Limits.pullback f (factorizedProductCentre I).blowupMap,
        ∃ hz : (pullback.fst (pullback.snd (g r) (J r).blowupMap) ((factorizedResidualCentre T e I
          J' r).comap (J r).blowupMap).blowupMap ≫ pullback.fst (g r) (J r).blowupMap) ≫ j r =
            z ≫ pullback.fst f (factorizedProductCentre I).blowupMap,
          z ≫ pullback.snd f (factorizedProductCentre I).blowupMap =
            phi.hom ≫ pullback.snd (g r ≫ e r) (factorizedProductCentre I).blowupMap ∧
          IsIso (cokernel.π (kernel.ι
          (moduleStrictTransformRestriction (pullback.snd (g r) (J r).blowupMap)
            ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap)
            (cokernel (kernel.ι (moduleStrictTransformRestriction (g r) (J r) ((tensorPullback (j
              r)).obj F))))))) ∧
          (cokernel (kernel.ι
          (moduleStrictTransformRestriction (pullback.snd (g r) (J r).blowupMap)
            ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap)
            (cokernel (kernel.ι (moduleStrictTransformRestriction (g r) (J r) ((tensorPullback (j
              r)).obj F))))))).IsFlatOver (pullback.snd (pullback.snd (g r) (J r).blowupMap)
              ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap).blowupMap) ∧
          ((tensorPullback z).obj (@moduleStrictTransform X S f (factorizedProductCentre I) hI F
            inferInstance)).IsFlatOver (pullback.snd (pullback.snd (g r) (J r).blowupMap)
            ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap).blowupMap) ∧
          ∃! theta : cokernel (kernel.ι
          (moduleStrictTransformRestriction (pullback.snd (g r) (J r).blowupMap)
            ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap)
            (cokernel (kernel.ι (moduleStrictTransformRestriction (g r) (J r) ((tensorPullback (j
              r)).obj F)))))) ≅
              (tensorPullback z).obj (@moduleStrictTransform X S f (factorizedProductCentre I) hI F
                inferInstance),
            (tensorPullback (pullback.fst (pullback.snd (g r) (J r).blowupMap)
              ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap).blowupMap)).map
              (cokernel.π (kernel.ι
          (moduleStrictTransformRestriction (g r) (J r) ((tensorPullback (j r)).obj F)))) ≫
                cokernel.π (kernel.ι
          (moduleStrictTransformRestriction (pullback.snd (g r) (J r).blowupMap)
            ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap)
            (cokernel (kernel.ι (moduleStrictTransformRestriction (g r) (J r) ((tensorPullback (j
              r)).obj F)))))) ≫ theta.hom =
              (factorizedTransformSourceIso (pullback.fst (pullback.snd (g r) (J r).blowupMap)
                ((factorizedResidualCentre T e I J' r).comap (J r).blowupMap).blowupMap)
                (pullback.fst (g r) (J r).blowupMap) (j r) z
                (pullback.fst f (factorizedProductCentre I).blowupMap) hz F).hom ≫
                (tensorPullback z).map (cokernel.π (kernel.ι (moduleStrictTransformRestriction f
                  (factorizedProductCentre I) F))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
