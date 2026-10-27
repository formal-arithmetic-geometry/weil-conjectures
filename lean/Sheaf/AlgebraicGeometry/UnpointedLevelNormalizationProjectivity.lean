/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.StableAbelianLevelNormalization
public import Sheaf.AlgebraicGeometry.SmoothCurveAbelianLevelRigidification
public import Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.FiniteOverProjective

/-! # Projectivity and families on the full unpointed level normalization

Source: de Jong (1996), §2.24, printed p. 62; Pikaart--de Jong (1995), §§2.3.3--2.3.7,
Proposition 2.3.4 and Remark 2.3.7
(blueprint: lem-sfb-unpointed-level-normalization-projectivity).

The supplied normalization and smooth-square witnesses are precisely those of
`exists_stable_abelian_level_normalization`. Evaluation at the identity gives the
actual universal stable family. On every field-valued smooth family the same finite
etale scheme represents its frames and its 2-fibre in the normalization. Equivalences
over the represented base express naturality on all test schemes, rather than just
bijections of field-valued points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The full level normalization is finite type and H-projective over the field, carries
its actual stable family, and has the finite etale frame functor as every smooth 2-fibre.
The hypotheses specify the representatives and normalization from the dependency nodes;
they do not select a generic component or assume a rational frame. The frame's universal
property is expressed with the canonical cohomology exchange in `HomCondition`.

Source: de Jong (1996), §2.24, printed p. 62; Pikaart--de Jong (1995), §§2.3.3--2.3.7,
Proposition 2.3.4 and Remark 2.3.7
(blueprint: lem-sfb-unpointed-level-normalization-projectivity).

Proof:
1. By lem-sfb-stable-abelian-level-normalization the map to the coarse scheme is finite.
   The latter is finite type by lem-sfb-unpointed-stable-coarse-projective. On finite
   affine covers, module generators of the finite algebra together with algebra
   generators of the coarse chart give finite generation over the field. Thus the
   composite is locally finite type and quasi-compact.
2. The coarse scheme is H-projective and quasi-compact, hence projective in the
   convention of def-pc-projective-morphism. Apply lem-fin-finite-over-projective over
   the affine Noetherian scheme Spec k. Its affine-base conclusion gives a closed
   embedding of Z in a finite projective space over k.
3. Evaluate a on the identity of Z. This is a stable unpointed family, including its
   projective-bundle condition. The unique arrow from a test map z to the identity in
   the represented groupoid gives, after applying a, its cartesian family arrow to
   this universal family. Functoriality makes these arrows a natural transformation,
   giving the required identifications with fibre products under further base change.
4. Given C/F, use the smooth 2-cartesian square of
   lem-sfb-stable-abelian-level-normalization to identify its 2-fibre in Z with its
   2-fibre in the full smooth level scheme. A comma object has comparison C_B to a(z),
   so invert it to obtain the pair's beta from the universal family to C_B. Both scheme
   factors are discrete, hence the fibre is the discrete functor of actual pairs.
5. By lem-sfb-smooth-curve-abelian-level-rigidification the latter fibre is the frame
   functor, represented by a finite etale surjective scheme P. Transporting a frame
   by the inverse of beta's cohomology pullback and its inverse operation give the
   comparison, naturally on arbitrary, possibly nonreduced, test schemes. Its universal
   frame has exactly the unique classifying maps and canonical frame equations below.
   Surjectivity asserts nonempty geometric fibres, without an F-rational point. -/
theorem unpointedLevelNormalizationProjectivity
    (k : Type u) [Field k] (g : ℕ) (hg : 2 ≤ g)
    (ℓ : AbelianLevelPrime (Spec (.of k)))
    (L : Over (Spec (.of k)))
    (eL : BasedFunctor (discreteModuli (yoneda.obj L))
      (abelianLevelBased (Spec (.of k)) g ℓ))
    (hL : eL.toFunctor.IsEquivalence)
    (Q : Over (Spec (.of k)))
    (π : BasedFunctor (stableModuliBased (Spec (.of k)) g)
      (discreteModuli (yoneda.obj Q)))
    (hQ : IsCoarseModuliScheme (stableModuliBased (Spec (.of k)) g) Q π)
    (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hQproj : IsHProjective Q.hom)
    (Z : Over (Spec (.of k)))
    (a : BasedFunctor (discreteModuli (yoneda.obj Z))
      (stableModuliBased (Spec (.of k)) g))
    (c : Z ⟶ Q) (hc : IsFinite c.left)
    (hcoarse : Nonempty (ModuliTwoIso (a.comp π) (discreteModuliMap (yoneda.map c))))
    (i : L ⟶ Z)
    (e : (discreteModuliMap (yoneda.map i)).comp a ≅ abelianLevelSchemeMap eL)
    (hnorm : IsModuliChartNormalization (abelianLevelSchemeMap eL) a
      (discreteModuliMap (yoneda.map i)) e)
    (hsmooth : (moduliTwoFiberLift (discreteModuliMap (yoneda.map i))
      (eL.comp (abelianLevelToSmooth (Spec (.of k)) g ℓ)) e).toFunctor.IsEquivalence) :
    LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsHProjective Z.hom ∧
    (∃ η : a.toFunctor ⟶
        (Functor.const _).obj (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj Z)))),
      ∀ z : (discreteModuli (yoneda.obj Z)).obj,
        (StablePointedModuli.forget (Spec (.of k)) g 0).IsHomLift
          (yoneda.preimage z.hom) (η.app z)) ∧
    ∀ (F : Type u) [Field F] [Algebra k F]
      (C : StablePointedModuli.Smooth (Spec (.of k)) g 0),
      C.obj.base = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k F))) →
      ∃ (P : Over (Spec (.of k))) (r : P ⟶ C.obj.base),
        IsFinite r.left ∧ Etale r.left ∧ Surjective r.left ∧
        ∃ frameP : abelianLevelConstant P.left g ℓ.val ≅
            abelianLevelCohomology (smoothCurveModuliPullback C P r).obj.projection ℓ.val,
          (∀ (T : Over (Spec (.of k))) (b : T ⟶ C.obj.base)
            (α : abelianLevelConstant T.left g ℓ.val ≅
              abelianLevelCohomology (smoothCurveModuliPullback C T b).obj.projection ℓ.val),
            ∃! d : T ⟶ P, d ≫ r = b ∧
              ∃ q : smoothCurveModuliPullback C T b ⟶ smoothCurveModuliPullback C P r,
                q.hom.base = d ∧
                q.hom.map ≫ pullback.fst C.obj.projection r.left =
                  pullback.fst C.obj.projection b.left ∧
                AbelianLevelModuli.HomCondition
                  (⟨smoothCurveModuliPullback C T b, α⟩ :
                    AbelianLevelModuli (Spec (.of k)) g ℓ)
                  (⟨smoothCurveModuliPullback C P r, frameP⟩ :
                    AbelianLevelModuli (Spec (.of k)) g ℓ) q) ∧
          ∃ t : BasedFunctor (discreteModuli (yoneda.obj C.obj.base))
              (smoothModuliBased (Spec (.of k)) g),
            ∃ ηC : t.toFunctor ⟶ (Functor.const _).obj C,
              (∀ z : (discreteModuli (yoneda.obj C.obj.base)).obj,
                (smoothCurveModuliBase (Spec (.of k)) g).IsHomLift
                  (yoneda.preimage z.hom) (ηC.app z)) ∧
              ∃ eP : BasedFunctor (discreteModuli (yoneda.obj P))
                  (moduliTwoFiberProduct (t.comp (smoothModuliInclusion (Spec (.of k)) g)) a),
                eP.toFunctor.IsEquivalence ∧
                Nonempty (ModuliTwoIso
                  (eP.comp (moduliTwoFiberFst
                    (t.comp (smoothModuliInclusion (Spec (.of k)) g)) a))
                  (discreteModuliMap (yoneda.map r))) := by
  sorry

end AlgebraicGeometry
