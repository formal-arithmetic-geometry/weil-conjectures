/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusWellDefined
import Sheaf.AlgebraicGeometry.WeaklyEtaleUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.RelativeFrobeniusIntegralUniversalHomeomorphism
import Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Canonical trivialization of absolute Frobenius on the small pro-etale site

Source: the main-20261015 blueprint, six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-trf-absolute-frobenius-site`, and Stacks Tag 0F6W
(blueprint: lem-trf-absolute-frobenius-site).

All constant commutative coefficient rings are allowed. The module adjunction unit,
evaluated on every section, fixes the trivialization; its derived version is exact
termwise descent. The comparisons in the compatibility equations are fixed by
fibre-product pasting and conjugation, not independently chosen isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Exact descent of a module-pullback trivialization, including the identity comparison.
Source: blueprint, proof paragraph 4 and Stacks Section 0735
(blueprint: lem-trf-absolute-frobenius-site). -/
noncomputable def proEtaleFrobeniusDerivedIso (A : Type u) [CommRing A]
    {X : Scheme.{u}} {f : X ⟶ X} (e : proEtaleConstantRingPullback A f ≅ 𝟭 _) :
    proEtaleConstantRingDerivedPullback A f ≅ 𝟭 (proEtaleDerivedCategory X A) :=
  Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryIdIso (proEtaleRingModules X (proEtaleConstantRing X A))

/-- Exact descent of a module composition comparison, with the ordinary derived pasting.
Source: Stacks Tag 0D6D and blueprint proof paragraph 4
(blueprint: lem-trf-absolute-frobenius-site). -/
noncomputable def proEtaleFrobeniusDerivedComp (A : Type u) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : proEtaleConstantRingPullback A (f ≫ g) ≅
      proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f) :
    proEtaleConstantRingDerivedPullback A (f ≫ g) ≅
      proEtaleConstantRingDerivedPullback A g ⋙ proEtaleConstantRingDerivedPullback A f :=
  Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryCompIso
      (proEtaleConstantRingPullback A g) (proEtaleConstantRingPullback A f)

/-- Absolute Frobenius has the canonical, open-compatible and iterate-compatible
trivialization on the ordinary unbounded derived category of its small pro-etale site.
The existential families are normalized on sections, so record the actual canonical maps.
The zero-iterate clause retains the identity, including on the empty scheme.

Source: main-20261015 blueprint, lem-trf-absolute-frobenius-site, and Stacks Tag 0F6W
(blueprint: lem-trf-absolute-frobenius-site).

Proof, following the seven steps of the DAG:
1. Put u(V) = V ×[X,F_X] X. Relative Frobenius has projections (F_V,v); the two
   projection equations prove naturality. Use the swap if the chosen base change has
   the other product order (def-pc-fibre-product, def-weil-proetale-inverse-image).
2. Relative Frobenius is integral and universally bijective by
   lem-trf-relative-frobenius-universal-homeomorphism (Stacks 0CCB).
3. Both site objects are weakly etale over X, by base change. Apply
   lem-trf-weakly-etale-between-objects and lem-trf-weakly-etale-homeomorphism to obtain
   the site isomorphisms r. They preserve covers by their naturality.
4. Precomposition gives the direct-image trivialization. Its inverse sends a section
   m on V to M(r_V inverse)(m) on u(V). Take its unique left-adjoint mate using
   lem-weil-pbc-conjugate-iso-unit-equation and the actual inverse-image adjunction.
   In inverse-image colimit coordinates the resulting map is
   (V,phi,x) ↦ M(r_V inverse composed with phi)(x). Sheafification extends it uniquely
   (def-weil-pbc-sheafification).
5. On constants the same map fixes every scalar. It therefore equals the published
   coefficient comparison. Transport the module action and tensor along that ring
   isomorphism. The normalized module adjunction gives precisely the displayed unit
   equation. Both module functors are exact; applying the comparison degreewise and
   localizing gives proEtaleFrobeniusDerivedIso
   (lem-weil-pbc-localization-universal-property, def-weil-pbc-proetale-operations).
6. Frobenius preserves every open. Relative Frobenius on an object over an open has
   the same two projections, so the section map is unchanged by restriction
   (lem-weil-absolute-frobenius-well-defined,
   lem-weil-proetale-weakly-etale-localization). The normalized mates and their exact
   derived descents agree under the displayed canonical square comparison.
7. The composite u_b(r_a) composed with r_b has projections F_V^(a+b) and v, hence is
   r_(a+b). Contravariance gives the successive section maps; the unit equation gives
   the module composite. Fibre-product pasting fixes its comparison by conjugation.
   Exact descent gives the displayed derived iterate equation. Equivalently use
   lem-pc-kflat-resolution and the flat K-flat normalization of
   lem-weil-pbc-proetale-derived-pullback-composition, then localization uniqueness.
   For zero the relative map is the canonical identity-base-change comparison. -/
theorem absoluteFrobenius_proEtale_trivialization (p : ℕ) (hp : Nat.Prime p)
    (A : Type u) [CommRing A] :
    ∃ (r : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
        𝟭 X.ProEt ≅ proEtaleBaseChange (X.iterateFrobenius hp (hX.2 ⊤) n)),
      (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (V : X.ProEt),
        ∃ hV : (p : Γ(V.left, ⊤)) = 0,
          ((r X hX n).hom.app V).left ≫
              pullback.fst V.hom (X.iterateFrobenius hp (hX.2 ⊤) n) =
            V.left.iterateFrobenius hp hV n) ∧
      ∃ (comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
          proEtaleConstantRingPullback A (f ≫ g) ≅
            proEtaleConstantRingPullback A g ⋙ proEtaleConstantRingPullback A f),
        (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
          (m : ((proEtaleConstantRingPushforward A f ⋙
            proEtaleConstantRingPushforward A g).obj M).val.obj (Opposite.op V)),
          ((conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction A g).comp (proEtaleConstantRingAdjunction A f))
            (proEtaleConstantRingAdjunction A (f ≫ g)) (comp f g)).hom.app M).val.app
              (Opposite.op V) m =
            M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op m) ∧
        ∃ (tau : ∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
            proEtaleConstantRingPullback A (X.iterateFrobenius hp (hX.2 ⊤) n) ≅ 𝟭 _),
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ)
            (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : X.ProEt)
            (m : M.val.obj (Opposite.op V)),
            ((proEtaleConstantRingAdjunction A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).unit.app M ≫
              (proEtaleConstantRingPushforward A
                (X.iterateFrobenius hp (hX.2 ⊤) n)).map ((tau X hX n).hom.app M)).val.app
                  (Opposite.op V) m = M.val.map ((r X hX n).inv.app V).op m) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ) (U : X.Opens),
            ∃ (hU : U.toScheme.IsCharacteristic p)
              (w : U.toScheme.iterateFrobenius hp (hU.2 ⊤) n ≫ U.ι =
                U.ι ≫ X.iterateFrobenius hp (hX.2 ⊤) n),
              (proEtaleFrobeniusDerivedComp A U.ι
                (X.iterateFrobenius hp (hX.2 ⊤) n)
                (comp U.ι (X.iterateFrobenius hp (hX.2 ⊤) n))).inv ≫
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (U.toScheme.iterateFrobenius hp (hU.2 ⊤) n) U.ι
                  (comp (U.toScheme.iterateFrobenius hp (hU.2 ⊤) n) U.ι)).hom ≫
                Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A U.ι)
                  (proEtaleFrobeniusDerivedIso A (tau U.toScheme hU n)).hom ≫
                (Functor.rightUnitor _).hom =
              Functor.whiskerRight (proEtaleFrobeniusDerivedIso A (tau X hX n)).hom
                (proEtaleConstantRingDerivedPullback A U.ι) ≫ (Functor.leftUnitor _).hom) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (a b : ℕ),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) a ≫
                X.iterateFrobenius hp (hX.2 ⊤) b =
                  X.iterateFrobenius hp (hX.2 ⊤) (a + b),
              (proEtaleFrobeniusDerivedIso A (tau X hX (a + b))).hom =
                eqToHom (congrArg (proEtaleConstantRingDerivedPullback A) w.symm) ≫
                (proEtaleFrobeniusDerivedComp A
                  (X.iterateFrobenius hp (hX.2 ⊤) a) (X.iterateFrobenius hp (hX.2 ⊤) b)
                  (comp (X.iterateFrobenius hp (hX.2 ⊤) a)
                    (X.iterateFrobenius hp (hX.2 ⊤) b))).hom ≫
                Functor.whiskerLeft
                  (proEtaleConstantRingDerivedPullback A (X.iterateFrobenius hp (hX.2 ⊤) b))
                  (proEtaleFrobeniusDerivedIso A (tau X hX a)).hom ≫
                (Functor.rightUnitor _).hom ≫
                (proEtaleFrobeniusDerivedIso A (tau X hX b)).hom) ∧
          (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p),
            ∃ w : X.iterateFrobenius hp (hX.2 ⊤) 0 = 𝟙 X,
              r X hX 0 =
                (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).symm ≪≫
                  eqToIso (congrArg proEtaleBaseChange w.symm)) := by
  sorry

end AlgebraicGeometry.Scheme
