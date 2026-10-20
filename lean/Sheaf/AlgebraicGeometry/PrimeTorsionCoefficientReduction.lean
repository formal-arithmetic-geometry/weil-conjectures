/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionCompat
public import Sheaf.AlgebraicGeometry.PunctualTensorBaseChange
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Paper.EtaleKFlatCriteria
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Prime coefficient tensor comparison constructions

Source: Stacks Project, Tags 03EK, 06YU and 0F1J, coefficient reduction
(blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor


namespace AlgebraicGeometry.Etale

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- The published counit-adjoint punctual comparison, with its functor endpoints explicit.
Source: Stacks, Tag 0F1J (blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction). -/
abbrev primeTensorComparison (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y S' T : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (sq : CommSq e h g f')
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (primeTensorSource Λ p f' g E).obj F ⟶ (primeTensorTarget Λ p h e E).obj F :=
  punctualTensorBaseChangeMap Λ p h e f' g sq
    ((primeSingle Λ X).obj E) ((primeSingle Λ T).obj F)

/-- Compute the composite of two exact inverse images on a sheaf in degree zero.
Source: Stacks, Tags 03EK, 06YU and 0F1J
(blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction). -/
def primeDoublePullbackSingleIso (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X')
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (primePullback Λ h).obj ((primePullback Λ p).obj ((primeSingle Λ X).obj E)) ≅
      (primeSingle Λ Y).obj (primePulledSheaf Λ h (primePulledSheaf Λ p E)) :=
  (primePullback Λ h).mapIso (primePullbackSingleIso Λ p E) ≪≫
    primePullbackSingleIso Λ h (primePulledSheaf Λ p E)

/-- The canonical direct-image coefficient comparison, including its degree-zero input.
Source: Stacks, Tag 0D6J (blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction). -/
def primeDirectImageRestriction (φ : A →+* B) {T S : Scheme.{u}} (g : T ⟶ S)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (Sheaf.derivedRestrictScalars S.smallEtaleTopology φ).obj
        ((primePushforward B g).obj ((primeSingle B T).obj F)) ⟶
      (primePushforward A g).obj ((primeSingle A T).obj
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj F)) :=
  (scalarRestrictionDirectImageMap φ g).app ((primeSingle B T).obj F) ≫
    (primePushforward A g).map
      (((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).hom.app F)

/-- Tensor coefficient comparison on Y before taking the direct image along h.
Source: Stacks, Tag 0F1J (blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction). -/
def primeTargetTensorRestriction (φ : A →+* B)
    {X X' Y T : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Φ : PrimeTensorCoefficientIso φ Y
      ((primePullback A h).obj ((primePullback A p).obj ((primeSingle A X).obj E)))
      ((primePullback B h).obj ((primePullback B p).obj ((primeSingle B X).obj
        ((primeCoefficientQuotient φ X).obj E)))))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
    ((primePullback A h).obj ((primePullback A p).obj ((primeSingle A X).obj E)))).map
    ((primePullback A e).map
      (((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
        0).inv.app F) ≫
      (scalarRestrictionPullbackIso φ e).hom.app ((primeSingle B T).obj F)) ≫
    Φ.hom.app ((primePullback B e).obj ((primeSingle B T).obj F))

/-- Canonical normalization for the two displayed coefficient isomorphisms.
The source equation uses the direct-image mate for g. The target equation uses the
same mate for h. The intervening coefficient maps are the canonical quotient tensor
maps, both after p and after h followed by p.
Source: Stacks, Tag 0F1J (blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction). -/
def PrimePunctualCoefficientNormalized (φ : A →+* B)
    {X X' Y S' T : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S')
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (a : (Sheaf.restrictScalars T.smallEtaleTopology φ ⋙ primeTensorSource A p f' g E) ≅
      (primeTensorSource B p f' g ((primeCoefficientQuotient φ X).obj E) ⋙
        Sheaf.derivedRestrictScalars X'.smallEtaleTopology φ))
    (b : (Sheaf.restrictScalars T.smallEtaleTopology φ ⋙ primeTensorTarget A p h e E) ≅
      (primeTensorTarget B p h e ((primeCoefficientQuotient φ X).obj E) ⋙
        Sheaf.derivedRestrictScalars X'.smallEtaleTopology φ)) : Prop :=
  ∃ (Φp : PrimeTensorCoefficientIso φ X'
      ((primePullback A p).obj ((primeSingle A X).obj E))
      ((primePullback B p).obj ((primeSingle B X).obj
        ((primeCoefficientQuotient φ X).obj E))))
    (Φhp : PrimeTensorCoefficientIso φ Y
      ((primePullback A h).obj ((primePullback A p).obj ((primeSingle A X).obj E)))
      ((primePullback B h).obj ((primePullback B p).obj ((primeSingle B X).obj
        ((primeCoefficientQuotient φ X).obj E))))),
    PrimeTensorCoefficientNormalized φ X'
      (primePulledSheaf A p E)
      (primePulledSheaf B p ((primeCoefficientQuotient φ X).obj E))
      (primePullbackCoefficientMap φ p E ((primeCoefficientQuotient φ X).obj E)
        ((primeCoefficientQuotientUnit φ X).app E)) _ _
      (primePullbackSingleIso A p E)
      (primePullbackSingleIso B p ((primeCoefficientQuotient φ X).obj E)) Φp ∧
    PrimeTensorCoefficientNormalized φ Y
      (primePulledSheaf A h (primePulledSheaf A p E))
      (primePulledSheaf B h (primePulledSheaf B p ((primeCoefficientQuotient φ X).obj E)))
      (primePullbackCoefficientMap φ h (primePulledSheaf A p E)
        (primePulledSheaf B p ((primeCoefficientQuotient φ X).obj E))
        (primePullbackCoefficientMap φ p E ((primeCoefficientQuotient φ X).obj E)
          ((primeCoefficientQuotientUnit φ X).app E))) _ _
      (primeDoublePullbackSingleIso A p h E)
      (primeDoublePullbackSingleIso B p h ((primeCoefficientQuotient φ X).obj E)) Φhp ∧
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B),
      ((derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((primePullback A p).obj ((primeSingle A X).obj E))).map
          ((primePullback A f').map (primeDirectImageRestriction φ g F)) ≫ a.hom.app F =
      ((derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((primePullback A p).obj ((primeSingle A X).obj E))).map
          ((scalarRestrictionPullbackIso φ f').hom.app
            ((primePushforward B g).obj ((primeSingle B T).obj F))) ≫
        Φp.hom.app ((primePullback B f').obj
          ((primePushforward B g).obj ((primeSingle B T).obj F)))) ∧
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B),
      b.hom.app F ≫ (scalarRestrictionDirectImageMap φ h).app
        (((derivedTensor (ModuleCat.{u + 1} B) Y).obj
          ((primePullback B h).obj ((primePullback B p).obj ((primeSingle B X).obj
            ((primeCoefficientQuotient φ X).obj E))))).obj
          ((primePullback B e).obj ((primeSingle B T).obj F))) =
        (primePushforward A h).map (primeTargetTensorRestriction φ p h e E Φhp F))

/-- The two coefficient isomorphisms, their joint naturality, and their compatibility
with the actual counit-adjoint comparison. The ordinary coefficient identification
is the constructed arrow primeCoefficientTensorMap, fixing its pure-tensor rule.
Source: Stacks, Tag 0F1J (blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction). -/
def PrimeTorsionCoefficientReduction (n ell : ℕ) (hd : ell ∣ n)
    {X X' Y S' T : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (sq : CommSq e h g f') : Prop :=
  (∀ E : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))), ObjectProperty.flat E →
    ObjectProperty.flat ((primeCoefficientQuotient (primeCoefficientHom n ell hd) X).obj E)) ∧
  ∃ (sourceIso : ∀ (E : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (_ : ObjectProperty.flat E),
    (Sheaf.restrictScalars T.smallEtaleTopology (primeCoefficientHom n ell hd) ⋙
        primeTensorSource (ULift.{u + 1} (ZMod n)) p f' g E) ≅
      (primeTensorSource (ULift.{u + 1} (ZMod ell)) p f' g
          ((primeCoefficientQuotient (primeCoefficientHom n ell hd) X).obj E) ⋙
        Sheaf.derivedRestrictScalars X'.smallEtaleTopology (primeCoefficientHom n ell hd)))
    (targetIso : ∀ (E : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (_ : ObjectProperty.flat E),
    (Sheaf.restrictScalars T.smallEtaleTopology (primeCoefficientHom n ell hd) ⋙
        primeTensorTarget (ULift.{u + 1} (ZMod n)) p h e E) ≅
      (primeTensorTarget (ULift.{u + 1} (ZMod ell)) p h e
          ((primeCoefficientQuotient (primeCoefficientHom n ell hd) X).obj E) ⋙
        Sheaf.derivedRestrictScalars X'.smallEtaleTopology (primeCoefficientHom n ell hd))),
    (∀ (E E' : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
      (hE : ObjectProperty.flat E) (hE' : ObjectProperty.flat E') (δ : E ⟶ E')
      (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))),
    (primeTensorSourceMap (ULift.{u + 1} (ZMod n)) p f' g δ).app
        ((Sheaf.restrictScalars T.smallEtaleTopology (primeCoefficientHom n ell hd)).obj F) ≫
        (sourceIso E' hE').hom.app F =
      (sourceIso E hE).hom.app F ≫
        (Sheaf.derivedRestrictScalars X'.smallEtaleTopology
          (primeCoefficientHom n ell hd)).map
          ((primeTensorSourceMap (ULift.{u + 1} (ZMod ell)) p f' g
            ((primeCoefficientQuotient (primeCoefficientHom n ell hd) X).map δ)).app F)) ∧
    (∀ (E E' : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
      (hE : ObjectProperty.flat E) (hE' : ObjectProperty.flat E') (δ : E ⟶ E')
      (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))),
    (primeTensorTargetMap (ULift.{u + 1} (ZMod n)) p h e δ).app
        ((Sheaf.restrictScalars T.smallEtaleTopology (primeCoefficientHom n ell hd)).obj F) ≫
        (targetIso E' hE').hom.app F =
      (targetIso E hE).hom.app F ≫
        (Sheaf.derivedRestrictScalars X'.smallEtaleTopology
          (primeCoefficientHom n ell hd)).map
          ((primeTensorTargetMap (ULift.{u + 1} (ZMod ell)) p h e
            ((primeCoefficientQuotient (primeCoefficientHom n ell hd) X).map δ)).app F)) ∧
    (∀ (E : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (hE : ObjectProperty.flat E),
      PrimePunctualCoefficientNormalized (primeCoefficientHom n ell hd) p h e f' g E
        (sourceIso E hE) (targetIso E hE)) ∧
    (∀ (E : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (hE : ObjectProperty.flat E)
      (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))),
    primeTensorComparison (ULift.{u + 1} (ZMod n)) p h e f' g sq E
        ((Sheaf.restrictScalars T.smallEtaleTopology (primeCoefficientHom n ell hd)).obj F) ≫
        (targetIso E hE).hom.app F =
      (sourceIso E hE).hom.app F ≫
        (Sheaf.derivedRestrictScalars X'.smallEtaleTopology
          (primeCoefficientHom n ell hd)).map
          (primeTensorComparison (ULift.{u + 1} (ZMod ell)) p h e f' g sq
            ((primeCoefficientQuotient (primeCoefficientHom n ell hd) X).obj E) F))

/-- Prime-torsion coefficient reduction, including the coefficient square for the comparison.
Source: Stacks Project, Tag 0F1J, prime-torsion paragraph
(blueprint: lem-kun-0f1j-prime-torsion-coefficient-reduction).

Proof plan:
1. Sheafify the mutually inverse balanced maps x tensor y maps to bar x tensor y and
bar x tensor y maps to x tensor y. Local lifts differ by ell z, whose tensor with y
vanishes. The formulas respect restrictions and both variables. This is precisely
primeCoefficientTensorMap, constructed from the quotient unit and lax tensor map.
2. Restriction of scalars is exact and reflects exactness on underlying abelian
sheaves. Apply the preceding tensor identity to short exact sequences: flatness of
E therefore gives flatness of its quotient, without flatness of R to k.
3. Exact étale inverse image preserves flatness and the quotient cokernel, for p
and for p composed with h; use flat module pullback and constant-ring inverse image.
4. These flat sheaves in degree zero are K-flat. Apply the ordinary coefficient
isomorphism degree by degree to any k-complex. Naturality makes this a chain
isomorphism and lets it descend through roofs, independently of the model.
5. For the source, use the canonical bounded-below direct-image coefficient
comparison for g, then inverse-image comparison for f', then Step 4.
6. For the target first use Step 4 on Y, then the direct-image comparison for h.
All direct-image inputs are bounded below; no arbitrary R-injective model is
claimed to be degreewise killed by ell.
7. Transpose the punctual comparison along h inverse image. It is the square and
tensor identifications followed by 1 tensor e inverse image of the counit for g.
The coefficient counit identity makes both adjoints equal after Step 4.
8. Naturality of the unit for h and the coefficient unit identity transpose this
equality back to comparison. Joint naturality follows from all the constructions.
The relevant nodes are the K-flat criteria, inverse-image monoidality, canonical
scalar comparisons, scalar adjunction identities, module-sheaf forgetful exactness,
flat module pullback, site composition and exact constant-coefficient inverse image.
-/
theorem primeTorsionCoefficientReduction
    (K : Type u) [Field K] (n ell : ℕ) (hn : 1 ≤ n) (hnK : IsUnit (n : K))
    (hell : Nat.Prime ell) (hd : ell ∣ n)
    {X X' Y S' T : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of K)) (aS : S' ⟶ Spec (CommRingCat.of K))
    (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (left : IsPullback p f' aX aS) (right : IsPullback e h g f')
    [QuasiCompact g] [QuasiSeparated g] :
    PrimeTorsionCoefficientReduction n ell hd p h e f' g right.toCommSq :=
  sorry

end AlgebraicGeometry.Etale
