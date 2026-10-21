/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.RingedDerivedSliceLocalization
public import Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedSliceDerivedAdjunction
import Sheaf.Paper.RingedSliceDerivedComparisons

/-!
# Normalization of the derived pullback comparison for a ringed slice

Source: Stacks Project, Modules on Sites, Tag 04J0; Cohomology on Sites,
Tags 07A6, 07A7 and 08FI
(blueprint: lem-weil-pbc-ringed-slice-pullback-mate-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary localization comparison applied termwise to a complex. Its components
are the specified inverse mate of the sectionwise identity, not a chosen isomorphism.
Source: Stacks Tag 04J0
(blueprint: lem-weil-pbc-ringed-slice-pullback-mate-normalization). -/
def ringedSlicePullbackComplexMap (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ((ringedSliceModulePullback (Over.post (X := V) u)
        (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).obj
        ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ⟶
      (CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj
        (((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P) where
  f n := (sliceModulePullbackMap u (ringedSiteModuleMap u a) V).app (P.X n)
  comm' i j _ :=
    ((sliceModulePullbackMap u (ringedSiteModuleMap u a) V).naturality (P.d i j)).symm

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical derived slice comparison is Q of the ordinary comparison on every
flat-term K-flat representative, and its direct-image comparison is the exchange mate.
The hypothesis `hnormal` specifies the canonical right-derived comparison on all
complexes, exactly as in `ringedDerivedSliceLocalization`; `d.lambda` is theta in
this statement's orientation. The four factors in the representative equation retain
both restriction factorizations and both derived pullback model comparisons.
Source: Stacks Tags 04J0, 07A6, 07A7 and 08FI
(blueprint: lem-weil-pbc-ringed-slice-pullback-mate-normalization).

Proof:
1. The ordinary comparison is the inverse mate of the sectionwise identity. Its
local transpose is restriction of the global ordinary unit followed by that identity
(lem-weil-pbc-localize-ringed-site-morphism and
lem-weil-pbc-slice-module-pullback-isIso). Apply this equation degreewise.
2. The two RingedSliceDerivedImage presentations normalize the derived Hom
bijections against the ordinary complex adjunctions. The canonical beta satisfies
hnormal on every complex (lem-weil-pbc-ringed-slice-derived-image-exists and
lem-weil-pbc-ringed-slice-derived-comparisons).
3. Restriction preserves flat-term K-flat complexes by the localization case of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The two epsilon components are
isomorphisms by lem-weil-pbc-ringed-topoi-derived-pullback and derived uniqueness.
4. Specialize global Hom normalization to the identity: the derived unit followed
by R(epsilon) is Q of the ordinary unit followed by eta. The unit equation of d
identifies the transpose of theta with restriction of the derived unit followed by beta.
5. Compute the local derived transpose of theta followed by restricted epsilon and
the target restriction factorization. Naturality of beta, the normalized global unit,
and hnormal at the actual complex f*P give Q of the restricted ordinary unit followed
by the ordinary direct-image identity and the local eta. No K-injectivity of f*P is used.
6. Local Hom normalization and step 1 give the same transpose for local epsilon
followed by Q(sigma). Naturality of the source restriction factorization inserts its
image under the local derived pullback. Injectivity of the local Hom bijection gives
the displayed equality; cancellation of the model isomorphisms gives theta = Q(sigma).
7. Flat-term K-flat resolutions (lem-pc-kflat-resolution) and naturality along their
inverted quasi-isomorphisms determine theta everywhere, independently of resolution.
The counit equation of d says beta is the transpose of theta followed by the restricted
global counit. This is the exchange mate (def-weil-pbc-adjunction-mate) and precisely
the base change map of Stacks 07A7. -/
theorem ringedSlicePullbackMateNormalization
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u a V))
    (d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
      (ringedSliceRestriction.{u, w} R V) (ringedSliceRestriction.{u, w} S (u.obj V)))
    (hnormal : ∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
      (ringedSliceRestriction.{u, w} R V).map
          (X := DerivedCategory.Q.{w}.obj
            (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I))
          (Y := e.right.obj (DerivedCategory.Q.{w}.obj I)) (e.eta.app I) ≫
        d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
        l.right.map
          (X := (ringedSliceRestriction.{u, w} S (u.obj V)).obj (DerivedCategory.Q.{w}.obj I))
          (Y := DerivedCategory.Q.{w}.obj
            ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
          ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
      (ringedSliceRestrictionFactors.{u, w} R V).hom.app
          (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
        l.eta.app ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u}
          J S (u.obj V)).obj I)) :
    (∀ (P : CochainComplex (SheafOfModules.{u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ n : ℤ, (P.X n).IsFlat) →
      CochainComplex.IsKFlatIndependentCoefficients
          ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ∧
        (∀ n : ℤ, IsFlat (R := R.over V)
          (((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P).X n)) ∧
        IsIso (e.epsilon.app P) ∧
        IsIso (l.epsilon.app
          ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P)) ∧
        d.lambda.hom.app (DerivedCategory.Q.{w}.obj P) ≫
            (ringedSliceRestriction.{u, w} S (u.obj V)).map (e.epsilon.app P) ≫
            (ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app
              (((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P) =
          l.left.map ((ringedSliceRestrictionFactors.{u, w} R V).hom.app P) ≫
            l.epsilon.app
              ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ≫
            DerivedCategory.Q.{w}.map (ringedSlicePullbackComplexMap u a V P)) ∧
      (mateEquiv e.adjunction l.adjunction
        (TwoSquare.mk _ _ _ _ d.lambda.hom)).natTrans = d.beta.hom ∧
      ∀ M : ringedSiteDerived.{u, w} S,
        l.adjunction.homEquiv _ _
          (d.lambda.hom.app (e.right.obj M) ≫
            (ringedSliceRestriction.{u, w} S (u.obj V)).map (e.adjunction.counit.app M)) =
          d.beta.hom.app M := by
  sorry

end SheafOfModules
