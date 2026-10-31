/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPinnedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.FiniteRootSiteComparison
public import WeilConjectures.SecSmoothPurity.FiniteNativeTatePullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

/-! # Normalized finite native Tate source comparisons

Source: blueprint `sec-smooth-purity/sk-prop-sp-purity-bc`, finite-A opening;
the normalized comparison refinement and its six proof steps in
`lem-pur-finite-native-tate-source-comparison`. No purity assertion is made.
(blueprint: lem-pur-finite-native-tate-source-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The ordinary line is the actual etale-to-pro-etale inverse image of the
published etale finite twist, in the fixed-scalar presentation of the intrinsic
comparison. In particular it is not defined by the root-comparison counit.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
@[reducible] def finiteOrdinaryTateLine (T : Scheme.{u}) (N : ℕ)
    (hA : (N : ULift.{u + 1, u} A) = 0) (m : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj
    (Scheme.finiteEtaleTateTwist T N (ULift.{u + 1, u} A) hA m)

/-- The root-site sigma pinned on local pure tensors by the existing root-site
specification. That specification determines sigma, not merely its isomorphism class.
Source: Stacks 0GLZ, 03EL; proof step 2 of the item.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateRootSigma (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1, u} A) = 0) (hT : IsUnit (N : Γ(T, ⊤))) :
    finiteOrdinaryTateLine A T N hA 1 ≅
      Scheme.finiteRootProTensor (ULift.{u + 1, u} A) N hN hA T :=
  (Scheme.finiteRootSiteComparison (ULift.{u + 1, u} A)).choose N hN hA T hT

/-- The native pure tensor a tensor z, using the actual sheaf tensor unit and the
canonical constant-scalar section. Source: proof steps 1--2, pure-pair normalization.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteNativeTatePure (T : Scheme.{u}) (N : ℕ) (W : T.ProEtᵒᵖ)
    (a : ULift.{u + 1, u} A)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T N).obj.obj W) :
    (finiteNativeTateLine A T N 1).X.obj.obj W :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (coefficient A) T) (Scheme.proEtaleRootsOfUnitySheaf T N)).app W
      ((canonicalAbelianMap A T).hom.app W
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1, u} A)))).app W a)
        ⊗ₜ[ℤ] z)

/-- Native exponent maps are scalar extension of the published power map on roots;
the maps on powers are its tensor powers, with identity on the unit.
Source: proof step 2, exponent changes.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteNativeTateExponent (T : Scheme.{u}) (N N' : ℕ) (hN : 0 < N)
    (hN' : 0 < N') (hdiv : N ∣ N') :
    (m : ℕ) → finiteNativeTateLine A T N' m ⟶ finiteNativeTateLine A T N m
  | 0 => 𝟙 _
  | 1 => (Mod.freeFunctor (condensedRingObj (coefficient A) T)).map
      (Scheme.proEtaleRootsOfUnityTransition T N N' hN hN' hdiv)
  | m + 2 => tensorHom (finiteNativeTateExponent T N N' hN hN' hdiv (m + 1))
      ((Mod.freeFunctor (condensedRingObj (coefficient A) T)).map
        (Scheme.proEtaleRootsOfUnityTransition T N N' hN hN' hdiv))

/-- The ordinary line pullback uses the site-comparison mate and the published
etale root-induced pullback, in that order. Source: proof steps 3--4.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteOrdinaryTatePull {S T : Scheme.{u}} (h : S ⟶ T) (N : ℕ) (hN : 0 < N)
    (hA : (N : ULift.{u + 1, u} A) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (hT : IsUnit (N : Γ(T, ⊤))) (m : ℕ) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).obj
      (finiteOrdinaryTateLine A T N hA m) ≅ finiteOrdinaryTateLine A S N hA m :=
  (ProEtale.comparisonCoefficientPullbackIso
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).symm.app _ ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) S).mapIso
      ((Scheme.finiteEtaleTwistPullbackData (ULift.{u + 1, u} A) N hN hA).c
        h hT hS (.ofNat m))

/-- The unit comparison for normalized heart tensorators, followed by the canonical
site inverse-image unit comparison. Source: proof step 3.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateUnit (T : Scheme.{u}) (E : Encoding A T)
    (t : (coefficientHeartEncoding A (Iso.refl _) T E).Monoidal)
    (N : ℕ) (hA : (N : ULift.{u + 1, u} A) = 0) :
    (coefficientHeartEncoding A (Iso.refl _) T E).obj
      (finiteNativeTateLine A T N 0) ≅ finiteOrdinaryTateLine A T N hA 0 :=
  letI := t
  (Functor.Monoidal.εIso (coefficientHeartEncoding A (Iso.refl _) T E)).symm ≪≫
    Functor.Monoidal.εIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T)

/-- The recursion uses precisely the normalized heart tensorators and the site
inverse-image tensorator. Source: proof step 3.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateRecursion (T : Scheme.{u}) (E : Encoding A T)
    (t : (coefficientHeartEncoding A (Iso.refl _) T E).Monoidal)
    (N : ℕ) (hA : (N : ULift.{u + 1, u} A) = 0) (m : ℕ)
    (b : (coefficientHeartEncoding A (Iso.refl _) T E).obj
      (finiteNativeTateLine A T N (m + 1)) ≅ finiteOrdinaryTateLine A T N hA (m + 1))
    (b1 : (coefficientHeartEncoding A (Iso.refl _) T E).obj
      (finiteNativeTateLine A T N 1) ≅ finiteOrdinaryTateLine A T N hA 1) :
    (coefficientHeartEncoding A (Iso.refl _) T E).obj
      (finiteNativeTateLine A T N (m + 2)) ≅ finiteOrdinaryTateLine A T N hA (m + 2) :=
  letI := t
  (Functor.Monoidal.μIso (coefficientHeartEncoding A (Iso.refl _) T E)
    (finiteNativeTateLine A T N (m + 1)) (finiteNativeTateLine A T N 1)).symm ≪≫
    tensorIso b b1 ≪≫ Functor.Monoidal.μIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T) _ _

/-- A derived tensor-source comparison, with its actual map: the pinned derived
pure-pair tensorator, then the given pinned pullback comparison in the first slot,
then the single-complex localization of b in the line slot. Source: proof step 5.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateTensorSource (T : Scheme.{u}) (E : Encoding A T)
    (t : (coefficientHeartEncoding A (Iso.refl _) T E).Monoidal)
    (L : Internal A T)
    (L0 : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (b : (coefficientHeartEncoding A (Iso.refl _) T E).obj L ≅ L0)
    (K : DerivedCategory (Internal A T))
    (K0 : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (p : (coefficientEncoding A (Iso.refl _) T E).obj K ≅ K0) :
    (coefficientEncoding A (Iso.refl _) T E).obj
      (((CondensedRing.derivedTensor (coefficient A) T).obj K).obj
        ((DerivedCategory.singleFunctor _ 0).obj L)) ≅
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj K0).obj
      ((DerivedCategory.singleFunctor _ 0).obj L0) :=
  ((CoefficientPullback.pinnedDerivedTensor A (coefficient A) (Iso.refl _) T E t).app K).app
      ((DerivedCategory.singleFunctor _ 0).obj L) ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapIso p).app _ ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj K0).mapIso
      ((CoefficientPullback.pinnedEncodingSingleIso A (coefficient A) (Iso.refl _) T E).app L
        ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso b)

/-- The shifted twisted-pullback source is the encoding shift comparison followed
by finiteTateTensorSource with the specified P_h. Both the native pullback and
Tate-line tensor occur in this construction. Source: proof step 5.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateShiftedSource (E : ∀ T : Scheme.{u}, Encoding A T)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (t : (coefficientHeartEncoding A (Iso.refl _) S (E S)).Monoidal)
    (N : ℕ) (hA : (N : ULift.{u + 1, u} A) = 0) (m : ℕ) (s : ℤ)
    (b : (coefficientHeartEncoding A (Iso.refl _) S (E S)).obj
      (finiteNativeTateLine A S N m) ≅ finiteOrdinaryTateLine A S N hA m)
    (K : DerivedCategory (Internal A T)) :=
  letI : (coefficientEncoding A (Iso.refl _) S (E S)).CommShift ℤ := by
    unfold coefficientEncoding
    infer_instance
  ((coefficientEncoding A (Iso.refl _) S (E S)).commShiftIso s).app
      (((CondensedRing.derivedTensor (coefficient A) S).obj
        ((CoefficientPullback.pull (coefficient A) h).obj K)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (finiteNativeTateLine A S N m))) ≪≫
    (shiftFunctor _ s).mapIso
      (finiteTateTensorSource A S (E S) t _ _ b _ _
        ((CoefficientPullback.pinnedPullback A (coefficient A) (Iso.refl _) E h).app K))

/-- The actual native square source map: inverse compositor, equality of the composite
scheme maps, compositor. Source: proof step 6.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateNativeSquare {X Y Y' Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (sq : f ≫ g = f' ≫ g') (K : DerivedCategory (Internal A Z)) :
    (CoefficientPullback.pull (coefficient A) f).obj
      ((CoefficientPullback.pull (coefficient A) g).obj K) ≅
    (CoefficientPullback.pull (coefficient A) f').obj
      ((CoefficientPullback.pull (coefficient A) g').obj K) :=
  (CondensedRing.leftDerivedUpperStarComp (coefficient A) f g).symm.app K ≪≫
    eqToIso (congrArg (fun h ↦ (CoefficientPullback.pull (coefficient A) h).obj K) sq) ≪≫
    (CondensedRing.leftDerivedUpperStarComp (coefficient A) f' g').app K

/-- The ordinary square source uses the published ordinary compositors, with the same
scheme-map equality. Source: proof step 6.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateOrdinarySquare {X Y Y' Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (sq : f ≫ g = f' ≫ g')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  (ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).symm.app K ≪≫
    eqToIso (congrArg (fun h ↦ (CoefficientPullback.fixedPull A h).obj K) sq) ≪≫
    (ProEtale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f' g').app K

/-- The two-step pinned comparison. Its factors are fixed definitions, not witnesses
of an existential comparison theorem. Source: proof step 6.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
def finiteTateDoublePull (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory (Internal A Z)) :=
  (CoefficientPullback.pinnedPullback A (coefficient A) (Iso.refl _) E f).app
      ((CoefficientPullback.pull (coefficient A) g).obj K) ≪≫
    (CoefficientPullback.fixedPull A f).mapIso
      ((CoefficientPullback.pinnedPullback A (coefficient A) (Iso.refl _) E g).app K)

/-- Complete normalized comparison data. Heart b's are pinned by roots, scalars, units
and recursion. Step 4 compares the independently constructed root-induced native line pullback.
The final equation compares the two twisted source routes of an arbitrary square.
Source: the item's six-step normalized comparison argument.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
structure FiniteNativeTateSourceData (ell n : ℕ) [Fact ell.Prime] where
  E : ∀ T : Scheme.{u}, Encoding A T
  tensor : ∀ T : Scheme.{u}, (coefficientHeartEncoding A (Iso.refl _) T (E T)).Monoidal
  normalized : ∀ T : Scheme.{u},
    CoefficientPullback.PinnedHeartNormalized A (coefficient A) (Iso.refl _) T (E T) (tensor T)
  b : ∀ (r : ℕ), n ≤ r → ∀ (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    (T : Scheme.{u}), IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤)) → ∀ m : ℕ,
    (coefficientHeartEncoding A (Iso.refl _) T (E T)).obj
      (finiteNativeTateLine A T (ell ^ r) m) ≅
      finiteOrdinaryTateLine A T (ell ^ r) hA m
  b_zero : ∀ (r : ℕ) (hr : n ≤ r)
    (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    (T : Scheme.{u}) (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))),
    b r hr hA T hT 0 = finiteTateUnit A T (E T) (tensor T) (ell ^ r) hA
  b_rec : ∀ (r : ℕ) (hr : n ≤ r)
    (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    (T : Scheme.{u}) (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))) (m : ℕ),
    b r hr hA T hT (m + 2) = finiteTateRecursion A T (E T) (tensor T) (ell ^ r) hA m
      (b r hr hA T hT (m + 1)) (b r hr hA T hT 1)
  b_root : ∀ (r : ℕ) (hr : n ≤ r)
    (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    (T : Scheme.{u}) (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))) (W : T.ProEtᵒᵖ)
    (a : ULift.{u + 1, u} A)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (ell ^ r)).obj.obj W),
    (b r hr hA T hT 1).hom.hom.app W
      ((((CoefficientPullback.pinnedSectionsIso A (coefficient A) (Iso.refl _) T (E T)).inv.app
        (finiteNativeTateLine A T (ell ^ r) 1)).hom.app W).hom
          (finiteNativeTatePure A T (ell ^ r) W a z)) =
    (finiteTateRootSigma A T (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r) hA hT).inv.hom.app W
      (Scheme.finiteRootProGenerator (ULift.{u + 1, u} A) (ell ^ r)
        (pow_pos (Fact.out : ell.Prime).pos r) hA T W a z)
  exponent : ∀ (r r' : ℕ) (hr : n ≤ r) (hrr : r ≤ r')
    (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    (hA' : ((ell ^ r' : ℕ) : ULift.{u + 1, u} A) = 0)
    (T : Scheme.{u}) (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤)))
    (hT' : IsUnit ((ell ^ r' : ℕ) : Γ(T, ⊤))),
    ∃ (q : T.rootsOfUnitySheaf (ell ^ r') ⟶ T.rootsOfUnitySheaf (ell ^ r))
      (t : ∀ m : ℕ,
        Scheme.finiteEtaleTateTwist T (ell ^ r') (ULift.{u + 1, u} A) hA' m ⟶
        Scheme.finiteEtaleTateTwist T (ell ^ r) (ULift.{u + 1, u} A) hA m),
    q ≫ kernel.ι ((ell ^ r) • 𝟙 T.gmSheaf) =
      (ell ^ r' / ell ^ r) • kernel.ι ((ell ^ r') • 𝟙 T.gmSheaf) ∧
    (∀ (W : T.Etaleᵒᵖ) (a : ULift.{u + 1, u} A)
      (z : (T.rootsOfUnitySheaf (ell ^ r')).obj.obj W),
      (t 1).hom.app W
        (Scheme.finiteEtaleTateOneGenerator (ULift.{u + 1, u} A) (ell ^ r') T hA' W a z) =
      Scheme.finiteEtaleTateOneGenerator (ULift.{u + 1, u} A) (ell ^ r) T hA W a
        (q.hom.app W z)) ∧
    t 0 = 𝟙 _ ∧ (∀ m : ℕ, t (m + 2) = tensorHom (t (m + 1)) (t 1)) ∧
    (∀ m : ℕ,
      (coefficientHeartEncoding A (Iso.refl _) T (E T)).map
        (finiteNativeTateExponent A T (ell ^ r) (ell ^ r')
          (pow_pos (Fact.out : ell.Prime).pos r) (pow_pos (Fact.out : ell.Prime).pos r')
          (pow_dvd_pow ell hrr) m) ≫ (b r hr hA T hT m).hom =
      (b r' (hr.trans hrr) hA' T hT' m).hom ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).map (t m))
  nativePull_isIso : ∀ (r : ℕ) (_hr : n ≤ r)
    (_hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (_hS : IsUnit ((ell ^ r : ℕ) : Γ(S, ⊤)))
    (_hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))) (m : ℕ),
    IsIso (finiteNativeTatePull A h (ell ^ r) m)
  step4 : ∀ (r : ℕ) (hr : n ≤ r)
    (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    {S T : Scheme.{u}} (h : S ⟶ T)
    (hS : IsUnit ((ell ^ r : ℕ) : Γ(S, ⊤)))
    (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))) (m : ℕ),
    (coefficientHeartEncoding A (Iso.refl _) S (E S)).map
        (finiteNativeTatePull A h (ell ^ r) m) ≫ (b r hr hA S hS m).hom =
      (CoefficientPullback.pinnedHeartPull A (coefficient A) (Iso.refl _) h (E S) (E T)).hom.app
        (finiteNativeTateLine A T (ell ^ r) m) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).map (b r hr hA T hT m).hom ≫
      (finiteOrdinaryTatePull A h (ell ^ r) (pow_pos (Fact.out : ell.Prime).pos r)
        hA hS hT m).hom
  tensor_pullback : ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    Adjunction.ComparisonCompatible
      (CoefficientPullback.pinnedPullback A (coefficient A) (Iso.refl _) E h).symm
      (CondensedRing.leftDerivedUpperStarTensor (coefficient A) h)
      (ProEtale.leftDerivedUpperStarTensorComparison
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h)
      (CoefficientPullback.pinnedDerivedTensor A (coefficient A) (Iso.refl _) S (E S) (tensor S))
      (CoefficientPullback.pinnedDerivedTensor A (coefficient A) (Iso.refl _) T (E T) (tensor T))
  pullback_shift : ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    CoefficientPullback.PinnedPullbackCommShift A (coefficient A) (Iso.refl _) E h
  square : ∀ (r : ℕ) (hr : n ≤ r)
    (hA : ((ell ^ r : ℕ) : ULift.{u + 1, u} A) = 0)
    {X Y Y' Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (sq : f ≫ g = f' ≫ g') (hX : IsUnit ((ell ^ r : ℕ) : Γ(X, ⊤)))
    (K : DerivedCategory (Internal A Z)) (m : ℕ) (s : ℤ),
    (shiftFunctor _ s).map
      ((coefficientEncoding A (Iso.refl _) X (E X)).map
        (((CondensedRing.derivedTensor (coefficient A) X).map
          (finiteTateNativeSquare A f g f' g' sq K).hom).app
            ((DerivedCategory.singleFunctor _ 0).obj (finiteNativeTateLine A X (ell ^ r) m))) ≫
        (finiteTateTensorSource A X (E X) (tensor X) _ _ (b r hr hA X hX m) _ _
          (finiteTateDoublePull A E f' g' K)).hom) =
    (shiftFunctor _ s).map
      ((finiteTateTensorSource A X (E X) (tensor X) _ _ (b r hr hA X hX m) _ _
          (finiteTateDoublePull A E f g K)).hom ≫
        ((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).map
          (finiteTateOrdinarySquare A f g f' g' sq
            ((coefficientEncoding A (Iso.refl _) Z (E Z)).obj K)).hom).app
              ((DerivedCategory.singleFunctor _ 0).obj (finiteOrdinaryTateLine A X (ell ^ r) hA m)))

/-- The canonical normalized native and ordinary finite Tate sources agree.
Source: the finite-A source identification and the six-step proof of
`lem-pur-finite-native-tate-source-comparison`.
Proof: use the constant-scalar-normalized Encoding and pure-pair heart tensorators.
The root-site sigma identifies the free internal root tensor with the pulled-back
etale line by the identity on local pure tensors. The unit and tensor recursion
extend this map to every nonnegative twist. Power maps commute on root sections
and keep the coefficient scalar unchanged, giving the exponent equations.
The inverse-image mate is the pinned heart comparison; checking its adjunct on
root sections gives Step 4. Localize termwise and apply pinnedDerivedTensor to
pullback K and the line; this is finiteTateTensorSource with pinnedPullback in the
first slot. The tensor/pullback equation identifies it with the comparison obtained
by first pulling back the twist. For a square, apply the pinned compositor equation
to both factorizations and cancel the common composite comparison. Insert the
Step-4 line equation and apply the shift functor; its termwise exact comparison
has identical differential signs on both routes. No purity map is used.
(blueprint: lem-pur-finite-native-tate-source-comparison). -/
theorem finiteNativeTateSourceComparison (ell : ℕ) [Fact ell.Prime]
    (n : ℕ) (hn : 0 < n) (hA : (ell ^ n : A) = 0) :
    Nonempty (FiniteNativeTateSourceData A ell n) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
