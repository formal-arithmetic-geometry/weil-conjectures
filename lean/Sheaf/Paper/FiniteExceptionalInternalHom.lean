/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.SmoothPurity.InternalAdjunctionEvaluation
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Mathlib.CategoryTheory.Shift.Adjunction
import Sheaf.Paper.ProjectionMateExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-! # Finite exceptional internal adjunction

Source: ILO, Expose XVII, Proposition 5.4.1, pp. 291 and 293
(blueprint: lem-per-finite-exceptional-internal-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The proper normalization of compact direct image for a finite map.
Source: ILO XVII 5.4.1, p. 291 (blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalSupportIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f] :
    R(f)_![ModuleCat A] ≅ R((f)_*[ModuleCat A]) :=
  (rightDerivedLowerShriekIso A (Compactification.ofIsProper f)).symm ≪≫
    unboundedEtaleProperCandidateIso A f (Compactification.ofIsProper f)

/-- The finite direct-image adjunction, with the proper-normalized counit.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f] :
    R((f)_*[ModuleCat A]) ⊣ R(f)^![ModuleCat A] :=
  (rightDerivedUpperShriekAdjunction (ModuleCat A) f).ofNatIsoLeft
    (finiteExceptionalSupportIso A f)

/-- The canonical finite internal adjunction is the ambient canonical isomorphism,
transported by proper coincidence in its first Hom argument.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalInternalHomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f] :
    RHom(T)[ModuleCat A] ⋙
        (Functor.whiskeringLeft _ _ _).obj R(f)^![ModuleCat A] ⋙
          (Functor.whiskeringRight _ _ _).obj R((f)_*[ModuleCat A]) ≅
      (R((f)_*[ModuleCat A])).op ⋙ RHom(S)[ModuleCat A] :=
  derivedHomRightDerivedLowerShriekIsoOfFinite A f ≪≫
    (Functor.isoWhiskerRight (NatIso.op (finiteExceptionalSupportIso A f))
      (derivedHom (ModuleCat A) S)).symm

/-- The isomorphism on bounded-below inputs, valued in the unbounded category.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalInternalHomPlusIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A)))
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A))) :
    (R((f)_*[ModuleCat A])).obj
        (((RHom(T)[ModuleCat A]).obj (op M.obj)).obj ((R(f)^![ModuleCat A]).obj N.obj)) ≅
      ((RHom(S)[ModuleCat A]).obj (op ((R((f)_*[ModuleCat A])).obj M.obj))).obj N.obj :=
  ((finiteExceptionalInternalHomIso A f).app (op M.obj)).app N.obj

/-- The ambient right adjoint preserves bounded-below objects, so its adjunction
restricts to the strictly full subcategories D⁺, with the same counit.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (steps 1--3): finite direct image is exact (finite-direct-image-exact), hence
has upper amplitude zero. Apply upper-shriek-bounded-below-from-amplitude; restrict
its Hom bijection to the strictly full D⁺ subcategories. Unique-right-adjoint
identifies any independently chosen bounded-below adjoint, compatibly with counits. -/
theorem finiteExceptionalInternalHom_boundedBelow
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian S] [CompactSpace S]
    (N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (hN : DerivedCategory.TStructure.t.plus N) :
    DerivedCategory.TStructure.t.plus ((R(f)^![ModuleCat A]).obj N) := by
  sorry

/-- Evaluation--counit normalization of the finite internal adjunction.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (step 4): apply internal-adjunction-evaluation to the canonical ambient
isomorphism, then transport its first Hom argument and its exceptional counit
by the proper normalization. The projection factor is transported by the same
normalization, so all inserted comparison inverses cancel. -/
theorem finiteExceptionalInternalHom_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A)))
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶ (R((f)_*[ModuleCat A])).obj
      (((RHom(T)[ModuleCat A]).obj (op M.obj)).obj ((R(f)^![ModuleCat A]).obj N.obj))) :
    ((derivedTensorHomAdjunction (ModuleCat A)
        ((R((f)_*[ModuleCat A])).obj M.obj)).homEquiv Q N.obj).symm
      (h ≫ (finiteExceptionalInternalHomPlusIso A f M N).hom) =
      (((-⊗ᴸ-(S)[ModuleCat A]).map ((finiteExceptionalSupportIso A f).inv.app M.obj)).app
        Q) ≫
      ((projectionMap (ModuleCat A) f).app M.obj).app Q ≫
      (finiteExceptionalSupportIso A f).hom.app
        (((-⊗ᴸ-(T)[ModuleCat A]).obj M.obj).obj (L((f)^*[ModuleCat A]).obj Q)) ≫
      (R((f)_*[ModuleCat A])).map
        (((derivedTensorHomAdjunction (ModuleCat A) M.obj).homEquiv
          (L((f)^*[ModuleCat A]).obj Q) ((R(f)^![ModuleCat A]).obj N.obj)).symm
          (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv Q _).symm h)) ≫
      (finiteExceptionalAdjunction A f).counit.app N.obj := by
  sorry

/-- The finite internal adjunction commutes with shifts of its second input.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (step 5): the ambient internal adjunction is the conjugate of the projection
map, which commutes with shifts. The proper comparison is termwise and commutes
with shifts as well. Transport through it; uniqueness of the unit/counit-compatible
right-adjoint shift structures fixes the exceptional shift comparison. -/
theorem finiteExceptionalInternalHom_commShift
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A))) :
    NatTrans.CommShift
      (F₁ := (R(f)^![ModuleCat A] ⋙ (RHom(T)[ModuleCat A]).obj (op M.obj)) ⋙
        R((f)_*[ModuleCat A]))
      (F₂ := (RHom(S)[ModuleCat A]).obj (op ((R((f)_*[ModuleCat A])).obj M.obj)))
      ((finiteExceptionalInternalHomIso A f).app (op M.obj)).hom ℤ := by
  sorry

/-- The unit specialization: with `M = A_T` the finite internal adjunction identifies
`RHom(f_*A_T, N)` with `f_*f^!N`. It is the inverse of the canonical isomorphism at the
derived tensor unit `A_T`, followed by the direct image of the unit identification
`RHom(A_T, K) ≅ K`, the tensor--Hom conjugate of the derived left unitor
`A_T ⊗ᴸ K ≅ K`; no unnormalized isomorphism is chosen.
Source: ILO XVII 5.4.1, p. 291
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (step 11): represent the exceptional image by a K-injective complex I.
Only the degree-zero term of the constant unit contributes to Hom(A,I).
Evaluation at 1 identifies its terms with I, with differential d_I; this is the
conjugate of the left unitor. Apply finiteExceptionalInternalHomIso to the unit and
invert its direction. -/
def finiteExceptionalInternalHom_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A))) :
    ((RHom(S)[ModuleCat A]).obj (op ((R((f)_*[ModuleCat A])).obj (𝟙_ _)))).obj N.obj ≅
      (R((f)_*[ModuleCat A])).obj ((R(f)^![ModuleCat A]).obj N.obj) :=
  (((finiteExceptionalInternalHomIso A f).app (op (𝟙_ _))).app N.obj).symm ≪≫
    (R((f)_*[ModuleCat A])).mapIso
      ((conjugateIsoEquiv (derivedTensorHomAdjunction (ModuleCat A) (𝟙_ _)) Adjunction.id
        (derivedTensorLeftUnitorNatIso (ModuleCat A) T).symm).app
          ((R(f)^![ModuleCat A]).obj N.obj))

/-- The right-adjoint compositor is the counit-compatible mate of ordinary direct-image
composition, not an unnormalized choice of an isomorphism.
Source: ILO XVII 5.4.1, p. 293
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalCompIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T S : Scheme.{u}} (g : V ⟶ T) (f : T ⟶ S) [IsFinite g] [IsFinite f] :
    R(f)^![ModuleCat A] ⋙ R(g)^![ModuleCat A] ≅ R(g ≫ f)^![ModuleCat A] :=
  conjugateIsoEquiv ((finiteExceptionalAdjunction A g).comp (finiteExceptionalAdjunction A f))
    (finiteExceptionalAdjunction A (g ≫ f)) (rightDerivedLowerStarComp (ModuleCat A) g f).symm

/-- Composition compatibility of the internal adjunction.
Source: ILO XVII 5.4.1, p. 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (steps 9--10): the composite exceptional counit is ε_f f_*(ε_g).
The two successive counit-defined projection factors equal the projection for fg:
transpose them by ordinary pullback/direct image and apply mate-pasting to the
composite ordinary counit. Transpose by tensor--Hom to obtain the displayed square. -/
theorem finiteExceptionalInternalHom_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T S : Scheme.{u}} (g : V ⟶ T) (f : T ⟶ S) [IsFinite g] [IsFinite f]
    [IsLocallyNoetherian V] [CompactSpace V] [IsLocallyNoetherian T] [CompactSpace T]
    [IsLocallyNoetherian S] [CompactSpace S]
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat A)))
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A))) :
    (rightDerivedLowerStarComp (ModuleCat A) g f).hom.app
        (((RHom(V)[ModuleCat A]).obj (op L.obj)).obj
          ((R(g)^![ModuleCat A]).obj ((R(f)^![ModuleCat A]).obj N.obj))) ≫
      (R((g ≫ f)_*[ModuleCat A])).map
        (((RHom(V)[ModuleCat A]).obj (op L.obj)).map
          ((finiteExceptionalCompIso A g f).hom.app N.obj)) ≫
      (finiteExceptionalInternalHomPlusIso A (g ≫ f) L N).hom =
      (R((f)_*[ModuleCat A])).map
        ((((finiteExceptionalInternalHomIso A g).app (op L.obj)).app
          ((R(f)^![ModuleCat A]).obj N.obj)).hom) ≫
      (((finiteExceptionalInternalHomIso A f).app
        (op ((R((g)_*[ModuleCat A])).obj L.obj))).app N.obj).hom ≫
      ((RHom(S)[ModuleCat A]).map
        (op ((rightDerivedLowerStarComp (ModuleCat A) g f).inv.app L.obj))).app N.obj := by
  sorry

/-- The counit-induced map corresponds to exceptional pullback of morphisms.
Source: ILO XVII 5.4.1, p. 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (step 12): naturality of ε_g at a rewrites f_*(ε_g) followed by f_*a
as f_*g_*g^!a followed by f_*ε_g. The pasted counit is the composite-adjunction
counit (step 9). Applying tensor--Hom transposition gives the same assertion for
internal maps, by the evaluation formula of step 4 and mate-pasting. -/
theorem finiteExceptionalInternalHom_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T S : Scheme.{u}} (g : V ⟶ T) (f : T ⟶ S) [IsFinite g] [IsFinite f]
    [IsLocallyNoetherian V] [CompactSpace V] [IsLocallyNoetherian T] [CompactSpace T]
    [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A)))
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (a : M.obj ⟶ (R(f)^![ModuleCat A]).obj N.obj) :
    (R((f)_*[ModuleCat A])).map ((finiteExceptionalAdjunction A g).counit.app M.obj) ≫
        ((finiteExceptionalAdjunction A f).homEquiv _ _).symm a =
      (rightDerivedLowerStarComp (ModuleCat A) g f).hom.app
          ((R(g)^![ModuleCat A]).obj M.obj) ≫
        ((finiteExceptionalAdjunction A (g ≫ f)).homEquiv _ _).symm
          ((R(g)^![ModuleCat A]).map a ≫ (finiteExceptionalCompIso A g f).hom.app N.obj) := by
  sorry

/-- The canonical opposite shift in the first internal-Hom argument, obtained by
conjugating the tensor-shift comparison and then commuting the remaining shift.
Source: ILO XVII 5.4.1 and the tensor--Hom adjunction
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalSourceShiftIso (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (n : ℤ) :
    (RHom(X)[ModuleCat A]).obj (op (M⟦n⟧)) ≅
      (RHom(X)[ModuleCat A]).obj (op M) ⋙ shiftFunctor _ (-n) :=
  (conjugateIsoEquiv
    ((derivedTensorHomAdjunction (ModuleCat A) M).comp
      (shiftEquiv' _ n (-n) (add_neg_cancel n)).toAdjunction)
    (derivedTensorHomAdjunction (ModuleCat A) (M⟦n⟧))
    ((derivedTensorSymmetry (ModuleCat A) X).app (M⟦n⟧) ≪≫
      derivedTensorRightShiftIso (ModuleCat A) M n ≪≫
      Functor.isoWhiskerRight ((derivedTensorSymmetry (ModuleCat A) X).app M).symm
        (shiftFunctor _ n))).symm ≪≫
    ((RHom(X)[ModuleCat A]).obj (op M)).commShiftIso (-n)

/-- Compatibility with the opposite shift in the source argument.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (step 5): conjugate the canonical tensor-shift comparisons on both sides
of the counit-defined projection formula. Their transposes agree by the exact
projection-mate compatibility and the unique adjunction shift structures.
The symmetry factors in the source-shift construction retain the Koszul signs. -/
theorem finiteExceptionalInternalHom_sourceShift
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A)))
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A))) (n : ℤ) :
    (R((f)_*[ModuleCat A])).map
        ((finiteExceptionalSourceShiftIso A T M.obj n).hom.app
          ((R(f)^![ModuleCat A]).obj N.obj)) ≫
      ((R((f)_*[ModuleCat A])).commShiftIso (-n)).hom.app
        (((RHom(T)[ModuleCat A]).obj (op M.obj)).obj ((R(f)^![ModuleCat A]).obj N.obj)) ≫
      (finiteExceptionalInternalHomPlusIso A f M N).hom⟦-n⟧' =
      (((finiteExceptionalInternalHomIso A f).app (op (M.obj⟦n⟧))).app N.obj).hom ≫
      ((RHom(S)[ModuleCat A]).map
        (op (((R((f)_*[ModuleCat A])).commShiftIso n).inv.app M.obj))).app N.obj ≫
      (finiteExceptionalSourceShiftIso A S ((R((f)_*[ModuleCat A])).obj M.obj) n).hom.app
        N.obj := by
  sorry

/-- Derive the exact slice sum-extension/restriction adjunction, transporting only
its right side from termwise inverse image to the recorded derived pullback.
Source: ILO XVII 5.4.1; site localization adjunction
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalSliceAdjunction (A : Type (u + 1)) [CommRing A]
    {U S : Scheme.{u}} (u : U ⟶ S) [Etale u] :
    D(etaleLowerShriek (ModuleCat A) u inferInstance) ⊣ L((u)^*[ModuleCat A]) :=
  (Adjunction.mapDerivedCategoryAdjunction
    (etaleLowerShriekUpperStarAdjunction (ModuleCat A) u inferInstance)).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) u).symm

/-- Finite direct image commutes with restriction to any etale object, including
nonseparated and non-quasi-compact objects.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (steps 6--8): on a slice, the section formula for finite direct image is
unchanged. Finite exactness descends this identity termwise to the unbounded
categories. Under the inverse-image adjunction the comparison is exactly the
standard base-change mate. No global Noetherian hypothesis on the slice is used. -/
theorem finiteExceptionalEtaleBaseChange_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S U : Scheme.{u}} (f : T ⟶ S) [IsFinite f] (u : U ⟶ S) [Etale u] :
    IsIso (derivedBaseChangeMap (ModuleCat A)
      (IsPullback.of_hasPullback f u).toCommSq) := by
  sorry

/-- The indexed-summand exchange u_Σ! f_U* → f_* v_Σ!, specified as the inverse
mate of finite base change under the exact slice adjunctions.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalSliceSumExchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S U : Scheme.{u}} (f : T ⟶ S) [IsFinite f] (u : U ⟶ S) [Etale u] :
    R((pullback.snd f u)_*[ModuleCat A]) ⋙
        D(etaleLowerShriek (ModuleCat A) u inferInstance) ⟶
      D(etaleLowerShriek (ModuleCat A) (pullback.fst f u) inferInstance) ⋙
        R((f)_*[ModuleCat A]) :=
  haveI := finiteExceptionalEtaleBaseChange_isIso A f u
  ((mateEquiv (finiteExceptionalSliceAdjunction A (pullback.fst f u))
    (finiteExceptionalSliceAdjunction A u)).symm
    (TwoSquare.mk _ _ _ _
      (asIso (derivedBaseChangeMap (ModuleCat A)
        (IsPullback.of_hasPullback f u).toCommSq)).inv)).natTrans

/-- The exceptional slice comparison is fixed by the slice sum exchange and the
exceptional counits, via conjugation of the two composite adjunctions.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalRestriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S U : Scheme.{u}} (f : T ⟶ S) [IsFinite f] (u : U ⟶ S) [Etale u] :
    R(f)^![ModuleCat A] ⋙ L((pullback.fst f u)^*[ModuleCat A]) ⟶
      L((u)^*[ModuleCat A]) ⋙ R(pullback.snd f u)^![ModuleCat A] :=
  conjugateEquiv
    ((finiteExceptionalSliceAdjunction A (pullback.fst f u)).comp
      (finiteExceptionalAdjunction A f))
    ((finiteExceptionalAdjunction A (pullback.snd f u)).comp
      (finiteExceptionalSliceAdjunction A u)) (finiteExceptionalSliceSumExchange A f u)

/-- The internal-Hom restriction map, defined by restricting evaluation and using
the canonical tensor-pullback comparison. It is used only for etale restrictions below.
Source: ILO XVII 5.4.1 and tensor--Hom adjunction
(blueprint: lem-per-finite-exceptional-internal-hom). -/
def finiteExceptionalHomRestriction (A : Type (u + 1)) [CommRing A]
    {U S : Scheme.{u}} (u : U ⟶ S)
    (M N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A))) :
    (L((u)^*[ModuleCat A])).obj (((RHom(S)[ModuleCat A]).obj (op M)).obj N) ⟶
      ((RHom(U)[ModuleCat A]).obj (op ((L((u)^*[ModuleCat A])).obj M))).obj
        ((L((u)^*[ModuleCat A])).obj N) :=
  ((derivedTensorHomAdjunction (ModuleCat A) ((L((u)^*[ModuleCat A])).obj M)).homEquiv _ _)
    ((leftDerivedUpperStarTensorIso (ModuleCat A) u M
        (((RHom(S)[ModuleCat A]).obj (op M)).obj N)).inv ≫
      (L((u)^*[ModuleCat A])).map ((derivedTensorHomAdjunction (ModuleCat A) M).counit.app N))

/-- The internal adjunction commutes with every etale restriction, using the
specified base-change and counit-compatible exceptional comparisons.
Source: ILO XVII 5.4.1, pp. 291, 293
(blueprint: lem-per-finite-exceptional-internal-hom).
Proof (steps 6--8): the slice sum exchange on stalks is the map from the sum of
finite products to the finite product of sums. The union of finitely many finite
supports constructs its inverse, including the empty-fibre case. Exact slice
adjunctions descend termwise; their conjugate identifies the exceptional images.
Internal Hom commutes with slice restriction. Restricting evaluation, projection
and the counit in step 4 yields precisely their counterparts in the slice.
Tensor--Hom transposition gives the square below, without detecting derived maps
by stalks and without imposing separatedness or quasi-compactness on the etale object. -/
theorem finiteExceptionalInternalHom_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T S U : Scheme.{u}} (f : T ⟶ S) [IsFinite f] (u : U ⟶ S) [Etale u]
    [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A)))
    (N : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat A))) :
    IsIso (finiteExceptionalRestriction A f u) ∧
    IsIso (finiteExceptionalHomRestriction A u ((R((f)_*[ModuleCat A])).obj M.obj) N.obj) ∧
    IsIso (finiteExceptionalHomRestriction A (pullback.fst f u) M.obj
      ((R(f)^![ModuleCat A]).obj N.obj)) ∧
    (L((u)^*[ModuleCat A])).map (finiteExceptionalInternalHomPlusIso A f M N).hom ≫
        finiteExceptionalHomRestriction A u ((R((f)_*[ModuleCat A])).obj M.obj) N.obj =
      (derivedBaseChangeMap (ModuleCat A) (IsPullback.of_hasPullback f u).toCommSq).app
        (((RHom(T)[ModuleCat A]).obj (op M.obj)).obj ((R(f)^![ModuleCat A]).obj N.obj)) ≫
      (R((pullback.snd f u)_*[ModuleCat A])).map
        (finiteExceptionalHomRestriction A (pullback.fst f u) M.obj
            ((R(f)^![ModuleCat A]).obj N.obj) ≫
          ((RHom(pullback f u)[ModuleCat A]).obj
            (op ((L((pullback.fst f u)^*[ModuleCat A])).obj M.obj))).map
              ((finiteExceptionalRestriction A f u).app N.obj)) ≫
      (((finiteExceptionalInternalHomIso A (pullback.snd f u)).app
        (op ((L((pullback.fst f u)^*[ModuleCat A])).obj M.obj))).app
          ((L((u)^*[ModuleCat A])).obj N.obj)).hom ≫
      ((RHom(U)[ModuleCat A]).map
        (op ((derivedBaseChangeMap (ModuleCat A)
          (IsPullback.of_hasPullback f u).toCommSq).app M.obj))).app
            ((L((u)^*[ModuleCat A])).obj N.obj) := by
  sorry

end AlgebraicGeometry.Etale
