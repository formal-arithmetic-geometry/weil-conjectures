module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Sheaf.Paper.NativeModuleConstructibilityComparison
public import Sheaf.Paper.LocallyFiniteCoefficientRingRealization
public import Sheaf.CategoryTheory.KInjectiveExactSquareComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.FixedPairDerivedForgetComparison
import Sheaf.Paper.NativeScalarForgetting
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Native coefficient hearts and normalized open/proper forgetting

Source: blueprint cor-coef-verdier-weil-equivariance, native refinement of Steps 1--2;
WeilSheaf/Category.lean, OpenImmersion.lean and LowerStar.lean; Stacks 03CY, 03EK, 03DJ
and 070I (blueprint: lem-sf-native-weil-open-proper-forgetting).

All derived categories are ordinary derived categories of the actual native hearts.
The comparisons below are assembled from the existing exact-localization and total-derived
comparisons, retaining their units. Constructibility is a condition on cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor
open scoped AlgebraicGeometry.ProEtale CategoryTheory.Obj

namespace AlgebraicGeometry.NativeWeilOpenProper

/-- The native locally finite-span functions are precisely the continuous functions locally
valued in finite subextensions. Source: coefficient realization, Step 1; HRS Example 3.1
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: a finite-dimensional span has a finite basis of algebraic elements; the field they
 generate is a finite extension. Conversely a finite subextension is finite dimensional,
so any subset of it spans a finite-dimensional subspace. The argument is pointwise on
neighbourhoods; empty spaces and the zero span use the base field. -/
theorem coefficient_sections (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (V : T.ProEt) (s : C(V.left, PadicAlgCl l)) :
    s ∈ PadicAlgCl.locallyFiniteFunctions l V.left ↔
      ∀ x : V.left, ∃ N ∈ nhds x, ∃ E : PadicAlgCl.FiniteIntermediateField l,
        ∀ y ∈ N, s y ∈ E.1 := by
  rw [PadicAlgCl.mem_locallyFiniteFunctions_iff]
  constructor
  · intro hs x
    obtain ⟨W, hW, hxW, E, hE, hvalues⟩ :=
      PadicAlgCl.exists_isOpen_mem_finiteIntermediateField hs x
    refine ⟨W, hW.mem_nhds hxW, ⟨E, hE⟩, hvalues⟩
  · intro hs x
    obtain ⟨N, hN, E, hvalues⟩ := hs x
    haveI : FiniteDimensional ℚ_[l] E.1 := E.2
    refine ⟨N, hN, Submodule.finiteDimensional_of_le
      (S₂ := E.1.toSubalgebra.toSubmodule) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hvalues y hy

/-- The canonical ring and module presentations preserve the actual underlying sheaf.
Source: native comparison Steps 1--2, Stacks 03CY and 03EK; the normalization and its
finite-extension/restriction equations are those of locallyFiniteCoefficientRing_realization
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: apply lem-sf-locally-finite-coefficient-ring-realization, including its finite-field
legs and naturality square. Unpack the balanced action B tensor M to M into sectionwise
bilinear maps. Unit and associativity become the module axioms, and morphisms become
sectionwise linear maps. The inverse construction uses tensor sheafification. These are
the existing sectionModuleEquivalence and nativeToOrdinaryModules; their underlying
abelian sheaves, restriction maps and actions coincide. -/
theorem coefficient_modules (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    IsMonHom (ProEtale.nativeModuleCoefficientIso l T).hom ∧
      (ProEtale.nativeToOrdinaryModules l T).IsEquivalence ∧
      ProEtale.nativeToOrdinaryModules l T ⋙ SheafOfModules.toSheaf _ =
        ProEtale.AdicSheaf.forget T ⋙ ProEtale.weilCoefficientsForgetAb l T := by
  refine ⟨inferInstance, ?_, ?_⟩
  · change (ProEtale.AdicSheaf.forgetAb l T ⋙
      Mod.comap (ProEtale.nativeModuleCoefficientIso l T).hom ⋙
      (ProEtale.nativeOrdinaryPresentation l T).functor).IsEquivalence
    have h₁ := AlgebraicGeometry.ProEtale.nativeScalarForgetting_isEquivalence l T
    have h₂ : (Mod.comap (ProEtale.nativeModuleCoefficientIso l T).hom).IsEquivalence :=
      (Mod.comapEquivalenceOfIsIso
        (ProEtale.nativeModuleCoefficientIso l T).hom).isEquivalence_functor
    have h₃ : (ProEtale.nativeOrdinaryPresentation l T).functor.IsEquivalence :=
      (ProEtale.nativeOrdinaryPresentation l T).isEquivalence_functor
    infer_instance
  · rfl

/-- The coefficient identification commutes with all scheme restrictions and every
finite-extension inclusion, and hence retains the coefficient ring rather than just
its additive sheaf. Source: native comparison Step 1; coefficient realization theorem
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: use the finite-extension section equation and coefficient-map naturality of
lem-sf-locally-finite-coefficient-ring-realization for its normalized chosen isomorphism.
Multiplication and the unit are preserved by coefficient_modules. Restriction along
an arrow of a pro-etale site is also preserved since this is a sheaf morphism. -/
theorem coefficient_naturality (l : ℕ) [Fact l.Prime] :
    (∀ (X Y : Scheme.{u}) (h : X ⟶ Y),
      ProEtale.condensedPushforwardHom (Profinite.padicAlgClRingObj l) h ≫
          (ProEtale.lowerStar Ab.{u + 1} h).map
            (ProEtale.nativeModuleCoefficientIso l X).hom =
        (ProEtale.nativeModuleCoefficientIso l Y).hom ≫
          (ProEtale.weilCoefficientsForgetAb l Y).map
            (ProEtale.adicConstantSheafToLowerStar l h)) ∧
      (∀ (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) (V : T.ProEtᵒᵖ)
        (s : (ProEtale.condensedRingObj (Profinite.continuousMapRingObj E) T).obj.obj V)
        (x : V.unop.left),
        (((((ProEtale.upperStarFromPoint T).map
          (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
            (ProEtale.nativeModuleCoefficientIso l T).hom).hom.app V) s).down.1 x) =
          (((ProEtale.chartComparison T E).hom.app V s).down x : PadicAlgCl l)) := by
  let R := AlgebraicGeometry.ProEtale.locallyFiniteCoefficientRing_realization l
  refine ⟨?_, ?_⟩
  · exact fun X Y h ↦ R.choose_spec.2.2 X Y h
  · exact fun T E V s x ↦ R.choose_spec.2.1 T E V s x

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- Structural and derived properties of the actual native coefficient heart and its
fixed pairs. Source: native comparison Steps 3--5; Category.lean and IsoAlgebra.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: the native heart is Grothendieck by the existing AdicSheaf instance, and
native Frobenius pullback is an equivalence, hence exact, with explicit inverse. Apply
lem-sf-fixed-pair-derived-forget-comparison: the integer-indexed free pair shifts its
summands, is exact, and is left adjoint to forgetting. Hence forgetting preserves
K-injectives. Exactness gives the natural cohomology isomorphism. It reflects zero and
therefore derived isomorphisms and boundedness. Exact-functor localization commutes with
shifts and preserves cone triangles (lem-sf-exact-functor-derived-triangulated).
Finally the geometric fibre is qcqs; the native qcqs-stratification lemma turns local
constructibility into a finite stratified lisse sheaf, whose strata are constructible by
definition, and conversely. Transport along the cohomology comparison in each degree to
obtain the last equivalence. -/
theorem hearts (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
    [Fact (ringChar k₀ ≠ l)] [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] :
    IsGrothendieckAbelian.{u + 1}
        (ProEtale.AdicSheaf l (T ↘ Spec (CommRingCat.of k₀)).geometricFiber) ∧
      IsGrothendieckAbelian.{u + 1} (ProEtaleWeilSheaf k₀ l T) ∧
      (WeilSheaf.frobeniusPullback k₀ l T).IsEquivalence ∧
      PreservesFiniteLimits (WeilSheaf.frobeniusPullback k₀ l T) ∧
      PreservesFiniteColimits (WeilSheaf.frobeniusPullback k₀ l T) ∧
      PreservesFiniteLimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
      PreservesFiniteColimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).ReflectsIsomorphisms ∧
      Nonempty (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l T) ⊣
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
      PreservesFiniteLimits (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l T)) ∧
      PreservesFiniteColimits (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l T)) ∧
      (∀ M : ProEtale.AdicSheaf l (T ↘ Spec (CommRingCat.of k₀)).geometricFiber,
        ((IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l T)).obj M).carrier =
          ∐ (IsoAlgebra.Free.obj (WeilSheaf.frobeniusPullback k₀ l T) M)) ∧
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).PreservesKInjectiveComplexes ∧
      (IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory.ReflectsIsomorphisms ∧
      Nonempty ((IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory.CommShift ℤ) ∧
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory.IsTriangulated ∧
      (∀ n : ℤ, Nonempty
        (DerivedCategory.homologyFunctor (ProEtaleWeilSheaf k₀ l T) n ⋙
            IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T) ≅
          (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory ⋙
            DerivedCategory.homologyFunctor _ n)) ∧
      (∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l T),
        (DerivedCategory.TStructure.t.bounded K ↔
          DerivedCategory.TStructure.t.bounded
            ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory.obj K))) ∧
      (∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l T),
        WeilComplex.objectProperty k₀ l T K ↔
          DerivedCategory.TStructure.t.bounded
            ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory.obj K) ∧
          ∀ n : ℤ, ProEtale.IsAdicStratifiedLisseSheaf
            ((DerivedCategory.homologyFunctor _ n).obj
              ((IsoAlgebra.forget
                (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory.obj K))) := by
  let F := WeilSheaf.frobeniusPullback k₀ l T
  let U := IsoAlgebra.forget F
  obtain ⟨hG, hlim, hcolim, href, hadj, hfreeLim, hfreeColim, hcarrier,
    _, _, hKI, hDref⟩ := IsoAlgebra.fixedPair_forget_properties F
  have hb (K : DerivedCategory (ProEtaleWeilSheaf k₀ l T)) :
      DerivedCategory.TStructure.t.bounded K ↔
        DerivedCategory.TStructure.t.bounded (U.mapDerivedCategory.obj K) :=
    ⟨U.bounded_mapDerivedCategory_obj, U.bounded_of_bounded_mapDerivedCategory_obj⟩
  refine ⟨inferInstance, hG, inferInstance, inferInstance, inferInstance,
    hlim, hcolim, href, hadj, hfreeLim, hfreeColim, hcarrier, hKI, hDref,
    ⟨inferInstance⟩, inferInstance, fun n ↦ ⟨U.mapDerivedCategoryHomologyFunctorIso n⟩,
    hb, ?_⟩
  intro K
  constructor
  · rintro ⟨hbound, hconstructible⟩
    refine ⟨(hb K).1 hbound, fun n ↦ ?_⟩
    exact (hconstructible n).isAdicStratifiedLisseSheaf.of_iso
      ((U.mapDerivedCategoryHomologyFunctorIso n).app K)
  · rintro ⟨hbound, hstratified⟩
    refine ⟨(hb K).2 hbound, fun n ↦ ?_⟩
    exact ((hstratified n).of_iso
      ((U.mapDerivedCategoryHomologyFunctorIso n).symm.app K)).isAdicConstructibleSheaf

/-- Frobenius and its inverse are the two coefficient-preserving reindexings of the
geometric-fibre site. The inverse is explicit, rather than an unspecified quasi-inverse.
Source: native comparison Step 3; Adic/GeometricFrobenius.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: geometric Frobenius is an automorphism of the geometric fibre, with inverse
arithmetic Galois Frobenius. Postcomposition gives inverse site equivalences. The
coefficient maps are precomposition of the same functions, respecting multiplication
and finite fields. Apply adicLowerStarEquivalence to the inverse automorphism; its
functor is the framework's P and its inverse is pushforward along geometric Frobenius.
Equivalences of abelian categories are exact in both directions. -/
theorem frobenius_reindexing (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))] :
    (ProEtale.adicLowerStarEquivalence l
      (T ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).functor =
        WeilSheaf.frobeniusPullback k₀ l T ∧
      PreservesFiniteLimits (ProEtale.adicLowerStarEquivalence l
        (T ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).inverse ∧
      PreservesFiniteColimits (ProEtale.adicLowerStarEquivalence l
        (T ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).inverse := by
  refine ⟨rfl, ?_, ?_⟩
  · infer_instance
  · infer_instance

variable {k₀ l}
variable [Fact (ringChar k₀ ≠ l)]
variable {X Z Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- The actual proper Frobenius transport comparison, not an independently chosen iso.
Source: LowerStar.lean and native comparison Step 7
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev properComparison (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))] :=
  letI : HasColimitsOfSize.{u + 1, u + 1}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    IsGrothendieckAbelian.hasColimits _
  letI : HasColimitsOfSize.{0, 0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  letI : HasCoproducts.{0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    fun J ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  letI : AB5OfSize.{0, 0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  letI : HasFiniteBiproducts
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : AB4OfSize.{0}
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    AB4.of_AB5 _
  IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
    (WeilSheaf.frobeniusPullback k₀ l Z)
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l p
      (comp_over p (Spec (CommRingCat.of k₀))))

/-- The native-unit arrow from the common sheaf-level representative.
Source: native comparison Step 8, Stacks 070I
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev properLeftUnit (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :=
  KInjectiveExactSquare.leftUnit
    (ProEtaleWeilSheaf.lowerStar k₀ l p)
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
      (comp_over p (Spec (CommRingCat.of k₀)))))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)) rfl
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctorUnit I

/-- The ordinary-unit arrow from the very same representative.
Source: native comparison Step 8, Stacks 070I
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev properRightUnit (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :=
  KInjectiveExactSquare.rightUnit
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
      (comp_over p (Spec (CommRingCat.of k₀)))))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
      (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctor
    (ProEtale.adicLowerStar l
      (Scheme.Hom.geometricFiberMap p
        (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctorUnit I

-- Uniqueness of total right derivation supplies the unit equations of each factor.
-- The strict underlying square cancels the homotopy-composition comparisons.
section UnitNormalization

universe w w' v v' uC uD

variable {C : Type uC} [Category.{v} C] [Abelian C]
  {D : Type uD} [Category.{v'} D] [Abelian D]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

private theorem fixedPair_unit_normalization (I : CochainComplex (IsoAlgebra F) ℤ) :
    KInjectiveExactSquare.leftUnit (IsoAlgebra.mapOfNatIso e) L
      (IsoAlgebra.forget F) (IsoAlgebra.forget G) rfl
      (IsoAlgebra.mapOfNatIso e).rightDerivedFunctor
      (IsoAlgebra.mapOfNatIso e).rightDerivedFunctorUnit I ≫
        (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
      KInjectiveExactSquare.rightUnit L (IsoAlgebra.forget F) L.rightDerivedFunctor
        L.rightDerivedFunctorUnit I := by
  let P := IsoAlgebra.mapOfNatIso e
  let r := IsoAlgebra.forget F
  let s := IsoAlgebra.forget G
  let K := (HomotopyCategory.quotient (IsoAlgebra F) (.up ℤ)).obj I
  have h₁ : s.mapDerivedCategoryFactorsh.inv.app
        ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      s.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app K) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso P s).inv.app
          (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (P ⋙ s)) (.up ℤ)).hom.app K) ≫
          (P ⋙ s).rightDerivedFunctorUnit.app K := by
    apply (cancel_mono ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso P s).hom.app
      (DerivedCategory.Qh.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
  have h₂ : (P ⋙ s).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso
        (IsoAlgebra.mapOfNatIsoCompForgetIso e)).hom.app (DerivedCategory.Qh.obj K) =
      (r ⋙ L).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      IsoAlgebra.mapOfNatIsoCompForgetIso, P, r, s]
  have h₃ : (r ⋙ L).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso r L).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (r ⋙ L)) (.up ℤ)).inv.app K) ≫
        L.rightDerivedFunctorUnit.app ((r.mapHomotopyCategory (.up ℤ)).obj K) ≫
          L.rightDerivedFunctor.map (r.rightDerivedFunctorUnit.app K) := by
    simp [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedFunctorCompUnit]
  have h₄ : r.rightDerivedFunctorUnit.app K ≫
      r.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) =
      r.mapDerivedCategoryFactorsh.inv.app K := by
    exact congr_app (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac r) K
  have ha : (KInjectiveExactSquare.sourceIso P L r s rfl).hom.app K = 𝟙 _ := by
    change (𝟙 _) ≫ (𝟙 _) = _
    exact Category.id_comp _
  have hc₁ : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (P ⋙ s)) (.up ℤ)).hom.app K = 𝟙 _ := rfl
  have hc₃ : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (r ⋙ L)) (.up ℤ)).inv.app K = 𝟙 _ := rfl
  dsimp only [KInjectiveExactSquare.leftUnit, KInjectiveExactSquare.rightUnit]
  simp only [Category.assoc]
  change DerivedCategory.Qh.map ((KInjectiveExactSquare.sourceIso P L r s rfl).hom.app K) ≫
    s.mapDerivedCategoryFactorsh.inv.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      s.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app K) ≫
        (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso F e).hom.app
          (DerivedCategory.Qh.obj K) =
    L.rightDerivedFunctorUnit.app ((r.mapHomotopyCategory (.up ℤ)).obj K) ≫
      L.rightDerivedFunctor.map (r.mapDerivedCategoryFactorsh.inv.app K)
  simp only [IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [reassoc_of% h₁, ha, hc₁]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rw [reassoc_of% h₂, reassoc_of% h₃, hc₃, CategoryTheory.Functor.map_id,
    Category.id_comp, ← L.rightDerivedFunctor.map_comp, h₄]

end UnitNormalization

-- Keep the existing characteristic binder for callers, although normalization is formal.
set_option linter.unusedSectionVars false in
/-- The total-derived comparison is induced by the equality of underlying sheaf functors
with their units. This equation makes it the identity after identifying both sides with
Q(p_* UI) by those units; it holds on every complex and in particular on K-injectives.
Source: native comparison Steps 7--8; Stacks 070Y and 070K
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: the lift is mapOfNatIso for the framework comparison. Its composite with forgetting
is literally forget followed by p_*. Use lem-sf-fixed-pair-derived-forget-comparison and
the unique unit-normalized exact-square comparison. Both units are invertible on a native
K-injective because forgetting preserves K-injectives. Their quotient is the identity
under the common representative identifications. Naturality extends the unit equality
along resolutions. This also proves uniqueness from normalization on K-injectives. -/
theorem proper_normalization (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    [IsProper p] :
    (∀ I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ,
      properLeftUnit p I ≫ (properComparison (k₀ := k₀) (l := l) p).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
          properRightUnit p I) ∧
      (∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) [I.IsKInjective],
        IsIso (properLeftUnit p I) ∧ IsIso (properRightUnit p I)) := by
  let r := IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have : r.PreservesKInjectiveComplexes := inferInstance
  constructor
  · intro I
    exact fixedPair_unit_normalization (WeilSheaf.frobeniusPullback k₀ l Z)
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l p
        (comp_over p (Spec (CommRingCat.of k₀)))) I
  · intro I hI
    have : CochainComplex.IsKInjective ((r.mapHomologicalComplex (.up ℤ)).obj I) :=
      inferInstance
    have hu : IsIso ((ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
        (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((r.mapHomologicalComplex (.up ℤ)).obj I))) := inferInstance
    constructor
    · dsimp only [properLeftUnit, KInjectiveExactSquare.leftUnit]
      infer_instance
    · dsimp only [properRightUnit, KInjectiveExactSquare.rightUnit]
      have : IsIso ((ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
          (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctorUnit.app
            ((r.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := hu
      infer_instance

omit [Fact (ringChar k₀ ≠ l)] in
/-- Exactness and literal sheaf-level forgetting for the native open lift.
Source: native comparison Step 6; Stacks 03DI and 03DJ, OpenImmersion.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: the pro-etale site of the open is the localized target site, with the same
coefficient functions. Ringed-site extension by zero is exact. The fixed-pair lift
has this exact underlying functor on objects and maps; conservative exact forgetting
then detects exactness of its image sequences. -/
theorem open_exact (j : X ⟶ Z) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))) ∧
      PreservesFiniteColimits (ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))) ∧
      PreservesFiniteLimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
      PreservesFiniteColimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
      ProEtaleWeilSheaf.extensionByZero k₀ l j ⋙
          IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) =
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙
          ProEtale.adicOpenImmersionLowerShriek l
            (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))) := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rfl

/-- Exact open forgetting, descended termwise from the actual native lift.
Source: OpenImmersion.lean, native comparison Step 6
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev openComparison (j : X ⟶ Z) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        (ProEtale.adicOpenImmersionLowerShriek l
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (IsoAlgebra.mapOfNatIsoCompForgetIso
        (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
          l j (comp_over j (Spec (CommRingCat.of k₀))))) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The ordered open/proper comparison c^0, assembled by precomposing the canonical
proper comparison with native open extension and then using exact open forgetting.
Source: native comparison Step 9; LowerShriek.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev comparison (j : X ⟶ Z) (p : Z ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        (ProEtale.adicOpenImmersionLowerShriek l
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory ⋙
        (ProEtale.adicLowerStar l
          (Scheme.Hom.geometricFiberMap p
            (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _ (properComparison (k₀ := k₀) (l := l) p) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openComparison (k₀ := k₀) (l := l) j) _ ≪≫
    Functor.associator _ _ _

/-- The ordinary Frobenius chain map on the common representative, with the native
source and target retained to make the coefficient identifications explicit.
Source: native comparison Step 8; LowerStar.lean, mapOfNatIso_obj_str
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
def ordinaryFrobeniusChain (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :=
  let J := ((ProEtaleWeilSheaf.lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I
  let t := (NatTrans.mapHomologicalComplex
    (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l Y)).hom (.up ℤ)).app J
  show (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)) ⋙
      WeilSheaf.frobeniusPullback k₀ l Y).mapHomologicalComplex (.up ℤ)).obj J ⟶
    ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapHomologicalComplex
      (.up ℤ)).obj J from
  { f := fun n ↦
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
        l p (comp_over p (Spec (CommRingCat.of k₀)))).hom.app (I.X n).carrier ≫
      (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap p
          (comp_over p (Spec (CommRingCat.of k₀))))).map (I.X n).str.hom
    comm' := fun i j _ ↦ t.comm i j }

omit [Fact (ringChar k₀ ≠ l)] in
/-- On the common native K-injective representative both Frobenius arrows are
Q(p_*(theta_I) a_UI), with the framework's precise direct-image comparison a.
Source: native comparison Step 8; LowerStar.lean and mapOfNatIso_obj_str
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof: evaluate the fixed-pair lift in every degree: its structure is a followed by
the image of theta, and its underlying differentials are p_* of the original ones.
Naturality of a and theta makes these maps the ordinaryFrobeniusChain. Localization
sends identical chain maps to identical arrows. Forgetting preserves K-injectivity,
and Frobenius is an exact equivalence, so ordinary derivation uses this same
representative. Thus the identity comparison intertwines both actions. -/
theorem proper_frobenius (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]
    [IsProper p] (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l Y)).hom (.up ℤ)).app
            (((ProEtaleWeilSheaf.lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I)) =
      DerivedCategory.Q.map (ordinaryFrobeniusChain (k₀ := k₀) (l := l) p I) := by
  rfl

/-- The ordinary ordered open/proper construction for the chosen compactification.
Source: LowerShriek.lean and native comparison Step 9
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev ordinaryCompactSupport (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) :=
  letI := c.over (k₀ := k₀)
  (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap c.i
        (comp_over c.i (Spec (CommRingCat.of k₀))))).mapDerivedCategory ⋙
    (ProEtale.adicLowerStar l
      (Scheme.Hom.geometricFiberMap c.g
        (comp_over c.g (Spec (CommRingCat.of k₀))))).rightDerivedFunctor

/-- The canonical comparison c^0 for the actual compactification functor of the native
framework. Source: LowerShriek.lean and native comparison Step 9
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev compactificationComparison (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        ordinaryCompactSupport (k₀ := k₀) (l := l) f c :=
  letI := c.over (k₀ := k₀)
  Functor.associator _ _ _ ≪≫ comparison (k₀ := k₀) (l := l) c.i c.g

/-- The derived native structure is obtained by localizing the actual structure
isomorphism of fixed pairs. It is not supplied by a structure on the derived category.
Source: native comparison Step 8; IsoAlgebra.strNatIso and exact localization
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev nativeDerivedStructure (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))] :
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory ⋙
        (WeilSheaf.frobeniusPullback k₀ l T).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l T))

/-- The ordinary proper Frobenius comparison is derived from the native sheaf
comparison a using the total-right-derived composition isomorphisms and their units.
It does not use properComparison or a transported native action.
Source: native comparison Steps 7--8; RightDerivedFunctor/Comp.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev ordinaryProperFrobenius (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
        (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctor ⋙
        (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory ≅
      (WeilSheaf.frobeniusPullback k₀ l Z).mapDerivedCategory ⋙
        (ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap p
          (comp_over p (Spec (CommRingCat.of k₀))))).rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
        l p (comp_over p (Spec (CommRingCat.of k₀)))) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (WeilSheaf.frobeniusPullback k₀ l Z).rightDerivedFunctorIsoMapDerivedCategory _

/-- The ordinary exact open comparison is the termwise localization of the actual
coefficient-preserving sheaf comparison for j!, independent of native forgetting.
Source: native comparison Step 6; OpenImmersion.lean
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev ordinaryOpenFrobenius (j : X ⟶ Z) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtale.adicOpenImmersionLowerShriek l (Scheme.Hom.geometricFiberMap j
        (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory ⋙
        (WeilSheaf.frobeniusPullback k₀ l Z).mapDerivedCategory ≅
      (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory ⋙
        (ProEtale.adicOpenImmersionLowerShriek l (Scheme.Hom.geometricFiberMap j
          (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
        l j (comp_over j (Spec (CommRingCat.of k₀)))) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary ordered Frobenius comparison is assembled from derived a for p_*
and the exact open comparison for j!. No use is made of compactificationComparison.
Source: native comparison Steps 8--9; ordered open/proper construction
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev ordinaryFrobeniusComparison (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    ordinaryCompactSupport (k₀ := k₀) (l := l) f c ⋙
        (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory ≅
      (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory ⋙
        ordinaryCompactSupport (k₀ := k₀) (l := l) f c :=
  letI := c.over (k₀ := k₀)
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ordinaryProperFrobenius (k₀ := k₀) (l := l) c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ordinaryOpenFrobenius (k₀ := k₀) (l := l) c.i) _ ≪≫
    Functor.associator _ _ _

/-- Frobenius on the native output is D(strNatIso) at the actual native compact-support
output. Source: native comparison Step 8, native derived structure
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev nativeCompactSupportFrobenius (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f)
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  (nativeDerivedStructure (k₀ := k₀) (l := l) Y).app
    ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).obj K)

/-- Frobenius on the ordinary output is the independently derived ordinary comparison
followed by Rp_*j! of the input's localized native structure theta.
Source: native comparison Steps 8--9, ordinary derived a, open comparison and theta
(blueprint: lem-sf-native-weil-open-proper-forgetting). -/
abbrev ordinaryCompactSupportFrobenius (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f)
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  (ordinaryFrobeniusComparison (k₀ := k₀) (l := l) f c).app
      ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory.obj K) ≪≫
    (ordinaryCompactSupport (k₀ := k₀) (l := l) f c).mapIso
      ((nativeDerivedStructure (k₀ := k₀) (l := l) X).app K)

/-- Exact open extension forgets to the ordinary functor on both sheaves and arrows;
the assembled c^0 intertwines the two derived Frobenius structures, respects shifts,
and is natural on all localized derived morphisms.
Source: native comparison Steps 6--9; Stacks 03DI, 03DJ, 070I and 070K
(blueprint: lem-sf-native-weil-open-proper-forgetting).
Proof:
1. Localize the pro-etale site at the geometric open. Both restricted coefficient rings
are the same functions. The exact ringed-site extension by zero is the underlying
native extension; the lift acts on arrows by the same functor. Exact conservative
forgetting detects exactness, and exact-functor localization gives openComparison.
2. The native and ordinary hearts of the middle scheme are Grothendieck by the existing
AdicSheaf instance, with no finite-type hypothesis on the middle scheme. The native
adicLowerStar and its fixed-pair lift are additive and left exact. The fixed-pair
derived comparison gives properComparison, and proper_normalization includes its
derived units.
3. Resolve the complex after open extension by a native K-injective I. It stays
K-injective after forgetting, so both constructions are Q(p_* UI). The normalization
equation identifies the comparison with the identity; proper_frobenius identifies
both Frobenius arrows with Q(p_*(theta_I) a_UI).
4. Every derived map between such representatives is the localization of a chain map
modulo homotopy (lem-weil-pbc-kinjective-hom-derived). Both functors apply p_* U to it,
so the identity comparison is natural on all localized morphisms and independent of
resolution. For shifts use I[n], still K-injective; both shifted structure arrows
are the same. Thus comparison commutes with the actual shift structures.
5. The ordinary action is defined independently: derive the sheaf comparison a
using the unit-normalized total-derived composition isomorphisms, compose with the
termwise open comparison, then apply Rp_*j! to the input D(strNatIso). The native
output action is D(strNatIso) at F^W K. On the common K-injective resolution the
unit equations of proper_normalization identify the proper comparison with the
identity and identify derived a with its original chain map. The sheaf lift formula
therefore makes the Frobenius square commute there. Naturality along the resolution
and the localization factors transports this equality to every K. This proves the
new square between the two independently constructed derived actions, rather than
only the degreewise lift formula recorded by proper_frobenius.
6. Precompose with the exact open extension and the ordered associativity maps to
obtain compactificationComparison. This uses the actual native compactification
construction on the ambient ordinary derived categories, without exceptional adjoints. -/
theorem open_proper (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (c : Compactification f) :
    (compactificationComparison (k₀ := k₀) (l := l) f c).hom.CommShift ℤ ∧
      (∀ K : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
        (WeilSheaf.frobeniusPullback k₀ l Y).mapDerivedCategory.map
            ((compactificationComparison (k₀ := k₀) (l := l) f c).hom.app K) ≫
          (ordinaryCompactSupportFrobenius (k₀ := k₀) (l := l) f c K).hom =
        (nativeCompactSupportFrobenius (k₀ := k₀) (l := l) f c K).hom ≫
          (compactificationComparison (k₀ := k₀) (l := l) f c).hom.app K) ∧
      (∀ (K L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (v : K ⟶ L),
        (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙
            (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory).map v ≫
          (compactificationComparison (k₀ := k₀) (l := l) f c).hom.app L =
        (compactificationComparison (k₀ := k₀) (l := l) f c).hom.app K ≫
          ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
            ordinaryCompactSupport (k₀ := k₀) (l := l) f c).map v) := by
  sorry

end AlgebraicGeometry.NativeWeilOpenProper
