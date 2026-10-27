module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.ConstantGeometricStalkUnit
public import Sheaf.Paper.PointTateFiberCoefficientComparisons
public import Sheaf.Paper.PointFibreDerivedTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Category.ModuleCat.Projective
import Sheaf.Paper.PointTensorNormalizationIndependent
import all Sheaf.Paper.PointFibreEquivalence
import all Sheaf.Paper.ScalarExtensionExactIntrinsic
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology

/-! # Canonical point realization of Weil pairings

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
`sk-thm-frobenius/prop-weil-operations.proof.md`, final smooth-pairing clause,
retained rational proof Step 10 (blueprint: lem-pod-point-weil-pairing-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointWeilPairing
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded rational bounded constructible category at the geometric point.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
abbrev C := sfRationalConstructibleCategory l E (Spec (.of D.k))
/-- The integral category underlying the recorded raw rational localization.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
abbrev I := sfIntegralConstructibleCategory l E (Spec (.of D.k))
/-- The recorded point fibre followed by its fully faithful ambient inclusion.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
abbrev F := pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι
/-- The recorded localization functor; its objects retain their integral presentation.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
abbrev Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
/-- Canonical rational pullback by geometric Frobenius on Spec k.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def P : C D l E ⥤ C D l E :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)
/-- The existing rational derived tensor, with its canonical prime-invertibility instance.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def T : C D l E × C D l E ⥤ C D l E :=
  @rationalDerivedTensor l _ E _ _ _ (Spec (.of D.k))
    (frobeniusPointPrimeInvertible D l hl)
/-- The untwisted rational coefficient line, namely the twist of exponent zero.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def U : C D l E :=
  @FrobeniusCoefficientTwists.rationalLine l _ E _ _ _ (Spec (.of D.k))
    (frobeniusPointPrimeInvertible D l hl) 0
/-- The canonical coefficient Weil isomorphism at exponent zero.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def c : (P D l hl E).obj (U D l hl E) ≅ U D l hl E :=
  @FrobeniusCoefficientTwists.rationalDerivedLineMap l _ E _ _ _ _ _
    (frobeniusPointIso D).hom _ (frobeniusPointPrimeInvertible D l hl)
    (frobeniusPointPrimeInvertible D l hl) 0
/-- Canonical rational point transport with the recorded pullback object identification.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def iota (N : C D l E) : (F D l hl E).obj N ⟶ (F D l hl E).obj ((P D l hl E).obj N) :=
  (frobeniusPointTransportRational D l hl E N).hom ≫
    (F D l hl E).map (eqToHom (frobeniusPointRationalPullbackEq D l hl E N).symm)
/-- The pullback shift fixed by the integral and rational localization square.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def pShift (r : ℤ) (N : C D l E) :
    (P D l hl E).obj (N⟦r⟧) ≅ ((P D l hl E).obj N)⟦r⟧ :=
  (Functor.commShiftIso (P D l hl E)
    (self := @fieldRationalPullShift l _ E _ _ _ _ _ (frobeniusPointIso D).hom
      (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)) r).app N

/-- Canonical point-unit normalization in the larger carrier universe.
It is constant-section multiplication, scalar extension, and the specified carrier descent.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def unitLarge :=
  letI := frobeniusPointPrimeInvertible D l hl
  PointTateFiber.rationalSizeNormalization D l E hl 0 ≪≫
    (Functor.mapDerivedCategory.{u + 1, u + 2, u + 1, u + 1, u + 2, u + 2}
      (pointFibreCoefficientDown E)).mapIso
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointIntegralToField l E)).mapDerivedCategory.mapIso
          (ConstantGeometricStalkUnit.integralSectionsUnit l E D) ≪≫
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (pointIntegralToField l E)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (ConstantGeometricStalkUnit.rationalRegular l E)) ≪≫
    ((pointFibreCoefficientDown E).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    ((ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategorySingleFunctor 0).symm.app
      (ModuleCat.of.{u} E E)

/-- Bounded finite-dimensional cohomology is stable under every integer shift.
Proof: the homology shift isomorphism translates the finite support and preserves
finite dimensionality. This supplies a structure already implicit in the point category.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem fdShift (V : Type u) [Field V] :
    (DerivedCategory.pointFiniteDimensional V).IsStableUnderShift ℤ where
  isStableUnderShiftBy r := ⟨fun X hX ↦ DerivedCategory.pointFd_shift_mem X hX r⟩

attribute [instance] fdShift

/-- The actual integral point fibre followed by rationalization and ambient inclusion.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
abbrev H := pointIntegralRationalFibre D l hl E ⋙
  (DerivedCategory.pointFiniteDimensional E).ι

/-- The integral-rational shift, transported by the fixed carrier-size equivalence.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
@[instance_reducible] def hShift : (H D l hl E).CommShift ℤ := by
  letI := pointFibreSizeLift_equivalence E
  letI : (pointFibreSizeLift E).CommShift ℤ := by
    dsimp only [pointFibreSizeLift]
    infer_instance
  letI : (pointFibreSizeDescent E).CommShift ℤ :=
    Functor.CommShift.ofComp
      (show pointFibreSizeDescent E ⋙ pointFibreSizeLift E ≅ 𝟭 _ from
        (pointFibreSizeLift E).asEquivalence.counitIso) ℤ
  dsimp only [H, pointIntegralRationalFibre]
  infer_instance

/-- The specified object identification for the raw rational point fibre.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def localizeObj (K : I D l E) : (F D l hl E).obj ((Q D l E).obj K) ≅
    (H D l hl E).obj K :=
  eqToIso (congrArg ObjectProperty.FullSubcategory.obj
    ((pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 ((Q D l E).obj K)))

/-- The rational shift is uniquely fixed on every localized integral object.
Proof: the coefficient-one object identification is natural by the pure-tensor
normalization of pointRationalFibre. Its integral functor has the displayed shift.
The shift universal property of raw localization descends it uniquely; the zero
and addition laws descend along the same essentially surjective localization.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem fShift_existsUnique :
    ∃! s : (F D l hl E).CommShift ℤ,
      ∀ (K : I D l E) (r : ℤ),
        (F D l hl E).map (((Q D l E).commShiftIso r).hom.app K) ≫
            ((Functor.commShiftIso (F D l hl E) (self := s) r).hom.app
              ((Q D l E).obj K)) ≫
            (localizeObj D l hl E K).hom⟦r⟧' =
          (localizeObj D l hl E (K⟦r⟧)).hom ≫
            ((Functor.commShiftIso (H D l hl E) (self := hShift D l hl E) r).hom.app K) := by
  classical
  let := hShift D l hl E
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E)) (I D l E)
  let : (Q D l E).IsLocalization W := rawLocalization
    (Padic.coefficientExtensionIntegers l E) (I D l E)
      (Padic.coefficientExtensionUniformizer l E)
  let e : Q D l E ⋙ F D l hl E ≅ H D l hl E :=
    NatIso.ofComponents (localizeObj D l hl E) (by
      intro K M f
      have hh := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.2 K M f 1
      have hh' : HEq ((F D l hl E).map ((Q D l E).map f))
          ((H D l hl E).map f) := by
        dsimp only [F, H, Q, Functor.comp_map, Functor.comp_obj, ObjectProperty.ι,
          inducedFunctor, pointRationalFibre, sfRationalConstructibleLocalization,
          ScalarLocalization.localization] at hh ⊢
        simpa only [map_one, one_smul] using hh
      change (F D l hl E).map ((Q D l E).map f) ≫
        (localizeObj D l hl E M).hom =
          (localizeObj D l hl E K).hom ≫ (H D l hl E).map f
      dsimp only [localizeObj, eqToIso, Iso.refl_hom]
      exact eq_of_heq ((comp_eqToHom_heq _ _).trans
        (hh'.trans (eqToHom_comp_heq _ _).symm)))
  let : Localization.Lifting (Q D l E) W (H D l hl E) (F D l hl E) := ⟨e⟩
  let s := Functor.commShiftOfLocalization (Q D l E) W ℤ (H D l hl E) (F D l hl E)
  have hs (K : I D l E) (r : ℤ) :
      (F D l hl E).map (((Q D l E).commShiftIso r).hom.app K) ≫
          ((Functor.commShiftIso (F D l hl E) (self := s) r).hom.app
            ((Q D l E).obj K)) ≫ (localizeObj D l hl E K).hom⟦r⟧' =
        (localizeObj D l hl E (K⟦r⟧)).hom ≫
          ((Functor.commShiftIso (H D l hl E) (self := hShift D l hl E) r).hom.app K) := by
    rw [Functor.commShiftOfLocalization_iso_hom_app]
    simp only [Category.assoc]
    change (F D l hl E).map _ ≫
      (F D l hl E).map _ ≫ (localizeObj D l hl E (K⟦r⟧)).hom ≫
        ((H D l hl E).commShiftIso r).hom.app K ≫
          (localizeObj D l hl E K).inv⟦r⟧' ≫ (localizeObj D l hl E K).hom⟦r⟧' = _
    simp
  refine ⟨s, hs, ?_⟩
  intro t ht
  have h : t.commShiftIso = s.commShiftIso := by
    funext r
    ext N
    have he := (ht N.obj r).trans (hs N.obj r).symm
    have he' := (cancel_epi
      ((F D l hl E).map (((Q D l E).commShiftIso r).hom.app N.obj))).mp he
    exact (cancel_mono ((localizeObj D l hl E N.obj).hom⟦r⟧')).mp he'
  have hinj : Function.Injective
      (fun z : (F D l hl E).CommShift ℤ ↦ z.commShiftIso) := by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl
  exact hinj h

/-- Canonical rational point shift, fixed by its localization square.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
@[instance_reducible] def fShift : (F D l hl E).CommShift ℤ :=
  (fShift_existsUnique D l hl E).exists.choose

/-- The small point unit is uniquely fixed by its constant-section normalization.
Proof: the carrier lift is fully faithful on bounded finite-dimensional complexes.
Descend unitLarge and its inverse; faithfulness reflects the two inverse identities.
Faithfulness also gives uniqueness of the descended isomorphism.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem unit_existsUnique :
    ∃! e : (F D l hl E).obj (U D l hl E) ≅
        (DerivedCategory.singleFunctor.{u} (ModuleCat.{u} E) 0).obj (ModuleCat.of.{u} E E),
      (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.mapIso e =
        unitLarge D l hl E  := by
  classical
  let p := DerivedCategory.pointFiniteDimensional E
  let q := DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
  let L := (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory
  let J := p.ι ⋙ L
  let J₀ := pointFibreSizeLift E ⋙ q.ι ⋙ (pointFibreCoefficientDown E).mapDerivedCategory
  let := pointFibreSizeLift_equivalence E
  let eJ : J₀ ≅ J :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (q.liftCompιIso (p.ι ⋙ (pointFibreModuleLift E).mapDerivedCategory)
          (pointFibreModuleLift_mem E)) (pointFibreCoefficientDown E).mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft p.ι (pointFibreLiftDownIso E)
  have : J₀.Full := by dsimp only [J₀]; infer_instance
  have : J₀.Faithful := by dsimp only [J₀]; infer_instance
  let ff := (Functor.FullyFaithful.ofFullyFaithful J₀).ofIso eJ
  have : J.Full := ff.full
  have : J.Faithful := ff.faithful
  let V := (DerivedCategory.singleFunctor.{u} (ModuleCat.{u} E) 0).obj
    (ModuleCat.of.{u} E E)
  have hV : p V := by
    refine ⟨⟨{0}, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
    · exact DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
        (Iso.refl V) (by simpa only [Finset.mem_singleton] using hi)
    · by_cases hi : i = 0
      · subst i
        let e₀ : (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).obj V ≅
            ModuleCat.of.{u} E E :=
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} E) 0).app _
        exact e₀.symm.toLinearEquiv.finiteDimensional
      · have hz := DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
          (Iso.refl V) hi
        have := ModuleCat.isZero_iff_subsingleton.mp hz
        infer_instance
  let X : p.FullSubcategory := (pointRationalFibre D l hl E).obj (U D l hl E)
  let Y : p.FullSubcategory := ⟨V, hV⟩
  let a : J.obj X ≅ J.obj Y := unitLarge D l hl E
  let e : X ≅ Y := J.preimageIso a
  refine ⟨p.ι.mapIso e, ?_, ?_⟩
  · change J.mapIso e = a
    ext
    exact J.map_preimage a.hom
  · intro e' he'
    let b : X ≅ Y := p.ι.preimageIso e'
    have hb : J.mapIso b = a := by
      change L.mapIso (p.ι.mapIso b) = a
      have h : p.ι.mapIso b = e' := by
        ext
        exact p.ι.map_preimage (X := X) (Y := Y) e'.hom
      rw [h]
      exact he'
    have he : J.mapIso e = a := by ext; exact J.map_preimage a.hom
    have hbe : b = e := J.mapIso_injective (hb.trans he.symm)
    calc
      e' = p.ι.mapIso b := by
        ext
        exact (p.ι.map_preimage (X := X) (Y := Y) e'.hom).symm
      _ = p.ι.mapIso e := congrArg (fun t ↦ p.ι.mapIso t) hbe

/-- The actual coefficient-unit identification with E concentrated in degree zero.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def unit := (unit_existsUnique D l hl E).exists.choose

/-- Evaluate at 1 after the coefficient-unit, fibre, and canonical shift comparisons.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def realize (N : C D l E) (i : ℤ) (x : U D l hl E ⟶ N⟦i⟧) :
    (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) i).obj ((F D l hl E).obj N) :=
  ((DerivedCategory.homSingleToHomology (ModuleCat.of.{u} E E) 0
    (((F D l hl E).obj N)⟦i⟧)
    ((unit D l hl E).inv ≫ (F D l hl E).map x ≫
      (Functor.commShiftIso (F D l hl E) (self := fShift D l hl E) i).hom.app N)) ≫
        (((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).shiftIso
          i 0 i (add_zero i)).hom.app ((F D l hl E).obj N))).hom 1

/-- The ambient realization of the rational point fibre is full.
Proof: take the rational equivalence component of point_fibre_equivalence, then
compose its full functor with the full inclusion of bounded finite-dimensional objects.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem full : (F D l hl E).Full := by
  let := pointRationalFibre_equivalence D l hl E
  infer_instance

/-- The ambient realization of the rational point fibre is faithful.
Proof: take the rational equivalence component of point_fibre_equivalence, then
compose its faithful functor with the faithful full-subcategory inclusion.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem faithful : (F D l hl E).Faithful := by
  let := pointRationalFibre_equivalence D l hl E
  infer_instance

/-- Point cohomology is canonically represented by maps from the coefficient unit.
Proof: point_fibre_equivalence is fully faithful. The canonical unit and shift
isomorphisms identify these maps with maps from E in degree zero to F(N)[i].
The regular module is projective, so homSingleEquivOfProjective identifies these
with linear maps E to H^i(F(N)). Evaluation at 1 is a bijection, with inverse
sending a vector to its scalar-span map.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem realize_bijective (N : C D l E) (i : ℤ) :
    Function.Bijective (realize D l hl E N i) := by
  let := full D l hl E
  let := faithful D l hl E
  let ff : (F D l hl E).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e₁ := ff.homEquiv
    (X := U D l hl E) (Y := N⟦i⟧)
  let e₂ := (unit D l hl E).homCongr
    ((Functor.commShiftIso (F D l hl E) (self := fShift D l hl E) i).app N)
  let e₃ := DerivedCategory.homSingleEquivOfProjective (ModuleCat.of.{u} E E) 0
    (((F D l hl E).obj N)⟦i⟧)
  let e₄ := (Iso.refl (ModuleCat.of.{u} E E)).homCongr
    (((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) 0).shiftIso
      i 0 i (add_zero i)).app ((F D l hl E).obj N))
  let V := (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) i).obj
    ((F D l hl E).obj N)
  let e₅ := (ModuleCat.homLinearEquiv (S := E)
    (M := ModuleCat.of.{u} E E) (N := V)).toEquiv.trans
      (LinearMap.ringLmapEquivSelf E E V).toEquiv
  convert (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))).bijective using 1
  funext x
  simp only [realize, Equiv.trans_apply, e₁, e₂, e₃, e₄, e₅,
    Functor.FullyFaithful.homEquiv_apply, LinearEquiv.coe_toEquiv,
    LinearMap.ringLmapEquivSelf_apply]
  rfl

/-- The canonical point-Hom equivalence, oriented from representatives to cohomology.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def realization (N : C D l E) (i : ℤ) :=
  Equiv.ofBijective (realize D l hl E N i) (realize_bijective D l hl E N i)

/-- The point tensor comparison is fixed by the existing representative normalization.
Proof: use pointFibreDerivedTensor over an algebraic closure of the finite field E.
Its rational comparison has exactly these endpoints. Its pure-tensor, quotient,
and full Roos-coordinate normalizations determine it on good representatives;
localization and faithful carrier descent determine it on every rational arrow.
Thus every canonical comparison family, over every algebraic closure, gives the
same map. The map and inverse satisfy the inverse identities and are unique.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem tensor_existsUnique (M N : C D l E) :
    ∃! e : (F D l hl E).obj ((T D l hl E).obj (M, N)) ≅
        (F D l hl E).obj M ⊗ (F D l hl E).obj N,
      ∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (S : PointFibreDerivedTensorSystem D l hl Ω),
        Nonempty (PointFibreDerivedTensorCanonical D l hl Ω S) →
          HEq e.hom ((S.rational E).tensorIso M N).hom := by
  obtain ⟨S₀, h₀⟩ := pointFibreDerivedTensor D l hl (AlgebraicClosure E)
  let e : (F D l hl E).obj ((T D l hl E).obj (M, N)) ≅
      (F D l hl E).obj M ⊗ (F D l hl E).obj N := (S₀.rational E).tensorIso M N
  have he : ∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (S : PointFibreDerivedTensorSystem D l hl Ω),
      Nonempty (PointFibreDerivedTensorCanonical D l hl Ω S) →
        HEq e.hom ((S.rational E).tensorIso M N).hom := by
    intro Ω _ _ _ S hS
    exact point_tensor_normalization_independent D l hl E _ Ω S₀ S h₀ hS M N
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact Iso.ext (eq_of_heq (he' (AlgebraicClosure E) S₀ h₀))

/-- The already normalized point tensor comparison, independent of closure presentation.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def tensor (M N : C D l E) := (tensor_existsUnique D l hl E M N).exists.choose

/-- Extract the second shift first, then the first, without swapping factors.
Full faithfulness reflects the field total-tensor comparison. The chosen order
gives precisely the coefficient (-1)^(j*p) on first shifted degree p.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def tensorShift (M N : C D l E) (i j : ℤ) :
    (T D l hl E).obj (M⟦i⟧,N⟦j⟧) ≅ ((T D l hl E).obj (M, N))⟦i + j⟧ :=
  let := full D l hl E
  let := faithful D l hl E
  (F D l hl E).preimageIso
    (tensor D l hl E (M⟦i⟧) (N⟦j⟧) ≪≫
      (MonoidalCategory.tensor _).mapIso
        (((Functor.commShiftIso (F D l hl E) (self := fShift D l hl E) i).app M).prod
          ((Functor.commShiftIso (F D l hl E) (self := fShift D l hl E) j).app N)) ≪≫
      (((curriedTensor (DerivedCategory (ModuleCat.{u} E))).obj
        (((F D l hl E).obj M)⟦i⟧)).commShiftIso j).app ((F D l hl E).obj N) ≪≫
      (shiftFunctor _ j).mapIso
        ((((curriedTensor (DerivedCategory (ModuleCat.{u} E))).flip.obj
          ((F D l hl E).obj N)).commShiftIso i).app ((F D l hl E).obj M)) ≪≫
      ((shiftFunctorAdd _ i j).app
        ((F D l hl E).obj M ⊗ (F D l hl E).obj N)).symm ≪≫
      (shiftFunctor _ (i + j)).mapIso (tensor D l hl E M N).symm ≪≫
      ((Functor.commShiftIso (F D l hl E) (self := fShift D l hl E) (i + j)).app
        ((T D l hl E).obj (M, N))).symm)

/-- The inverse tensor-unit constraint, reflected through the normalized point equivalence.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def j : U D l hl E ⟶ (T D l hl E).obj (U D l hl E, U D l hl E) :=
  let := full D l hl E
  (F D l hl E).preimage
    ((unit D l hl E).hom ≫
      (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} E)).hom ≫
      (λ_ (𝟙_ (DerivedCategory (ModuleCat.{u} E)))).inv ≫
      (((DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} E)).inv ≫
        (unit D l hl E).inv) ⊗ₘ
       ((DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} E)).inv ≫
        (unit D l hl E).inv)) ≫ (tensor D l hl E (U D l hl E) (U D l hl E)).inv)


/-- The canonical pullback tensor isomorphism of the recorded dependency.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def mu (M N : C D l E) :
    (P D l hl E).obj ((T D l hl E).obj (M, N)) ≅
      (T D l hl E).obj ((P D l hl E).obj M, (P D l hl E).obj N) :=
  @canonicalRationalPullbackTensor l _ E _ _ _ _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl) M N

/-- Point Frobenius: canonical transport followed by the rational Weil isomorphism.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def frobenius (N : C D l E) (theta : (P D l hl E).obj N ≅ N) :=
  iota D l hl E N ≫ (F D l hl E).map theta.hom

/-- The transported shifted representative: c inverse, then P(x), then pullback shift.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def transportRep (N : C D l E) (r : ℤ) (x : U D l hl E ⟶ N⟦r⟧) :=
  (c D l hl E).inv ≫ (P D l hl E).map x ≫ (pShift D l hl E r N).hom

/-- The Frobenius representative, postcomposing transportRep with the shifted Weil map.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def frobeniusRep (N : C D l E) (theta : (P D l hl E).obj N ≅ N)
    (r : ℤ) (x : U D l hl E ⟶ N⟦r⟧) :=
  transportRep D l hl E N r x ≫ theta.hom⟦r⟧'

/-- The induced Weil datum on every integer shift.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def shiftedTheta (N : C D l E) (theta : (P D l hl E).obj N ≅ N) (r : ℤ) :=
  pShift D l hl E r N ≪≫ (shiftFunctor _ r).mapIso theta

/-- Tensor the two ordered representatives and compose with B.
The second input is identified with D[n][-i]; the signed comparison then removes
the shifts i and -i, and the shift-zero constraint gives the target of B.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def pairingEnd (A D₁ : C D l E) (n i : ℤ)
    (B : (T D l hl E).obj (A, D₁⟦n⟧) ⟶ U D l hl E)
    (x : U D l hl E ⟶ A⟦i⟧) (y : U D l hl E ⟶ D₁⟦n - i⟧) :
    U D l hl E ⟶ U D l hl E :=
  j D l hl E ≫ (T D l hl E).map
    (Prod.mkHom x (y ≫ (shiftFunctorAdd' (C D l E) n (-i) (n - i)
      (sub_eq_add_neg n i).symm).hom.app D₁)) ≫
    (tensorShift D l hl E A (D₁⟦n⟧) i (-i)).hom ≫
    eqToHom (congrArg (fun r : ℤ ↦ ((T D l hl E).obj (A, D₁⟦n⟧))⟦r⟧)
      (add_neg_cancel i)) ≫
    (shiftFunctorZero (C D l E) ℤ).hom.app _ ≫ B

/-- Tensor the ordered representatives before applying a pairing morphism.
Source: retained point-pairing proof Step 5.
(blueprint: def-pod-point-weil-pairing-coordinates). -/
def pairingVector (A D₁ : C D l E) (n i : ℤ)
    (x : U D l hl E ⟶ A⟦i⟧) (y : U D l hl E ⟶ D₁⟦n - i⟧) :
    U D l hl E ⟶ (T D l hl E).obj (A, D₁⟦n⟧) :=
  j D l hl E ≫ (T D l hl E).map
    (Prod.mkHom x (y ≫ (shiftFunctorAdd' (C D l E) n (-i) (n - i)
      (sub_eq_add_neg n i).symm).hom.app D₁)) ≫
    (tensorShift D l hl E A (D₁⟦n⟧) i (-i)).hom ≫
    eqToHom (congrArg (fun r : ℤ ↦ ((T D l hl E).obj (A, D₁⟦n⟧))⟦r⟧)
      (add_neg_cancel i)) ≫
    (shiftFunctorZero (C D l E) ℤ).hom.app _

/-- The canonical coefficient of a unit endomorphism, obtained by evaluating at 1.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def scalar (h : U D l hl E ⟶ U D l hl E) : E :=
  (DerivedCategory.homSingleToHomology (ModuleCat.of.{u} E E) 0
    ((DerivedCategory.singleFunctor.{u} (ModuleCat.{u} E) 0).obj (ModuleCat.of.{u} E E))
    ((unit D l hl E).inv ≫ (F D l hl E).map h ≫ (unit D l hl E).hom) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} E) 0).hom.app
        (ModuleCat.of.{u} E E)).hom 1

/-- Every unit endomorphism is a unique coefficient scalar.
Proof: full faithfulness and the normalized point unit identify End(U) with
End(E[0]). Maps from the projective regular single are maps E to E; evaluation
at 1 is a bijection. This is the degree-zero case of the point-Hom realization.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
theorem scalar_bijective : Function.Bijective (scalar D l hl E) := by
  let := full D l hl E
  let := faithful D l hl E
  let ff : (F D l hl E).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  let e₁ := ff.homEquiv
    (X := U D l hl E) (Y := U D l hl E)
  let e₂ := (unit D l hl E).homCongr (unit D l hl E)
  let e₃ := DerivedCategory.homSingleEquivOfProjective (ModuleCat.of.{u} E E) 0
    ((DerivedCategory.singleFunctor.{u} (ModuleCat.{u} E) 0).obj (ModuleCat.of.{u} E E))
  let e₄ := (Iso.refl (ModuleCat.of.{u} E E)).homCongr
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} E) 0).app
      (ModuleCat.of.{u} E E))
  let e₅ := (ModuleCat.homLinearEquiv (S := E)
    (M := ModuleCat.of.{u} E E) (N := ModuleCat.of.{u} E E)).toEquiv.trans
      (LinearMap.ringLmapEquivSelf E E E).toEquiv
  convert (e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))).bijective using 1
  funext x
  simp only [scalar, Equiv.trans_apply, e₁, e₂, e₃, e₄, e₅,
    Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply,
    DerivedCategory.homSingleEquivOfProjective_apply, LinearEquiv.coe_toEquiv,
    LinearMap.ringLmapEquivSelf_apply]
  rfl

/-- The degreewise scalar pairing obtained from the two canonical point-Hom representatives.
Source: retained rational point-pairing proof, Steps 1--7
(blueprint: lem-pod-point-weil-pairing-realization). -/
def pairing (A D₁ : C D l E) (n i : ℤ)
    (B : (T D l hl E).obj (A, D₁⟦n⟧) ⟶ U D l hl E)
    (x : (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) i).obj
      ((F D l hl E).obj A))
    (y : (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) (n - i)).obj
      ((F D l hl E).obj D₁)) : E :=
  scalar D l hl E (pairingEnd D l hl E A D₁ n i B
    ((realization D l hl E A i).symm x) ((realization D l hl E D₁ (n - i)).symm y))


end WeilConjectures.PointWeilPairing
