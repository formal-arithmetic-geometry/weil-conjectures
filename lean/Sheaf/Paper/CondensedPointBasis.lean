/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Connected.Separation
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import WeilConjectures.RingTheory.ProEtale.WeakDimension

/-!
# Affine ind-etale schemes over a separably closed field

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-prop-pe-condensed-point-basis and its proof
(blueprint: det-pe-condensed-point-basis).

## Main definitions

* `AlgebraicGeometry.ProEtale.condensedPointAlgebraFunctor`: locally constant algebras,
  contravariantly by precomposition.
* `AlgebraicGeometry.ProEtale.condensedPointSchemeFunctor`: their spectra over the field.

## Main statement

* `AlgebraicGeometry.ProEtale.condensed_point_basis`: the finite and ind-etale
  classifications, the specified Hom bijection, the equivalence onto affine ind-etale
  schemes, and its natural identification with the existing relative test-object functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The algebra part of `S ↦ Ω[S]`: the actual algebra `LocallyConstant S Ω`, with
morphisms given by precomposition. Source: main-20261015 blueprint,
sk-prop-pe-condensed-point-basis, opening paragraph and clause (3)
(blueprint: det-pe-condensed-point-basis). -/
def condensedPointAlgebraFunctor (Ω : Type u) [CommRing Ω] :
    Profinite.{u} ⥤ (CommAlgCat.{u} Ω)ᵒᵖ where
  obj S := op (CommAlgCat.of Ω (LocallyConstant S Ω))
  map f := (CommAlgCat.ofHom (LocallyConstant.comapₐ Ω f.hom.hom)).op

/-- The specified functor `S ↦ Spec LC(S,Ω)` over `Spec Ω`, with spectra of
precomposition on arrows. This uses Mathlib's existing relative spectrum functor.
Source: main-20261015 blueprint, sk-prop-pe-condensed-point-basis, final paragraph
(blueprint: det-pe-condensed-point-basis). -/
noncomputable def condensedPointSchemeFunctor (Ω : Type u) [CommRing Ω] :
    Profinite.{u} ⥤ Over (Spec (.of Ω)) :=
  condensedPointAlgebraFunctor Ω ⋙ algSpec (.of Ω)


private lemma indEtale_of_across {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (h : RingHom.IndEtaleAcrossUniverses (algebraMap R A)) : Algebra.IndEtale R A := by
  have hP := RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  exact (RingHom.IndEtale.algebraMap_iff R A).mp
    (hP.1 _ ULift.ringEquiv (hP.2 _ ULift.ringEquiv.symm h))

private noncomputable def pointEval (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A] (p : PrimeSpectrum A) : A →ₐ[Ω] Ω :=
  have := Algebra.IndEtale.isSeparable_residueField_of_field (K := Ω) p.asIdeal
  (AlgEquiv.ofBijective (Algebra.ofId Ω p.asIdeal.ResidueField)
    (IsSepClosed.algebraMap_bijective Ω p.asIdeal.ResidueField)).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom Ω A p.asIdeal.ResidueField)

private lemma pointEval_eq_zero_iff (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A] (p : PrimeSpectrum A) (a : A) :
    pointEval Ω A p a = 0 ↔ a ∈ p.asIdeal := by
  dsimp [pointEval]
  rw [map_eq_zero_iff _ (AlgEquiv.injective _)]
  exact Ideal.algebraMap_residueField_eq_zero

private lemma pointEval_comp (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A]
    {B : Type u} [CommRing B] [Algebra Ω B] [Algebra.Etale Ω B]
    (f : B →ₐ[Ω] A) (p : PrimeSpectrum A) :
    (pointEval Ω A p).comp f =
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω B).symm
        (PrimeSpectrum.comap f.toRingHom p) := by
  apply (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω B).injective
  rw [Equiv.apply_symm_apply]
  ext a
  exact pointEval_eq_zero_iff Ω A p (f a)

private lemma pointEval_isLocallyConstant (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A] (a : A) :
    IsLocallyConstant (fun p : PrimeSpectrum A ↦ pointEval Ω A p a) := by
  obtain ⟨I, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := Ω) (S := A)
  obtain ⟨i, b, rfl⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
    (CategoryTheory.Limits.isColimitOfPreserves (forget (CommAlgCat Ω)) P.isColimit) a
  have := hP i
  have := Algebra.FormallyUnramified.finite_of_free Ω (P.diag.obj i)
  have : IsArtinianRing (P.diag.obj i) := isArtinian_of_tower Ω inferInstance
  have h := (IsLocallyConstant.of_discrete
    (fun q : PrimeSpectrum (P.diag.obj i) ↦
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω (P.diag.obj i)).symm q b)).comp_continuous
        (PrimeSpectrum.continuous_comap (P.ι.app i).hom.toRingHom)
  change IsLocallyConstant (fun p : PrimeSpectrum A ↦
    pointEval Ω A p ((P.ι.app i).hom b))
  have he : (fun p : PrimeSpectrum A ↦ pointEval Ω A p ((P.ι.app i).hom b)) =
      (fun p ↦ ((Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω
        (P.diag.obj i)).symm (PrimeSpectrum.comap (P.ι.app i).hom.toRingHom p)) b) := by
    funext p
    exact DFunLike.congr_fun (pointEval_comp Ω A (P.ι.app i).hom p) b
  rw [he]
  exact h

private lemma indEtale_totallySeparated (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A] :
    TotallySeparatedSpace (PrimeSpectrum A) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro p q hpq
  obtain ⟨a, ha⟩ : ∃ a : A, ¬ (a ∈ p.asIdeal ↔ a ∈ q.asIdeal) :=
    not_forall.mp fun h ↦ hpq (PrimeSpectrum.ext (Ideal.ext h))
  have hne : pointEval Ω A p a ≠ pointEval Ω A q a := by
    intro he
    apply ha
    rw [← pointEval_eq_zero_iff Ω A p a, ← pointEval_eq_zero_iff Ω A q a, he]
  exact ⟨_, (pointEval_isLocallyConstant Ω A a).isClopen_fiber (pointEval Ω A p a),
    rfl, hne.symm⟩

private noncomputable def pointEvaluation (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A] :
    A →ₐ[Ω] LocallyConstant (PrimeSpectrum A) Ω where
  toFun a := ⟨fun p ↦ pointEval Ω A p a, pointEval_isLocallyConstant Ω A a⟩
  map_one' := by ext p; exact map_one (pointEval Ω A p)
  map_mul' a b := by ext p; exact map_mul (pointEval Ω A p) a b
  map_zero' := by ext p; exact map_zero (pointEval Ω A p)
  map_add' a b := by ext p; exact map_add (pointEval Ω A p) a b
  commutes' r := by ext p; exact (pointEval Ω A p).commutes r

private lemma pointEvaluation_bijective (Ω A : Type u) [Field Ω] [IsSepClosed Ω]
    [CommRing A] [Algebra Ω A] [Algebra.IndEtale Ω A] :
    Function.Bijective (pointEvaluation Ω A) := by
  classical
  have : Ring.AbsolutelyFlat A := Ring.AbsolutelyFlat.of_flat_lmul' Ω A
    (Algebra.WeaklyEtale.flat_lmul' Ω A)
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply isNilpotent_iff_eq_zero.mp
    rw [nilpotent_iff_mem_prime]
    intro P hP
    have := hP
    apply (pointEval_eq_zero_iff Ω A ⟨P, hP⟩ (a - b)).mp
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun f : LocallyConstant (PrimeSpectrum A) Ω ↦ f ⟨P, hP⟩) hab
  · intro f
    refine ⟨LocallyConstant.liftPrimeSpectrum (algebraMap Ω A) ⟨id, continuous_id⟩ f, ?_⟩
    ext p
    have h := LocallyConstant.liftPrimeSpectrum_sub_mem (algebraMap Ω A)
      (⟨id, continuous_id⟩ : C(PrimeSpectrum A, PrimeSpectrum A)) f p
    have he := (pointEval_eq_zero_iff Ω A p _).mpr h
    rw [map_sub] at he
    change pointEval Ω A p
        (LocallyConstant.liftPrimeSpectrum (algebraMap Ω A)
          (⟨id, continuous_id⟩ : C(PrimeSpectrum A, PrimeSpectrum A)) f) -
        pointEval Ω A p (algebraMap Ω A (f p)) = 0 at he
    have he' := sub_eq_zero.mp he
    change pointEval Ω A p _ = f p
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using he'


/-- The algebra classification and the specified Hom bijection give the equivalence
onto affine ind-etale schemes. Source: main-20261015 blueprint,
`sk-prop-pe-condensed-point-basis`, proof step 9
(blueprint: det-pe-condensed-point-basis).

Proof: the Hom bijection makes the locally constant algebra functor fully faithful.
Compose it with the fully faithful relative spectrum functor. Every object has
ind-etale structure map, so lift to the indicated full subcategory. An affine scheme
over the field is the relative spectrum of its algebra of global sections. Its
pro-affine-etale property makes that algebra ind-etale; the algebra classification
therefore identifies it with a locally constant algebra. This proves essential
surjectivity, hence the lifted functor is an equivalence. -/
private theorem condensed_point_basis_scheme_equivalence (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (hclass : ∀ (A : Type u) [CommRing A] [Algebra Ω A],
      RingHom.IndEtale (algebraMap Ω A) →
      ∃ S : Profinite.{u}, Nonempty (A ≃ₐ[Ω] LocallyConstant S Ω))
    (hind : ∀ S : Profinite.{u},
      RingHom.IndEtale (algebraMap Ω (LocallyConstant S Ω)))
    (hhom : ∀ S T : Profinite.{u}, Function.Bijective
      (fun s : C(T, S) ↦ (LocallyConstant.comapₐ Ω s :
        LocallyConstant S Ω →ₐ[Ω] LocallyConstant T Ω))) :
    ∃ E : Profinite.{u} ≌ ObjectProperty.FullSubcategory
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom),
      Nonempty (E.functor ⋙ ObjectProperty.ι
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom) ≅
          condensedPointSchemeFunctor Ω) := by
  classical
  let F := condensedPointAlgebraFunctor Ω
  have hF : F.FullyFaithful := by
    apply Nonempty.some
    apply (Functor.FullyFaithful.nonempty_iff_map_bijective F).mpr
    intro S T
    constructor
    · intro f g h
      apply ConcreteCategory.hom_ext
      exact ContinuousMap.congr_fun ((hhom T S).injective
        (congrArg (fun k ↦ k.unop.hom) h))
    · intro f
      obtain ⟨s, hs⟩ := (hhom T S).surjective f.unop.hom
      refine ⟨ConcreteCategory.ofHom s, ?_⟩
      apply Quiver.Hom.unop_inj
      exact CommAlgCat.hom_ext hs
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  let P : ObjectProperty (Over (Spec (.of Ω))) :=
    fun Y ↦ IsAffine Y.left ∧ proAffineEtale Y.hom
  have hP : ∀ S, P ((condensedPointSchemeFunctor Ω).obj S) := by
    intro S
    change IsAffine (Spec (.of (LocallyConstant S Ω))) ∧ _
    exact ⟨inferInstance, proAffineEtale_Spec_iff.mpr (hind S)⟩
  let G := P.lift (condensedPointSchemeFunctor Ω) hP
  have hcomp : (condensedPointSchemeFunctor Ω).FullyFaithful :=
    hF.comp (algSpec.fullyFaithful (R := .of Ω))
  have : (condensedPointSchemeFunctor Ω).Full := hcomp.full
  have : (condensedPointSchemeFunctor Ω).Faithful := hcomp.faithful
  have : G.EssSurj := by
    constructor
    intro Y
    obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr Y.property.1
    have hA : proAffineEtale ((algSpec (.of Ω)).obj A).hom := by
      rw [← e.hom.w, MorphismProperty.cancel_left_of_respectsIso (P := proAffineEtale)]
      exact Y.property.2
    have hi : RingHom.IndEtale (algebraMap Ω A.unop) :=
      proAffineEtale_Spec_iff.mp hA
    obtain ⟨S, ⟨eA⟩⟩ := hclass A.unop hi
    exact ⟨S, ⟨P.isoMk ((algSpec (.of Ω)).mapIso (CommAlgCat.isoMk eA).op ≪≫ e)⟩⟩
  have : G.IsEquivalence := {}
  exact ⟨G.asEquivalence, ⟨P.liftCompιIso _ hP⟩⟩


private noncomputable def componentMap {S : Profinite.{u}} {B : Type u} [CommRing B]
    (φ : LocallyConstant S ℤ →+* B) : C(PrimeSpectrum B, S) :=
  ⟨fun p ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      (PrimeSpectrum.comap φ p)).1,
    continuous_fst.comp
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous.comp
        (PrimeSpectrum.continuous_comap φ))⟩

private lemma map_localization_eq_eval {S : Profinite.{u}} {R : Type*} {B : Type u}
    [CommRing R] [CommRing B] (φ : LocallyConstant S ℤ →+* B)
    (h : LocallyConstant S R →+* B)
    (hh : h.comp (LocallyConstant.mapRingHom (Int.castRingHom R)) = φ)
    (p : PrimeSpectrum B) (g : LocallyConstant S R) :
    algebraMap B (Localization.AtPrime p.asIdeal) (h g) =
      algebraMap B (Localization.AtPrime p.asIdeal)
        (h (algebraMap R (LocallyConstant S R) (g (componentMap φ p)))) := by
  classical
  let s := componentMap φ p
  let q := ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
    (PrimeSpectrum.comap φ p)).2
  have hp : PrimeSpectrum.comap φ p = LocallyConstant.toPrimeSpectrum (s, q) :=
    ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).apply_symm_apply _).symm
  let χ := LocallyConstant.charFn ℤ (g.isLocallyConstant.isClopen_fiber (g s))
  let χR := LocallyConstant.mapRingHom (Int.castRingHom R) χ
  have hχ : h χR ∉ p.asIdeal := by
    have he : h χR = φ χ := DFunLike.congr_fun hh χ
    rw [he]
    change χ ∉ (PrimeSpectrum.comap φ p).asIdeal
    rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
    simpa [χ, LocallyConstant.charFn_apply_of_mem] using q.isPrime.one_notMem
  have hid : IsIdempotentElem χR := by
    change χR * χR = χR
    ext x
    change (χ x : R) * (χ x : R) = (χ x : R)
    by_cases hx : g x = g s
    · simp [χ, LocallyConstant.charFn_apply_of_mem, hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have hχloc : algebraMap B (Localization.AtPrime p.asIdeal) (h χR) = 1 :=
    (hid.map h).algebraMap_localization_atPrime_of_notMem hχ
  have hmul : χR * g = χR * algebraMap R (LocallyConstant S R) (g s) := by
    ext x
    change (χ x : R) * g x = (χ x : R) * g s
    by_cases hx : g x = g s
    · rw [hx]
    · simp [χ, LocallyConstant.charFn_apply_of_notMem, hx]
  have he := congrArg (fun v ↦ algebraMap B (Localization.AtPrime p.asIdeal) (h v)) hmul
  simpa only [map_mul, hχloc, one_mul] using he

private lemma lift_restrict {S : Profinite.{u}} {R B : Type u}
    [CommRing R] [CommRing B] (φ : LocallyConstant S ℤ →+* B) (ψ : R →+* B) :
    (LocallyConstant.liftPrimeSpectrum ψ (componentMap φ)).comp
      (LocallyConstant.mapRingHom (Int.castRingHom R)) = φ := by
  ext g
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  rw [RingHom.comp_apply, LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
  have he := map_localization_eq_eval φ φ (by ext f; rfl) p g
  change algebraMap B (Localization.AtPrime p.asIdeal) (ψ (g (componentMap φ p) : R)) = _
  change algebraMap B (Localization.AtPrime p.asIdeal) (φ g) =
    algebraMap B (Localization.AtPrime p.asIdeal)
      (φ (g (componentMap φ p) : LocallyConstant S ℤ)) at he
  simpa only [map_intCast] using he.symm

private lemma lift_unique {S : Profinite.{u}} {R B : Type u}
    [CommRing R] [CommRing B] (φ : LocallyConstant S ℤ →+* B) (ψ : R →+* B)
    (h : LocallyConstant S R →+* B)
    (hh : h.comp (LocallyConstant.mapRingHom (Int.castRingHom R)) = φ)
    (hc : h.comp (algebraMap R (LocallyConstant S R)) = ψ) :
    h = LocallyConstant.liftPrimeSpectrum ψ (componentMap φ) := by
  ext g
  apply PrimeSpectrum.eq_of_forall_algebraMap_localization_eq
  intro p
  rw [LocallyConstant.algebraMap_localization_liftPrimeSpectrum]
  have he := map_localization_eq_eval φ h hh p g
  rw [show h (algebraMap R (LocallyConstant S R) (g (componentMap φ p))) =
    ψ (g (componentMap φ p)) from DFunLike.congr_fun hc _] at he
  exact he

open CategoryTheory.Limits in
private theorem locallyConstant_pushout (R : Type u) [CommRing R] (S : Profinite.{u}) :
    IsPushout
      (CommRingCat.ofHom ((algebraMap ℤ (LocallyConstant S ℤ)).comp
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))
      (CommRingCat.ofHom ((Int.castRingHom R).comp
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))
      (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R)))
      (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))) := by
  let c : PushoutCocone
      (CommRingCat.ofHom ((algebraMap ℤ (LocallyConstant S ℤ)).comp
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))
      (CommRingCat.ofHom ((Int.castRingHom R).comp
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)) := PushoutCocone.mk
    (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R) :
      LocallyConstant S ℤ →+* LocallyConstant S R))
    (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))) (by ext n x; rfl)
  apply IsPushout.of_isColimit (c := c)
  refine PushoutCocone.IsColimit.mk _
    (fun t ↦ CommRingCat.ofHom
      (LocallyConstant.liftPrimeSpectrum t.inr.hom (componentMap t.inl.hom))) ?_ ?_ ?_
  · intro t
    exact CommRingCat.hom_ext (lift_restrict t.inl.hom t.inr.hom)
  · intro t
    ext r
    exact LocallyConstant.liftPrimeSpectrum_algebraMap _ _ r
  · intro t m hl hr
    exact CommRingCat.hom_ext (lift_unique t.inl.hom t.inr.hom m.hom
      (congrArg CommRingCat.Hom.hom hl) (congrArg CommRingCat.Hom.hom hr))

open CategoryTheory.Limits in
private theorem comparisonSquare (R : Type u) [CommRing R] (S : Profinite.{u}) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (LocallyConstant.mapRingHom (Int.castRingHom R) :
        LocallyConstant S ℤ →+* LocallyConstant S R)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (LocallyConstant S R))))
      (toSpecZ (Spec (.of (LocallyConstant S ℤ)))) (toSpecZ (Spec (.of R))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (locallyConstant_pushout R S)
  convert h using 1 <;> exact specULiftZIsTerminal.hom_ext _ _

open CategoryTheory.Limits in
private noncomputable def comparisonIso (R : Type u) [CommRing R] (S : Profinite.{u}) :
    (condensedPointSchemeFunctor R).obj S ≅
      (profiniteToProEtOf (Spec (.of R)) ⋙ Scheme.ProEt.forget (Spec (.of R))).obj S :=
  Over.isoMk (comparisonSquare R S).isoPullback
    (comparisonSquare R S).isoPullback_hom_snd

open CategoryTheory.Limits in
/-- The specified spectrum functor agrees with the relative test-object functor.
Source: main-20261015 blueprint, condensed point basis, final paragraph
(blueprint: det-pe-condensed-point-basis).

Proof: the characteristic function of the fibre of a locally constant function at a
point is one after localization at that point. Thus maps from LC(S, R) are determined
by the scalar map and the induced component map from Spec of the target to S.
`liftPrimeSpectrum` constructs the unique such map, proving that LC(S, R) is the
pushout of LC(S, ℤ) and R over ℤ. Taking spectra gives the defining base-change
pullback for the relative test object. The comparison is over Spec R, and its two
projections prove naturality, since precomposition commutes with scalar extension. -/
private theorem condensed_point_basis_test_functor (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    Nonempty (condensedPointSchemeFunctor Ω ≅
      profiniteToProEtOf (Spec (.of Ω)) ⋙ Scheme.ProEt.forget (Spec (.of Ω))) := by
  refine ⟨NatIso.ofComponents (comparisonIso Ω) ?_⟩
  intro S T f
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change Spec.map (CommRingCat.ofHom (LocallyConstant.comapRingHom f.hom.hom)) ≫
        (comparisonSquare Ω T).isoPullback.hom ≫ pullback.fst _ _ =
      (comparisonSquare Ω S).isoPullback.hom ≫
        (pullback.lift (pullback.fst _ _ ≫ profiniteToScheme.map f)
          (pullback.snd _ _) _) ≫ pullback.fst _ _
    rw [IsPullback.isoPullback_hom_fst, pullback.lift_fst,
      ← Category.assoc, IsPullback.isoPullback_hom_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫
      Spec.map (CommRingCat.ofHom (LocallyConstant.comapRingHom f.hom.hom :
        LocallyConstant T ℤ →+* LocallyConstant S ℤ))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · change Spec.map (CommRingCat.ofHom (LocallyConstant.comapRingHom f.hom.hom)) ≫
        (comparisonSquare Ω T).isoPullback.hom ≫ pullback.snd _ _ =
      (comparisonSquare Ω S).isoPullback.hom ≫
        (pullback.lift (pullback.fst _ _ ≫ profiniteToScheme.map f)
          (pullback.snd _ _) _) ≫ pullback.snd _ _
    rw [IsPullback.isoPullback_hom_snd, pullback.lift_snd,
      IsPullback.isoPullback_hom_snd, ← Spec.map_comp]
    rfl

/-- Over a separably closed field, finitely presented etale algebras are finite
powers, ind-etale algebras are exactly locally constant algebras on profinite spaces,
and all algebra maps between these algebras are uniquely continuous precompositions.
The specified spectrum functor gives the equivalence onto the full category of affine
ind-etale schemes over the field, and is naturally the relative test-object functor.

Source: main-20261015 blueprint, sk-prop-pe-condensed-point-basis, all three numbered
clauses and the final paragraph (blueprint: det-pe-condensed-point-basis).

Proof plan, following the node's nine steps:
1. `lem-weil-pbc-etale-ring-map-iff-etale-affine` and
   `lem-weil-pbc-etale-algebra-over-field-product` express a finite-stage algebra as a
   finite product of finite separable fields. `lem-pc-sepclosed-finite-sep-trivial`
   identifies each factor with Ω. Number the finite set, retaining the empty product.
   Conversely use `lem-weil-pbc-finite-separable-extension-etale` on Ω and
   `lem-weil-pbc-etale-algebra-finite-product` on its finite powers.
2. An algebra map from Ω^F is determined by its orthogonal characteristic idempotents,
   whose sum is one. In LC(T,Ω) their fibers at one give a clopen partition of T,
   including empty blocks. This is exactly a continuous map T → F; the algebra map
   is precomposition. For empty F it exists precisely when the target is zero.
3. For any small cofiltered diagram of finite spaces, realize the limit as compatible
   tuples in the product. The compatibility conditions are closed. Use
   `lem-weil-pbc-tychonoff-product-quasi-compact` and
   `lem-weil-pbc-closed-in-quasi-compact` for compactness. Coordinates separate points
   and force connected subsets to be singletons. Thus the limit is profinite,
   with the usual universal property, including empty factors and empty limits.
4. Index finite clopen partitions by refinement. Common refinements show cofilteredness.
   The canonical map from a profinite space to the limit of its finite quotients is
   injective by `lem-weil-pbc-profinite-clopen-basis`, and surjective by compactness
   and the finite intersection property of compatible blocks. Apply
   `lem-weil-pbc-compact-hausdorff-bijection`. For an empty space use its empty quotient.
5. If two functions at one finite stage agree on the limit, they agree after some
   transition: otherwise compactness of the product would give a compatible tuple
   where they differ. Explicitly choose a finite incompatible subfamily and a cone
   over its finitely many objects and arrows, equalizing parallel composites using
   `def-weil-pbc-category-colimit`. An empty stage is handled by a common predecessor.
6. `lem-weil-pbc-profinite-limit-function-factorization` factors every locally constant
   function through a finite stage. Step 5 makes evaluation by any compatible algebra
   cocone independent of the representative. Put finitely many representatives at a
   common stage to check ring operations and scalars. This is the colimit universal
   property of `def-weil-pbc-category-colimit`. It is also a ring colimit: all stage
   scalar maps agree by filteredness and the index category is nonempty.
7. Apply this colimit property to finite quotients of S. Step 2 identifies algebra maps
   to LC(T,Ω) with compatible continuous maps to the finite quotients of S. Step 4
   gives a unique continuous T → S. On a representative h = f ∘ q its algebra map is
   h ↦ f ∘ q ∘ s = h ∘ s, compatibly with identities and composition.
8. Use `def-weil-pbc-ind-etale-algebra` to present an ind-etale algebra by finite-stage
   etale algebras. Step 1 gives finite powers, and step 2 gives the opposite finite
   diagram. Steps 3 and 6 identify its colimit with LC(S,Ω). Conversely the finite
   quotients of every S give a filtered etale presentation of LC(S,Ω).
9. `def-weil-affine-spectrum` translates step 7 to full faithfulness and step 8 to
   essential surjectivity onto affine ind-etale schemes. For the final comparison use
   `def-sfb-profinite-test-objects`, `lem-weil-pbc-finite-affine-coproduct-spectrum`
   and `lem-weil-pbc-spec-small-colimit-limit`: both functors are limits of the same
   finite coproduct diagram over Spec Ω. Their unique limit comparison is over Ω
   and natural because transitions and maps are spectra of precomposition. -/
theorem condensed_point_basis (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (∀ (A : Type u) [CommRing A] [Algebra Ω A],
      Algebra.Etale Ω A → Algebra.FinitePresentation Ω A →
      ∃ n : ℕ, Nonempty (A ≃ₐ[Ω] (Fin n → Ω))) ∧
    (∀ (A : Type u) [CommRing A] [Algebra Ω A],
      RingHom.IndEtaleAcrossUniverses (algebraMap Ω A) →
      ∃ S : Profinite.{u}, Nonempty (A ≃ₐ[Ω] LocallyConstant S Ω)) ∧
    (∀ S : Profinite.{u},
      RingHom.IndEtaleAcrossUniverses (algebraMap Ω (LocallyConstant S Ω))) ∧
    (∀ S T : Profinite.{u}, Function.Bijective
      (fun s : C(T, S) ↦ (LocallyConstant.comapₐ Ω s :
        LocallyConstant S Ω →ₐ[Ω] LocallyConstant T Ω))) ∧
    (∃ E : Profinite.{u} ≌ ObjectProperty.FullSubcategory
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom),
      Nonempty (E.functor ⋙ ObjectProperty.ι
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom) ≅
          condensedPointSchemeFunctor Ω)) ∧
    Nonempty (condensedPointSchemeFunctor Ω ≅
      profiniteToProEtOf (Spec (.of Ω)) ⋙ Scheme.ProEt.forget (Spec (.of Ω))) := by
  classical
  have halg :
    (∀ (A : Type u) [CommRing A] [Algebra Ω A],
      Algebra.Etale Ω A → Algebra.FinitePresentation Ω A →
      ∃ n : ℕ, Nonempty (A ≃ₐ[Ω] (Fin n → Ω))) ∧
    (∀ (A : Type u) [CommRing A] [Algebra Ω A],
      RingHom.IndEtaleAcrossUniverses (algebraMap Ω A) →
      ∃ S : Profinite.{u}, Nonempty (A ≃ₐ[Ω] LocallyConstant S Ω)) ∧
    (∀ S : Profinite.{u},
      RingHom.IndEtaleAcrossUniverses (algebraMap Ω (LocallyConstant S Ω))) ∧
    (∀ S T : Profinite.{u}, Function.Bijective
      (fun s : C(T, S) ↦ (LocallyConstant.comapₐ Ω s :
        LocallyConstant S Ω →ₐ[Ω] LocallyConstant T Ω))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro A _ _ hA _
      let := hA
      let := Algebra.Etale.finite_primeSpectrum Ω A
      let := Fintype.ofFinite (PrimeSpectrum A)
      exact ⟨Fintype.card (PrimeSpectrum A),
        ⟨(Algebra.FormallyEtale.equivPiOfIsSepClosed Ω A).trans
          (AlgEquiv.piCongrLeft Ω (fun _ ↦ Ω) (Fintype.equivFin (PrimeSpectrum A)))⟩⟩
    · intro A _ _ hA
      let : Algebra.IndEtale Ω A := indEtale_of_across hA
      let := indEtale_totallySeparated Ω A
      exact ⟨Profinite.of (PrimeSpectrum A),
        ⟨AlgEquiv.ofBijective (pointEvaluation Ω A) (pointEvaluation_bijective Ω A)⟩⟩
    · intro S
      exact (RingHom.IndZariski.respectsIso.1 _ ULift.ringEquiv.symm
        (RingHom.IndZariski.respectsIso.2 _ ULift.ringEquiv
          ((RingHom.IndZariski.algebraMap_iff Ω (LocallyConstant S Ω)).mpr
            inferInstance))).indEtale
    · intro S T
      constructor
      · intro f g h
        apply ContinuousMap.ext
        intro t
        by_contra hne
        have : TotallySeparatedSpace S := loc_compact_t2_tot_disc_iff_tot_sep.mp inferInstance
        obtain ⟨U, hU, hf, hg⟩ := exists_isClopen_of_totally_separated hne
        have he := congrArg (fun ψ : LocallyConstant S Ω →ₐ[Ω] LocallyConstant T Ω ↦
          ψ (LocallyConstant.charFn Ω hU) t) h
        simp [LocallyConstant.charFn_apply_of_mem hU hf,
          LocallyConstant.charFn_apply_of_notMem hU hg] at he
      · intro φ
        let p : PrimeSpectrum Ω := ⟨⊥, inferInstance⟩
        let s : C(T, S) :=
          ⟨fun t ↦ ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := Ω)).symm
            (PrimeSpectrum.comap φ.toRingHom (LocallyConstant.toPrimeSpectrum (t, p)))).1,
          continuous_fst.comp
            ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := Ω)).symm.continuous.comp
              ((PrimeSpectrum.continuous_comap φ.toRingHom).comp
                (LocallyConstant.continuous_toPrimeSpectrum.comp
                  (continuous_id.prodMk continuous_const))))⟩
        refine ⟨s, ?_⟩
        ext f t
        have hp : PrimeSpectrum.comap φ.toRingHom (LocallyConstant.toPrimeSpectrum (t, p)) =
            LocallyConstant.toPrimeSpectrum (s t, p) := by
          have he := (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := Ω)).apply_symm_apply
            (PrimeSpectrum.comap φ.toRingHom (LocallyConstant.toPrimeSpectrum (t, p)))
          convert he.symm using 1
          exact congrArg (fun q ↦ LocallyConstant.toPrimeSpectrum (s t, q))
            (Subsingleton.elim _ _)
        have hm : f - algebraMap Ω (LocallyConstant S Ω) (f (s t)) ∈
            (PrimeSpectrum.comap φ.toRingHom (LocallyConstant.toPrimeSpectrum (t, p))).asIdeal := by
          rw [hp, LocallyConstant.mem_toPrimeSpectrum_asIdeal]
          change f (s t) - f (s t) ∈ p.asIdeal
          rw [sub_self]
          exact p.asIdeal.zero_mem
        change (φ (f - algebraMap Ω (LocallyConstant S Ω) (f (s t)))) t = 0 at hm
        change f (s t) = (φ f) t
        exact (sub_eq_zero.mp (by
          simpa only [map_sub, φ.commutes, LocallyConstant.sub_apply,
            LocallyConstant.algebraMap_apply_apply] using hm)).symm
  refine ⟨halg.1, halg.2.1, halg.2.2.1, halg.2.2.2, ?_,
    condensed_point_basis_test_functor Ω⟩
  apply condensed_point_basis_scheme_equivalence Ω
  · intro A _ _ hA
    let : Algebra.IndEtale Ω A := (RingHom.IndEtale.algebraMap_iff Ω A).mp hA
    let := indEtale_totallySeparated Ω A
    exact ⟨Profinite.of (PrimeSpectrum A),
      ⟨AlgEquiv.ofBijective (pointEvaluation Ω A) (pointEvaluation_bijective Ω A)⟩⟩
  · intro S
    exact (RingHom.IndEtale.algebraMap_iff Ω (LocallyConstant S Ω)).mpr inferInstance
  · exact halg.2.2.2

end AlgebraicGeometry.ProEtale
