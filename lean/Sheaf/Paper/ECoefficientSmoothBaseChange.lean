/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.AdicSmoothBaseChange
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.SbcFiniteWitnessRealization
import Sheaf.Paper.SbcFiniteConstructibility

/-! # Smooth base change with finite-extension rational coefficients
Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
The exchange lives in the raw rationalization of the ambient complete category.
Constructible landing is represented through the fully faithful integral inclusion
and the specified lattice presentation. It makes no integral constructibility claim
about an arbitrary representative merely rationally isomorphic to a constructible one.

## Main statements

- `sbcRationalExchange`: the localized canonical integral mate.
- `sbcTransportedExchange`: transport along a specified presentation.
- `eCoefficientSmoothBaseChange`: invertibility, independence and constructible landing.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The scalar localization of the left integral composite, on all complete complexes.
Equivalently this is successive rational direct image and rational completed pullback:
both send a tensor r tensor a to r tensor P_f(D_g(a)).
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalLeft : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPush l E g ⋙ sbcPull l E f)

/-- The scalar localization of the right integral composite, without constructibility
assumptions on its outputs. Source: blueprint order 1445
(blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalRight : PbcRationalComplete l E T ⥤ PbcRationalComplete l E X :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcPull l E e ⋙ sbcPush l E h)

/-- Rational exchange is exactly scalar localization of the specified integral mate.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcRationalExchange : sbcRationalLeft l E (f := f) (g := g) ⟶
    sbcRationalRight l E (e := e) (h := h) :=
  ScalarLocalization.betweenNat (PbcIntegralRing l E)
    (pbcUniformizer l E) (sbcExchange l E sq)

/-- Localize an ambient integral complete complex by the same raw construction.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
abbrev sbcCompleteRationalize (W : Scheme.{u}) :=
  ScalarLocalization.localization (PbcIntegralRing l E)
    (PbcComplete l E W) (pbcUniformizer l E)

/-- Transport of the lattice exchange along the specified rational presentation.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def sbcTransportedExchange [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    (sbcRationalLeft l E (f := f) (g := g)).obj ((pbcRationalInclusion l E T).obj K) ⟶
      (sbcRationalRight l E (e := e) (h := h)).obj ((pbcRationalInclusion l E T).obj K) :=
  (sbcRationalLeft l E (f := f) (g := g)).map
      ((pbcRationalInclusion l E T).map L.rationalization.inv) ≫
    (sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj ((pbcConstructibleInclusion l E T).obj L.integral)) ≫
    (sbcRationalRight l E (e := e) (h := h)).map
      ((pbcRationalInclusion l E T).map L.rationalization.hom)

/-- Constructible landing means a constructible rational isomorphism representing the
ambient exchange, with the endpoints identified using this lattice presentation.
The integral endpoint identifications precede rationalization, so an arbitrary rational
representative is never inferred to have a constructible integral model.
Source: blueprint order 1445 (blueprint: sbc-thm-e-coefficient-smooth-base-change). -/
def SbcConstructibleExchangeRepresentation [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) : Prop :=
  ∃ (J J' : PbcIntegralConstructible l E X)
    (a : (pbcConstructibleInclusion l E X).obj J ≅
      (sbcPull l E f).obj ((sbcPush l E g).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (b : (pbcConstructibleInclusion l E X).obj J' ≅
      (sbcPush l E h).obj ((sbcPull l E e).obj
        ((pbcConstructibleInclusion l E T).obj L.integral)))
    (β : (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J ≅
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj J'),
    (pbcRationalInclusion l E X).map β.hom ≫
        ((sbcCompleteRationalize l E X).mapIso b ≪≫
          (sbcRationalRight l E (e := e) (h := h)).mapIso
            ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom =
      ((sbcCompleteRationalize l E X).mapIso a ≪≫
        (sbcRationalLeft l E (f := f) (g := g)).mapIso
          ((pbcRationalInclusion l E T).mapIso L.rationalization)).hom ≫
        (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)

omit [Fact l.Prime] in
/-- Pulling an invertible global integer back to every stalk preserves invertibility.
Source: blueprint order 1445, invertibility on every corner in proof step 1
(blueprint: sbc-thm-e-coefficient-smooth-base-change).
Proof: map the global section through q.appTop and the global-to-stalk germ. Ring maps
preserve units and natural-number casts. This also handles an empty source scheme. -/
theorem sbcPrimeUnitOnSource {U V : Scheme.{u}} (q : U ⟶ V)
    (_hl : IsUnit (l : Γ(V, ⊤))) : ∀ t : U, IsUnit (l : U.presheaf.stalk t) := by
  intro t
  have hv : IsUnit (V.presheaf.Γgerm (q t) (l : Γ(V, ⊤))) :=
    (V.presheaf.Γgerm (q t)).hom.isUnit_map _hl
  have hu := (q.stalkMap t).hom.isUnit_map hv
  simpa only [Scheme.Hom.germ_stalkMap_apply, map_natCast] using hu

private theorem sbcQuotientCard (n : ℕ) : ∃ k : ℕ,
    Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) = l ^ k := by
  classical
  let R := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  let : Fintype R := Fintype.ofFinite R
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos.ne') ?_⟩
  intro q hq hdiv
  by_contra hne
  have hcop : Nat.Coprime q l := (hq.coprime_iff_not_dvd).2
    (fun hd ↦ hne ((Nat.dvd_prime (Fact.out : l.Prime)).1 hd |>.resolve_left hq.ne_one))
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hunit : IsUnit (q : Padic.coefficientExtensionIntegers l E) := by
    apply (hdvr.2.2.1 _).2
    have hext := spectralNorm_extends (K := ℚ_[l]) (L := E) (q : ℚ_[l])
    change Padic.coefficientExtensionAbsoluteValue l E (q : E) = 1
    rw [show (q : E) = algebraMap ℚ_[l] E (q : ℚ_[l]) by simp]
    change spectralNorm ℚ_[l] E (algebraMap ℚ_[l] E (q : ℚ_[l])) = 1
    rw [hext]
    exact Padic.norm_natCast_eq_one_iff.mpr hcop.symm
  have hu : IsUnit (q : PbcIntegralRing l E) := by
    exact_mod_cast (ULift.ringEquiv.symm.toRingHom.isUnit_map hunit)
  have hv : IsUnit (q : R) := by
    simpa only [map_natCast] using
      (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1))).isUnit_map hu
  let : Fact q.Prime := ⟨hq⟩
  exact not_isUnit_prime_of_dvd_card (by simpa only [Nat.card_eq_fintype_card] using hdiv) hv

private theorem sbcTransportedExchange_eq [IsNoetherian T]
    (hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hlT : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) {K : PbcRationalConstructible l E T}
    (L : IntegralLattice l E T hT hlT K) :
    sbcTransportedExchange l E sq hT hlT L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K) := by
  unfold sbcTransportedExchange
  rw [← (sbcRationalExchange l E sq).naturality]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    L.rationalization.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem sbcCoefficientConstructible_iso
    (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {F G : pbcModules W (adicLisseConstantRing W A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleCoefficientModuleSheaf W A F) :
    IsConstructibleProEtaleCoefficientModuleSheaf W A G := by
  obtain ⟨S, hn, hS, hF⟩ := hF
  refine ⟨S, hn, hS, fun i ↦ ?_⟩
  obtain ⟨K, hK, hF⟩ := hF i
  refine ⟨K, hK, fun V g hg ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hF V g hg
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso
    ((proEtaleModuleInverseImage (S.immersion i)
      (adicLisseConstantRing W A)).mapIso e.symm) ≪≫ eM⟩⟩

private theorem sbcWindowTransport (W : Scheme.{u}) (n : ℕ) (a b : ℤ)
    (M : ProEtale.PbcWitnessAmbient W (pbcIntegralDatum l E) n)
    (N : DerivedCategory (pbcModules W
      ((pbcAdicRings W (pbcIntegralDatum l E)).obj (op n))))
    (e : (pbcDerivedFunctionRealization W (pbcIntegralDatum l E) n).obj M ≅ N)
    (hM : sbcIntrinsicConstructibleIn W
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) a b M) (i : ℤ) :
    IsConstructibleProEtaleCoefficientModuleSheaf W
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
        (sbcAdicFiniteCohomology l E W n N i) ∧
      ((i < a ∨ b < i) → IsZero (sbcAdicFiniteCohomology l E W n N i)) := by
  let R := pbcFunctionRealization W (pbcIntegralDatum l E) n
  let U := pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom
  let c := U.mapIso ((R.mapDerivedCategoryHomologyFunctorIso i).app M ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e)
  refine ⟨sbcCoefficientConstructible_iso W _ c
    (sbcFiniteRealization_constructible l E W n _ (hM i).1), ?_⟩
  intro hi
  exact (U.map_isZero (R.map_isZero ((hM i).2 hi))).of_iso c.symm

/-- Smooth base change for E coefficients, including lattice independence and
constructible landing with the specified endpoint identifications.
The integral and rational constructible categories and both lattice predicates are
the landed Q06 declarations. Their full inclusion into the complete category uses the
same completed coefficient ring and published intrinsic predicate. Completed pullback
is the strict tower construction with its maps. No additional universe equality is required.
Source: blueprint order 1445, sec-smooth-base-change/sk-rem-rest
(blueprint: sbc-thm-e-coefficient-smooth-base-change).

Proof: the ring of integers is a Noetherian DVR with finite residue field; its positive
quotients are finite and have two-term finite-free resolutions. Multiplication by a
positive uniformizer power is injective because the valuation ring is a domain, so
these resolutions give perfect quotients. The residue field has characteristic l:
l has absolute value less than one and lies in the maximal ideal. If its cardinality
is l^d, cancellation identifies each successive uniformizer-ideal quotient with that
residue field, giving cardinality l^(d(n+1)) at level n. Its order is invertible on S
by the hypothesis on l, and hence on every corner. This verifies the coefficient
hypotheses of sbc-thm-adic-smooth-base-change, using
lem-weil-l-adic-extension-integers-dvr and lem-weil-valued-dvr-finite-quotients.
The lattice's complete-category membership supplies the compatible etale origins,
and its finite-level admissibility supplies bounded constructible origins. Apply the
adic theorem to this lattice. Its finite-level smooth base change applies
to every bounded constructible étale origin of the lattice reduction. The completed
pullback-reduction and direct-image/derived-limit comparisons identify the completed
integral mate with the derived inverse limit of these finite exchange maps, hence
make it invertible on the lattice. The operations are additive and A-linear, so raw
scalar localization gives the displayed natural transformation and preserves its
inverse. Naturality, followed by cancellation of the two inverse presentation maps,
gives transported exchange = exchange at K; applying the same equality to every
other admissible presentation proves independence.

For square-constructible admissibility, the four finite systems share one window.
Their canonical quotient-linear comparisons are the actual reductions of the four
completed integral outputs. Normalized constructible local effectivity supplies the
uniform stratified local models and bounded étale origins for the two X endpoints.
Lift each quotient normalization to its étale origin using full faithfulness on D+;
the normalization cocycle and faithfulness give the witness cocycle. Thus both integral
endpoints are in the published bounded constructible complete subcategory. Its full
inclusion remains fully faithful after tensoring Hom groups. The localized exchange
and its inverse are consequently an isomorphism of the rational constructible
endpoints. Composing their endpoint identifications with the given presentation gives
the equality required by SbcConstructibleExchangeRepresentation. -/
theorem eCoefficientSmoothBaseChange
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (K : PbcRationalConstructible l E T)
    (L : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K)
    (_hL : L.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl)) :
    IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L =
      (sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) ∧
    (∀ L' : IntegralLattice l E T _hT (sbcPrimeUnitOnSource l g _hl) K,
      L'.IsFiniteLevelEtaleAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) →
      sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L' =
        sbcTransportedExchange l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) ∧
    (L.IsSquareConstructiblyAdmissible l E T _hT (sbcPrimeUnitOnSource l g _hl) sq →
      SbcConstructibleExchangeRepresentation l E sq _hT (sbcPrimeUnitOnSource l g _hl) L) := by
  classical
  have hglobal {U V : Scheme.{u}} (q : U ⟶ V)
      (hunit : IsUnit (l : Γ(V, ⊤))) : IsUnit (l : Γ(U, ⊤)) := by
    simpa only [map_natCast] using q.appTop.hom.isUnit_map hunit
  have horder (n : ℕ) := sbcQuotientCard l E n
  have horders : ∀ n : ℕ,
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(S, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(X, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(T, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(Y, ⊤)) := by
    intro n
    obtain ⟨k, hk⟩ := horder n
    rw [hk]
    simp only [Nat.cast_pow]
    exact ⟨_hl.pow k, (hglobal f _hl).pow k, (hglobal g _hl).pow k,
      (hglobal e (hglobal g _hl)).pow k⟩
  have horigin : ∀ n : ℕ,
      ∃ M : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
        Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
              T).mapDerivedCategory.obj M.obj) ≅
          (sbcReduction l E T n).obj L.integral.obj) := by
    intro n
    obtain ⟨M, ⟨a⟩⟩ := _hL n
    exact ⟨M, ⟨(pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).mapIso a ≪≫
      (pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).asEquivalence.counitIso.app _⟩⟩
  have hadic := adicSmoothBaseChange l E sq _hT _hl horders L.integral horigin
  have hint := hadic.1
  have hrat : IsIso ((sbcRationalExchange l E sq).app
      ((sbcCompleteRationalize l E T).obj
        ((pbcConstructibleInclusion l E T).obj L.integral))) := by
    change IsIso ((sbcCompleteRationalize l E X).map
      (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)))
    infer_instance
  have hK : IsIso ((sbcRationalExchange l E sq).app ((pbcRationalInclusion l E T).obj K)) := by
    rw [← sbcTransportedExchange_eq l E sq _hT (sbcPrimeUnitOnSource l g _hl) L]
    unfold sbcTransportedExchange
    infer_instance
  refine ⟨hK, sbcTransportedExchange_eq l E sq _hT _ L, ?_, ?_⟩
  · intro L' _
    exact (sbcTransportedExchange_eq l E sq _hT _ L').trans
      (sbcTransportedExchange_eq l E sq _hT _ L).symm
  · intro hsq
    have hwindow : ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ,
        (IsConstructibleProEtaleCoefficientModuleSheaf S
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj L.integral.obj))) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf Y
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj L.integral.obj))) i))) := by
      obtain ⟨a, b, hab, hw⟩ := hsq.2
      refine ⟨a, b, hab, fun n i ↦ ?_⟩
      let R (W : Scheme.{u}) := pbcDerivedFunctionRealization W (pbcIntegralDatum l E) n
      let M := L.reduction l E T _hT (sbcPrimeUnitOnSource l g _hl) n
      let c : (R T).obj M ≅ (sbcReduction l E T n).obj L.integral.obj :=
        (R T).asEquivalence.counitIso.app _
      obtain ⟨cg⟩ := (sbcFiniteWitnessRealization l E g n).1
      obtain ⟨cf⟩ := (sbcFiniteWitnessRealization l E f n).2
      obtain ⟨ce⟩ := (sbcFiniteWitnessRealization l E e n).2
      obtain ⟨ch⟩ := (sbcFiniteWitnessRealization l E h n).1
      let eg := cg.app M ≪≫ (sbcFinitePush l E g n).mapIso c
      let ef := cf.app _ ≪≫ (sbcFinitePull l E f n).mapIso eg
      let ee := ce.app M ≪≫ (sbcFinitePull l E e n).mapIso c
      let eh := ch.app _ ≪≫ (sbcFinitePush l E h n).mapIso ee
      exact ⟨sbcWindowTransport l E S n a b _ _ eg (hw n).1 i,
        sbcWindowTransport l E X n a b _ _ ef (hw n).2.1 i,
        sbcWindowTransport l E Y n a b _ _ ee (hw n).2.2.1 i,
        sbcWindowTransport l E X n a b _ _ eh (hw n).2.2.2 i⟩
    obtain ⟨hB, hD, hiso⟩ := hadic.2 _hX hwindow
    let J : PbcIntegralConstructible l E X := ⟨_, hB⟩
    let J' : PbcIntegralConstructible l E X := ⟨_, hD⟩
    let a : (pbcConstructibleInclusion l E X).obj J ≅
        (sbcPull l E f).obj ((sbcPush l E g).obj
          ((pbcConstructibleInclusion l E T).obj L.integral)) := Iso.refl _
    let b : (pbcConstructibleInclusion l E X).obj J' ≅
        (sbcPush l E h).obj ((sbcPull l E e).obj
          ((pbcConstructibleInclusion l E T).obj L.integral)) := Iso.refl _
    let c : J ≅ J' := asIso (ObjectProperty.homMk
      (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj L.integral)).hom)
    let β := (pbcRationalization X (pbcIntegralDatum l E)
      (pbcUniformizer l E)).mapIso c
    refine ⟨J, J', a, b, β, ?_⟩
    have hc : (pbcRationalInclusion l E X).map β.hom =
        (sbcRationalExchange l E sq).app
          ((sbcCompleteRationalize l E T).obj
            ((pbcConstructibleInclusion l E T).obj L.integral)) := by
      change ((pbcConstructibleInclusion l E X).mapLinearMap
        (PbcIntegralRing l E)).baseChange (Localization.Away (pbcUniformizer l E))
          ((pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).map c.hom) = _
      simp only [pbcRationalization, ScalarLocalization.localization,
        LinearMap.baseChange_tmul]
      rfl
    simp only [a, b, Functor.mapIso_refl, Iso.refl_trans,
      Functor.mapIso_hom, hc]
    exact ((sbcRationalExchange l E sq).naturality
      ((pbcRationalInclusion l E T).map L.rationalization.hom)).symm

end WeilConjectures
