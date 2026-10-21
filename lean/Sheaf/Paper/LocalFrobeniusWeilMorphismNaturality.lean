/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.SixFunctors.FrobeniusPointTransportNatural

/-! # Naturality of iterated local Frobenius for morphisms of Weil pairs

Source: Weil blueprint, sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed local alternating-trace formula, with its agent-extracted naturality argument
(blueprint: lem-fd-local-frobenius-weil-morphism-naturality).

The auxiliary abbreviations specialize the published pullback functor with its inherited
prime-invertibility instances. The return comparison and transport extend the published
local construction to every constructible object, without requiring a Weil structure.
All positive-power indices below denote exponent one greater than the index.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The specified pullback S_(r+1) on the point, with inherited invertibility.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
abbrev localPointPowerPullback (r : ℕ) :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (frobeniusPointIso D).hom r)
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

private theorem pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K =
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K

private theorem pullback_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K J : sfIntegralConstructibleCategory l E Y) (a : K ⟶ J)
    (b : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((rationalDerivedPullback l E f).map
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] a))
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E f).map a) :=
  (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K J a b

private theorem composition_heq {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    HEq (localPullbackComposition l E h k K).hom
      ((sfRationalConstructibleLocalization l E X).map
        (((integralPullbackComposition l E).choose h k).hom.app K.obj)) := by
  simp only [localPullbackComposition, localPullbackObjectIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_map, ← Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

private theorem map_heq {C T : Type*} [Category C] [Category T]
    (Q : C ⥤ T) {U V U' V' : C} (hu : U = U') (hv : V = V')
    {f : U ⟶ V} {f' : U' ⟶ V'} (hf : HEq f f') : HEq (Q.map f) (Q.map f') := by
  subst U'
  subst V'
  exact heq_of_eq (congrArg Q.map (eq_of_heq hf))

private theorem composition_natural {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K J : sfRationalConstructibleCategory l E Z) (v : K ⟶ J) :
    (localPullbackComposition l E h k K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E k).map v) =
      (rationalDerivedPullback l E (h ≫ k)).map v ≫
        (localPullbackComposition l E h k J).hom := by
  let _ : (rationalDerivedPullback l E h).Additive :=
    (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  let _ : (rationalDerivedPullback l E k).Additive :=
    (rationalDerivedPullback_existsUnique l E k).exists.choose_spec.1
  let _ : (rationalDerivedPullback l E (h ≫ k)).Additive :=
    (rationalDerivedPullback_existsUnique l E (h ≫ k)).exists.choose_spec.1
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    change (localPullbackComposition l E h k K).hom ≫
        (rationalDerivedPullback l E h).map
          ((rationalDerivedPullback l E k).map (a + b : K ⟶ J)) =
      (rationalDerivedPullback l E (h ≫ k)).map (a + b : K ⟶ J) ≫
        (localPullbackComposition l E h k J).hom
    rw [(rationalDerivedPullback l E k).map_add,
      (rationalDerivedPullback l E h).map_add,
      (rationalDerivedPullback l E (h ≫ k)).map_add,
      Preadditive.comp_add, Preadditive.add_comp, ha, hb]
  | tmul b a =>
    have hh : HEq ((rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E k).map (b ⊗ₜ[_] a)))
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E h).map
            ((constructibleIntegralPullback l E k).map a)) :=
      (map_heq _ (pullback_obj l E k K) (pullback_obj l E k J)
        (pullback_tmul l E k K.obj J.obj a b)).trans
          (pullback_tmul l E h _ _ ((constructibleIntegralPullback l E k).map a) b)
    apply eq_of_heq
    apply (heq_comp (pullback_obj l E (h ≫ k) K)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (composition_heq l E h k K) hh).trans
    apply HEq.trans _ (heq_comp (pullback_obj l E (h ≫ k) K)
      (pullback_obj l E (h ≫ k) J)
      (by rw [pullback_obj, pullback_obj]; rfl)
      (pullback_tmul l E (h ≫ k) K.obj J.obj a b)
      (composition_heq l E h k J)).symm
    change HEq (ScalarLocalization.composition _ _ _ _ _ _
      (b ⊗ₜ[_] _) (1 ⊗ₜ[_] _))
      (ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ[_] _) (b ⊗ₜ[_] _))
    simp only [ScalarLocalization.composition_tmul, mul_one, one_mul]
    exact heq_of_eq (congrArg (fun f ↦ b ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)
      (((integralPullbackComposition l E).choose h k).hom.naturality a).symm)

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The specified pullback G_(r+1) on the geometric fibre, with inherited invertibility.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
abbrev localGeometricPowerPullback (r : ℕ) :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (D.geometricFrobenius X₀).hom r)
    (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)

/-- The specified pullback P at an arbitrary geometric point, on the full constructible domain.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
abbrev localConstructibleStalkFunctor
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ x
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)

/-- The specified return comparison rho, on every constructible object M.
This is the same composite as localReturnComparison, with no Weil structure required.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
def localConstructibleReturnComparison
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (localPointPowerPullback l E D hl r).obj
        ((localConstructibleStalkFunctor l E D hl X₀ x).obj M) ≅
      (localConstructibleStalkFunctor l E D hl X₀ x).obj
        ((localGeometricPowerPullback l E D hl X₀ r).obj M) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl X₀
  (localPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom r)
    x M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M) h.symm) ≪≫
    localPullbackComposition l E x
      (localPositivePower (D.geometricFrobenius X₀).hom r) M

/-- The specified R(M) = Q(rho_M) I^[r+1]_(P(M)), on every constructible object.
Source: blueprint trace formula (blueprint: lem-fd-local-frobenius-weil-morphism-naturality). -/
def localConstructibleReturnTransport
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  localPointTransportIterate l E D hl
      ((localConstructibleStalkFunctor l E D hl X₀ x).obj M) r ≫
    (pointRationalFibre D l hl E).map
      (localConstructibleReturnComparison l E D hl X₀ x r h M).hom

private theorem point_natural
    (N J : sfRationalConstructibleCategory l E (Spec (.of D.k))) (w : N ⟶ J) :
    localPointTransport l E D hl N ≫
        (pointRationalFibre D l hl E).map ((localPointPowerPullback l E D hl 0).map w) =
      (pointRationalFibre D l hl E).map w ≫ localPointTransport l E D hl J := by
  let := frobeniusPointPrimeInvertible D l hl
  have hw := (frobeniusPointTransport_natural D l hl E).2.2.2.2.2.2.2.2.2.2.1 N J w
  dsimp only [localPointTransport]
  have he (M : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
      (localPullbackObjectIso l E (frobeniusPointIso D).hom M).inv =
        eqToHom (frobeniusPointRationalPullbackEq D l hl E M).symm := by
    rfl
  simp only [he]
  rw [Category.assoc, ← Functor.map_comp]
  rw [← Category.assoc, hw, Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Functor.map_comp]
  rfl

private theorem comparison_inv_natural {C T : Type*} [Category C] [Category T]
    {F G : C ⥤ T} (e : ∀ K, F.obj K ≅ G.obj K)
    (he : ∀ {K J} (v : K ⟶ J), (e K).hom ≫ G.map v = F.map v ≫ (e J).hom)
    {K J : C} (v : K ⟶ J) :
    (e K).inv ≫ F.map v = G.map v ≫ (e J).inv := by
  apply (cancel_epi (e K).hom).1
  simpa only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using congrArg (fun f ↦ f ≫ (e J).inv) (he v).symm

private theorem point_iterate_natural (r : ℕ)
    (N J : sfRationalConstructibleCategory l E (Spec (.of D.k))) (w : N ⟶ J) :
    localPointTransportIterate l E D hl N r ≫
        (pointRationalFibre D l hl E).map ((localPointPowerPullback l E D hl r).map w) =
      (pointRationalFibre D l hl E).map w ≫ localPointTransportIterate l E D hl J r := by
  let := frobeniusPointPrimeInvertible D l hl
  induction r generalizing N J with
  | zero => exact point_natural l E D hl N J w
  | succ r ih =>
    have hc := comparison_inv_natural
      (F := rationalDerivedPullback l E
        (localPositivePower (frobeniusPointIso D).hom r ≫ (frobeniusPointIso D).hom))
      (G := rationalDerivedPullback l E (frobeniusPointIso D).hom ⋙
        rationalDerivedPullback l E (localPositivePower (frobeniusPointIso D).hom r))
      (localPullbackComposition l E _ _) (fun v ↦ composition_natural l E _ _ _ _ v) w
    dsimp only [localPointTransportIterate, localPointPowerPullback, localPositivePower]
    simp only [Category.assoc]
    rw [← Functor.map_comp, hc, Functor.map_comp]
    have hi := ih _ _ ((rationalDerivedPullback l E (frobeniusPointIso D).hom).map w)
    dsimp only [localPointPowerPullback] at hi
    simp only [Functor.comp_map]
    rw [reassoc_of% hi]
    have hbase := point_natural l E D hl N J w
    dsimp only [localPointPowerPullback, localPositivePower] at hbase
    rw [reassoc_of% hbase]

private theorem weil_iterate_natural (r : ℕ)
    (A B : sfWeilComplex D l hl X₀ E) (v : A ⟶ B) :
    (localWeilIterate l E D hl X₀ A r).hom ≫ v.hom.f =
      (localGeometricPowerPullback l E D hl X₀ r).map v.hom.f ≫
        (localWeilIterate l E D hl X₀ B r).hom := by
  let := sfWeilPrimeInvertible D l hl X₀
  induction r with
  | zero => exact v.hom.h.symm
  | succ r ih =>
    have hv : A.str.hom ≫ v.hom.f =
        (rationalDerivedPullback l E (D.geometricFrobenius X₀).hom).map v.hom.f ≫
          B.str.hom := v.hom.h.symm
    have hc := composition_natural l E
      (localPositivePower (D.geometricFrobenius X₀).hom r)
      (D.geometricFrobenius X₀).hom A.carrier B.carrier v.hom.f
    dsimp only [localWeilIterate, Iso.trans_hom, Functor.mapIso_hom,
      localGeometricPowerPullback, localPositivePower]
    have hf := congrArg
      (fun f ↦ (localGeometricPowerPullback l E D hl X₀ r).map f) hv
    simp only [Functor.map_comp] at hf
    simp only [Category.assoc]
    rw [ih, reassoc_of% hf, reassoc_of% hc]

attribute [local irreducible] rationalDerivedPullback

private theorem equality_natural {C T : Type*} [Category C] [Category T]
    {I : Type*} (F : I → C ⥤ T) {i j : I} (e : i = j) {M J : C} (v : M ⟶ J) :
    eqToHom (congrArg (fun i ↦ (F i).obj M) e) ≫ (F j).map v =
      (F i).map v ≫ eqToHom (congrArg (fun i ↦ (F i).obj J) e) := by
  cases e
  simp

private theorem return_natural
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (M J : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (v : M ⟶ J) :
    (localConstructibleReturnComparison l E D hl X₀ x r h M).hom ≫
        (localConstructibleStalkFunctor l E D hl X₀ x).map
          ((localGeometricPowerPullback l E D hl X₀ r).map v) =
      (localPointPowerPullback l E D hl r).map
        ((localConstructibleStalkFunctor l E D hl X₀ x).map v) ≫
          (localConstructibleReturnComparison l E D hl X₀ x r h J).hom := by
  let := frobeniusPointPrimeInvertible D l hl
  let := sfWeilPrimeInvertible D l hl X₀
  have ha := comparison_inv_natural
    (F := rationalDerivedPullback l E
      (localPositivePower (frobeniusPointIso D).hom r ≫ x))
    (G := rationalDerivedPullback l E x ⋙
      rationalDerivedPullback l E (localPositivePower (frobeniusPointIso D).hom r))
    (localPullbackComposition l E _ x) (fun v ↦ composition_natural l E _ x _ _ v) v
  have hb := composition_natural l E x
    (localPositivePower (D.geometricFrobenius X₀).hom r) M J v
  have he :
      (eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M) h.symm)).hom ≫
          (rationalDerivedPullback l E
            (x ≫ localPositivePower (D.geometricFrobenius X₀).hom r)).map v =
        (rationalDerivedPullback l E
          (localPositivePower (frobeniusPointIso D).hom r ≫ x)).map v ≫
          (eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj J) h.symm)).hom := by
    exact @equality_natural
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left)
      (sfRationalConstructibleCategory l E (Spec (.of D.k))) _ _
      (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (fun f ↦ rationalDerivedPullback l E f) _ _ h.symm M J v
  dsimp only [localConstructibleReturnComparison, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, hb, reassoc_of% he]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫
      (eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj J) h.symm)).hom ≫
      (localPullbackComposition l E x
        (localPositivePower (D.geometricFrobenius X₀).hom r) J).hom) ha

private theorem return_transport_natural
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (M J : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (v : M ⟶ J) :
    localConstructibleReturnTransport l E D hl X₀ x r h M ≫
        ((localConstructibleStalkFunctor l E D hl X₀ x) ⋙
          pointRationalFibre D l hl E).map
            ((localGeometricPowerPullback l E D hl X₀ r).map v) =
      ((localConstructibleStalkFunctor l E D hl X₀ x) ⋙
        pointRationalFibre D l hl E).map v ≫
          localConstructibleReturnTransport l E D hl X₀ x r h J := by
  dsimp only [localConstructibleReturnTransport, Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, return_natural l E D hl X₀ x r h M J v,
    Functor.map_comp, ← Category.assoc, point_iterate_natural]
  simp only [Category.assoc]

private theorem operator_natural
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius X₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x)
    (A B : sfWeilComplex D l hl X₀ E) (v : A ⟶ B) :
    localFrobeniusOperator l E D hl X₀ A x r h ≫
        ((localConstructibleStalkFunctor l E D hl X₀ x) ⋙
          pointRationalFibre D l hl E).map v.hom.f =
      ((localConstructibleStalkFunctor l E D hl X₀ x) ⋙
        pointRationalFibre D l hl E).map v.hom.f ≫
          localFrobeniusOperator l E D hl X₀ B x r h := by
  let P := localConstructibleStalkFunctor l E D hl X₀ x
  let Q := pointRationalFibre D l hl E
  let R := localConstructibleReturnTransport l E D hl X₀ x r h
  have hdef (K : sfWeilComplex D l hl X₀ E) :
      localFrobeniusOperator l E D hl X₀ K x r h =
        R K.carrier ≫ (P ⋙ Q).map (localWeilIterate l E D hl X₀ K r).hom := by
    simp only [localFrobeniusOperator, localDerivedStalk, localReturnComparison, R, P, Q,
      localConstructibleReturnTransport, localConstructibleReturnComparison,
      localConstructibleStalkFunctor, Functor.comp_map, Category.assoc]
  rw [hdef, hdef, Category.assoc, ← Functor.map_comp,
    weil_iterate_natural l E D hl X₀, Functor.map_comp, ← Category.assoc,
    return_transport_natural l E D hl X₀ x r h A.carrier B.carrier v.hom.f, Category.assoc]

attribute [local irreducible] pointRationalFibre localPointTransportIterate localWeilIterate
  localConstructibleReturnComparison localConstructibleReturnTransport localExtensionFrobenius

/-- Naturality on the full raw rationalized constructible domain, including arbitrary
(noninvertible) morphisms of Weil pairs. Each r : ℕ denotes the positive exponent r+1.
Source: blueprint sec-fourier-transform/sk-def-trace/def-fd-trace-function.md,
displayed alternating-trace formula, agent-extracted comparison lemma
(blueprint: lem-fd-local-frobenius-weil-morphism-naturality).

Proof:
1. The rational clause of lem-weil-frobenius-point-transport-natural gives the single-step
   naturality square for every rational constructible arrow w, including all its pullbacks.
   The functor Q is clause 3 of def-weil-finite-coefficient-point.
2. Induct on the positive exponent to compose these squares. Conjugate the iterated
   one-step pullback by the specified composition comparison. Its rational naturality and
   iteration compatibility are lem-trf-integral-pullback-comparison-realization. This gives
   Q(S_r(w)) I_N^[r] = I_N'^[r] Q(w).
3. The return equality identifies the sources of the two specified composition comparisons
   a : H ≅ S_n P and b : H ≅ P G_n. The return is b a⁻¹. Their naturality squares give
   P(G_n(v)) rho_M = rho_M' S_n(P(v)). This uses the actual semilinear return equality,
   not a fixed geometric-point equation.
4. Apply Q to step 3, multiply by I^[n], and use step 2 for P(v). Functoriality yields
   D(G_n(v)) R(M) = R(M') D(v).
5. The Weil-pair morphism equation is the exponent-one base. In the recursion
   alpha^[r+1] = alpha^[r] G_r(alpha) k_r, insert the induction hypothesis, use the
   one-step equation under G_r, and then naturality of the specified k_r. This proves
   v alpha^[r] = beta^[r] G_r(v) for every positive r.
6. Apply D to step 5 at n and multiply by R(A). Step 4 turns the result into the local
   operator intertwining equation. No inverse of v, Weil-stable integral lattice or
   finite-reduction Tor-amplitude condition is used. -/
theorem localFrobeniusWeilMorphismNaturality
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (F : Padic.FiniteCoefficientFields c.l c.Qbar)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn) :
    (∀ (r : ℕ) (N N' : sfRationalConstructibleCategory c.l F.val (Spec (.of D.k)))
      (w : N ⟶ N'),
      (localPointTransportIterate c.l F.val D c.different N r) ≫ (pointRationalFibre D c.l
          c.different F.val).map ((localPointPowerPullback c.l F.val D c.different r).map w) =
        (pointRationalFibre D c.l c.different F.val).map w ≫ (localPointTransportIterate c.l F.val D
          c.different N' r)) ∧
    (∀ (M M' : sfRationalConstructibleCategory c.l F.val (D.geometricFiber X₀).left)
      (v : M ⟶ M'),
      (localConstructibleReturnComparison c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x) (n - 1) (localExtensionPoint_return D X₀ n hn x) M).hom ≫
          (localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)).map ((localGeometricPowerPullback c.l F.val D c.different X₀ (n - 1)).map v) =
        (localPointPowerPullback c.l F.val D c.different (n - 1)).map
          ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)).map v) ≫ (localConstructibleReturnComparison c.l F.val D c.different X₀
          (localExtensionPoint D X₀ n hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x)
          M').hom) ∧
    (∀ (M M' : sfRationalConstructibleCategory c.l F.val (D.geometricFiber X₀).left)
      (v : M ⟶ M'),
      (localConstructibleReturnTransport c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x) (n - 1) (localExtensionPoint_return D X₀ n hn x) M) ≫ ((localConstructibleStalkFunctor
          c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn x)) ⋙ (pointRationalFibre D c.l
          c.different F.val)).map
          ((localGeometricPowerPullback c.l F.val D c.different X₀ (n - 1)).map v) =
        ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)) ⋙ (pointRationalFibre D c.l c.different F.val)).map v ≫
          (localConstructibleReturnTransport c.l F.val D c.different X₀ (localExtensionPoint D X₀ n
          hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x) M')) ∧
    (∀ (r : ℕ) (A B : sfWeilComplex D c.l c.different X₀ F.val) (v : A ⟶ B),
      (localWeilIterate c.l F.val D c.different X₀ A r).hom ≫ v.hom.f =
        (localGeometricPowerPullback c.l F.val D c.different X₀ r).map v.hom.f ≫ (localWeilIterate
          c.l F.val D c.different X₀ B r).hom) ∧
    (∀ (A B : sfWeilComplex D c.l c.different X₀ F.val) (v : A ⟶ B),
      (localExtensionFrobenius c.l F.val D c.different X₀ A n hn x) ≫
          ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)) ⋙ (pointRationalFibre D c.l c.different F.val)).map v.hom.f =
        ((localConstructibleStalkFunctor c.l F.val D c.different X₀ (localExtensionPoint D X₀ n hn
          x)) ⋙ (pointRationalFibre D c.l c.different F.val)).map v.hom.f ≫ (localExtensionFrobenius
          c.l F.val D c.different X₀ B n hn x)) := by
  refine ⟨point_iterate_natural c.l F.val D c.different,
    return_natural c.l F.val D c.different X₀
      (localExtensionPoint D X₀ n hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x),
    return_transport_natural c.l F.val D c.different X₀
      (localExtensionPoint D X₀ n hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x),
    weil_iterate_natural c.l F.val D c.different X₀,
    ?_⟩
  intro A B v
  simpa only [localExtensionFrobenius] using
    operator_natural c.l F.val D c.different X₀
      (localExtensionPoint D X₀ n hn x) (n - 1) (localExtensionPoint_return D X₀ n hn x) A B v

end WeilConjectures
