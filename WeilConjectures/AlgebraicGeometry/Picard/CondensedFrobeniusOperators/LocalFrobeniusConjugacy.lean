/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.ZetaSeries
public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPointsCount
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.LocalFrobeniusConjugacyOrbit
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.LocalFrobeniusConjugacyTransport
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.PointCount

/-!
# Local Frobenius conjugacy along the normalized orbit

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-c-proper-global/
lem-trf-local-frobenius-conjugacy.md, clauses 1--3, with the DAG's explicit source
reparametrization (blueprint: lem-trf-local-frobenius-conjugacy).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators

open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

variable (F : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of F.k₀)))
  [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The normalized orbit `Spec(sigma^i);z;g^i`. The inverse of the base map of geometric
Frobenius is precisely Spec(sigma). Source: the DAG's explicit semilinear convention,
clause 1 (blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusOrbit
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) (i : ℕ) :
    Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left :=
  ((condensedFrobeniusGeometry F Y₀).b.pow i).inv ≫
    (z ≫ ((condensedFrobeniusGeometry F Y₀).h.pow i).hom)

/-- A lift is a k-morphism whose projection to X₀ has image x.
Source: the opening paragraph of the DAG statement
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def IsLocalFrobeniusLift (x : Y₀.left)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) : Prop :=
  z ≫ (F.geometricFiber Y₀).hom = 𝟙 _ ∧
    (z ≫ pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k)))).base
      (IsLocalRing.closedPoint F.k) = x

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)

/-- The actual coefficient complex Fib_s(Lz* K), computed by the recorded scalar sections.
Source: clause 2 and def-weil-finite-coefficient-point
(blueprint: lem-trf-local-frobenius-conjugacy). -/
abbrev localFrobeniusFibre (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) :=
  L (finiteCoefficient ell E n) z ⋙ Γ (finiteCoefficient ell E n) (Spec (.of F.k))

/-- Canonical reparametrization of the source point. Insertion is restriction along b
on terminal sections, and the inverse compositor expresses it in L(b;v)* coordinates.
Thus represented stalk germs are sent to the same section with the reparametrized lift.
Source: the reparametrization paragraph and proof step 3 of the DAG
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusReparam
    (v : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (b : Spec (.of F.k) ⟶ Spec (.of F.k)) :
    localFrobeniusFibre F Y₀ ell E n v ≅ localFrobeniusFibre F Y₀ ell E n (b ≫ v) :=
  Functor.isoWhiskerLeft (L (finiteCoefficient ell E n) v)
      (insertion (finiteCoefficient ell E n) b) ≪≫
    (Functor.isoWhiskerRight (leftDerivedUpperStarComp (finiteCoefficient ell E n) b v)
      (Γ (finiteCoefficient ell E n) (Spec (.of F.k)))).symm

/-- The specified transport: remove Spec(sigma^i), use the inverse pullback--stalk
comparison, and apply phi^[i]. The owning iterate includes the canonical zero case.
No reduction of the iterate modulo the degree occurs.
Source: clause 2, the displayed definition of T_i
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusTransport (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) (i : ℕ) :
    (localFrobeniusFibre F Y₀ ell E n (localFrobeniusOrbit F Y₀ z i)).obj K.carrier.obj ≅
      (localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj :=
  (localFrobeniusReparam F Y₀ ell E n
      (z ≫ ((condensedFrobeniusGeometry F Y₀).h.pow i).hom)
      ((condensedFrobeniusGeometry F Y₀).b.pow i).inv).symm.app K.carrier.obj ≪≫
    (Γ (finiteCoefficient ell E n) (Spec (.of F.k))).mapIso
      ((leftDerivedUpperStarComp (finiteCoefficient ell E n) z
        ((condensedFrobeniusGeometry F Y₀).h.pow i).hom).app K.carrier.obj) ≪≫
    (localFrobeniusFibre F Y₀ ell E n z).mapIso (iteratedWeil F Y₀ ell E n hn K i)

/-- The owning local operator in the coordinates of an equal chosen geometric lift.
This changes only equality coordinates; the operator is exactly condensedLocalFrobenius.
Source: clause 3, identifying bar(y_i) with z_i
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusAtLift (hEll : ell ≠ F.p)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn) (m : ℕ) (hm : 1 ≤ m)
    (y : F.extensionPoints Y₀ m hm)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (hy : extensionPointGeometry F Y₀ m hm y = z) :
    End ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj) :=
  let e := eqToIso (congrArg
    (fun w ↦ (localFrobeniusFibre F Y₀ ell E n w).obj K.carrier.obj) hy)
  e.inv ≫ condensedLocalFrobenius F Y₀ ell hEll E n hn m hm ⟨y⟩ K ≫ e.hom

/-- Compatibility of a chosen residue-field embedding with the model base map.
Source: the closed-point construction in def-weil-local-frobenius-trace.
Proof: compose the residue-field structural map and use contravariance of Spec. -/
private theorem closedPointLift_compatible
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (i : Y₀.left.residueField y.val →+* F.k)
    (hi : i.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap F.k₀ F.k) :
    (Spec.map (CommRingCat.ofHom i) ≫ Y₀.left.fromSpecResidueField y.val) ≫ Y₀.hom =
      (𝟙 (Spec (.of F.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k)) := by
  rw [Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
    Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hi]

/-- The same concrete closed-point lift, retained privately for the counting proof.
Source: def-weil-local-frobenius-trace. This is the universal pullback lift of
Spec of the chosen residue-field embedding and the identity map of Spec k. -/
private def closedPointLift (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (i : Y₀.left.residueField y.val →+* F.k)
    (hi : i.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap F.k₀ F.k) :
    Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom i) ≫ Y₀.left.fromSpecResidueField y.val)
    (𝟙 _) (closedPointLift_compatible F Y₀ y i hi)

private theorem iso_pow_add {C : Type*} [Category C] {X : C}
    (e : X ≅ X) (i j : ℕ) : e.pow (i + j) = e.pow i ≪≫ e.pow j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, Iso.pow_succ, ih, Iso.pow_succ, Iso.trans_assoc]

private theorem localFrobeniusOrbit_zero
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) :
    localFrobeniusOrbit F Y₀ z 0 = z := by
  change 𝟙 _ ≫ (z ≫ 𝟙 _) = z
  rw [Category.id_comp, Category.comp_id]

private theorem localFrobeniusOrbit_add
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) (i j : ℕ) :
    localFrobeniusOrbit F Y₀ (localFrobeniusOrbit F Y₀ z i) j =
      localFrobeniusOrbit F Y₀ z (i + j) := by
  simp only [localFrobeniusOrbit, iso_pow_add, Iso.trans_hom, Iso.trans_inv,
    Category.assoc]

private theorem localFrobeniusOrbit_iterate
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left) (i : ℕ) :
    localFrobeniusOrbit F Y₀ z i =
      ((fun w ↦ localFrobeniusOrbit F Y₀ w 1)^[i]) z := by
  induction i with
  | zero => exact localFrobeniusOrbit_zero F Y₀ z
  | succ i ih =>
    rw [← localFrobeniusOrbit_add, ih, Function.iterate_succ_apply']

private theorem factor_field_point_native {K : Type u} [Field K] {X : Scheme.{u}}
    (z : Spec (.of K) ⟶ X) (y : X)
    (hy : z (IsLocalRing.closedPoint K) = y) :
    ∃ i : X.residueField y →+* K,
      Spec.map (CommRingCat.ofHom i) ≫ X.fromSpecResidueField y = z := by
  obtain ⟨⟨p, i⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] at hy
  subst p
  exact ⟨i.hom, rfl⟩

private theorem factor_lift_native (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left))
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (hz : IsLocalFrobeniusLift F Y₀ x z) :
    ∃ i : Y₀.left.residueField x →+* F.k,
      ∃ hi : i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k,
        z = (closedPointLift F Y₀ ⟨x, hx⟩ i hi) := by
  obtain ⟨i, hi⟩ := factor_field_point_native
    (z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k)))) x hz.2
  have hb : (Spec.map (CommRingCat.ofHom i) ≫ Y₀.left.fromSpecResidueField x) ≫
      Y₀.hom = Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k)) := by
    rw [hi, Category.assoc, pullback.condition]
    change z ≫ (F.geometricFiber Y₀).hom ≫ _ = _
    rw [← Category.assoc, hz.1, Category.id_comp]
  rw [Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
    ← Spec.map_comp, Spec.map_inj] at hb
  have hic : i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k :=
    congrArg (fun f : CommRingCat.of F.k₀ ⟶ CommRingCat.of F.k ↦ f.hom) hb
  refine ⟨i, hic, ?_⟩
  apply pullback.hom_ext
  · simpa only [closedPointLift, pullback.lift_fst] using hi.symm
  · simpa [closedPointLift, FiniteFieldDatum.geometricFiber] using hz.1

private def lift_of_embedding (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left))
    (i : Y₀.left.residueField x →+* F.k)
    (hi : i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k) :
    Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left :=
  closedPointLift F Y₀ ⟨x, hx⟩ i hi

private theorem lift_of_embedding_isLift (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left))
    (i : Y₀.left.residueField x →+* F.k)
    (hi : i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k) :
    IsLocalFrobeniusLift F Y₀ x (lift_of_embedding F Y₀ x hx i hi) := by
  constructor
  · simp [lift_of_embedding, closedPointLift, FiniteFieldDatum.geometricFiber]
  · simp only [lift_of_embedding, closedPointLift, pullback.lift_fst,
      Scheme.Hom.comp_apply]
    exact Y₀.left.fromSpecResidueField_apply x _

private theorem lift_of_embedding_surjective (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left)) :
    Function.Surjective (fun p : {i : Y₀.left.residueField x →+* F.k //
        i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k} ↦
      (⟨lift_of_embedding F Y₀ x hx p.1 p.2,
        lift_of_embedding_isLift F Y₀ x hx p.1 p.2⟩ :
        {z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left //
          IsLocalFrobeniusLift F Y₀ x z})) := by
  intro z
  obtain ⟨i, hi, hz⟩ := factor_lift_native F Y₀ x hx z.1 z.2
  refine ⟨⟨i, hi⟩, ?_⟩
  apply Subtype.ext
  exact hz.symm

private theorem lift_of_embedding_injective (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left)) :
    Function.Injective (fun p : {i : Y₀.left.residueField x →+* F.k //
        i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k} ↦
      (⟨lift_of_embedding F Y₀ x hx p.1 p.2,
        lift_of_embedding_isLift F Y₀ x hx p.1 p.2⟩ :
        {z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left //
          IsLocalFrobeniusLift F Y₀ x z})) := by
  intro p q h
  apply Subtype.ext
  have hb := congrArg
    (fun z => z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k))))
    (congrArg Subtype.val h)
  simp only [lift_of_embedding, closedPointLift, pullback.lift_fst] at hb
  exact congrArg CommRingCat.Hom.hom
    ((Scheme.specMap_comp_fromSpecResidueField_injective x) hb)

private theorem lift_of_embedding_bijective (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left)) :
    Function.Bijective (fun p : {i : Y₀.left.residueField x →+* F.k //
        i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k} ↦
      (⟨lift_of_embedding F Y₀ x hx p.1 p.2,
        lift_of_embedding_isLift F Y₀ x hx p.1 p.2⟩ :
        {z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left //
          IsLocalFrobeniusLift F Y₀ x z})) :=
  ⟨lift_of_embedding_injective F Y₀ x hx, lift_of_embedding_surjective F Y₀ x hx⟩

private theorem embedding_card_native (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left)) :
    Nat.card {i : Y₀.left.residueField x →+* F.k //
      i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k} =
      Y₀.hom.degreeOver x := by
  let : Algebra F.k₀ (Y₀.left.residueField x) :=
    (Y₀.hom.residueFieldAlgebraMap x).toAlgebra
  have : Module.Finite F.k₀ (Y₀.left.residueField x) := by
    exact Y₀.hom.finite_residueField_of_isClosed x hx
  let e : {i : Y₀.left.residueField x →+* F.k //
      i.comp (Y₀.hom.residueFieldAlgebraMap x) = algebraMap F.k₀ F.k} ≃
      (Y₀.left.residueField x →ₐ[F.k₀] F.k) :=
    { toFun := fun i =>
        { toRingHom := i.1
          commutes' := by
            intro a
            exact RingHom.congr_fun i.2 a }
      invFun := fun i =>
        ⟨i.toRingHom, by
          ext a
          exact i.commutes a⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [Nat.card_congr e, AlgHom.natCard_of_splits F.k₀ (Y₀.left.residueField x) F.k
    (fun _ => IsAlgClosed.splits _)]
  rfl

private theorem lift_card_native (x : Y₀.left) (hx : IsClosed ({x} : Set Y₀.left)) :
    Nat.card {z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left //
      IsLocalFrobeniusLift F Y₀ x z} = Y₀.hom.degreeOver x := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (lift_of_embedding_bijective F Y₀ x hx)), embedding_card_native F Y₀ x hx]

private theorem local_trace_conjugacy {R : Type*} [CommRing R]
    [HasDerivedCategory (ModuleCat R)]
    {P Q : DerivedCategory (ModuleCat R)}
    (hP : DerivedCategory.IsPerfectRingComplex P)
    (hQ : DerivedCategory.IsPerfectRingComplex Q)
    (f : P ⟶ P) (g : Q ⟶ Q) (e : P ≅ Q)
    (hf : f = e.hom ≫ g ≫ e.inv) :
    DerivedCategory.perfectCategoricalTrace P hP f =
      DerivedCategory.perfectCategoricalTrace Q hQ g := by
  let := DerivedCategory.perfectTraceCanonicalBraiding (ModuleCat R)
  let := DerivedCategory.perfectTraceHasRightDual P hP
  let := DerivedCategory.perfectTraceHasRightDual Q hQ
  unfold DerivedCategory.perfectCategoricalTrace
  apply congrArg DerivedCategory.perfectTraceScalar
  apply MonoidalCategory.trace_eq_of_iso e f g
  rw [hf]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- All clauses of local Frobenius conjugacy, on the native condensed finite coefficient
category and on literal point-fibre complexes.

Source: literature/blueprint/latest/blueprint/sec-trace-formula/sk-c-proper-global/
lem-trf-local-frobenius-conjugacy.md, clauses 1--3, with the DAG's normalized k-points
(blueprint: lem-trf-local-frobenius-conjugacy).

Proof: (1) Lifts correspond to k₀-embeddings of the closed point's finite residue field
into k. The unique subfield of cardinality q^d and its cyclic Frobenius Galois group
show there are d, forming the stated orbit. The affine formula for G sends an embedding
e to sigma e. For d dividing m the embedding factors uniquely through F_(q^m), and the
q^m-power formula fixes the lift under Phi^m.
(2) Reparametrize every pointed neighbourhood by Spec(sigma^i), keeping its section.
The stalk colimit gives the reparametrization, and the pullback comparison is induced
by the base-change neighbourhood. At Spec k the stalk is exact terminal evaluation.
These are the same maps as insertion and the derived pullback compositor used above.
Their identity, composition and naturality laws, together with the owning Weil-iterate
cocycle, give T_0=id and T_(i+j)=T_j at G^i(z) followed by T_i at z, also at zero indices.
(3) The normalized absolute-Frobenius trivialization defining kappa removes precisely
the Spec(sigma^m) reparametrization at a Phi^m-fixed lift. Thus the specified local
Frobenius equals the circuit transport T_m. The two cocycle expansions of T_(i+m)
and T_(m+i), using G^m(z)=z, give T_i F_(y_i,m)=F_(y_0,m) T_i. Invert T_i to obtain
the displayed conjugacy. Compact-support perfectness at geometric stalks gives bounded
finite-projective point complexes, so categorical trace is defined and invariant under
this conjugacy. Set m=d and enumerate every lift to obtain one-circuit independence.
The HEq laws express equality after the explicitly stated equalities of source points.
-/
theorem local_frobenius_conjugacy (hEll : ell ≠ F.p)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (x : Y₀.left) (_hx : IsClosed ({x} : Set Y₀.left)) :
    letI : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (condensedScalarRing (finiteCoefficient ell E n))) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    Nat.card {z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left //
      IsLocalFrobeniusLift F Y₀ x z} = Y₀.hom.degreeOver x ∧
    ∀ (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
      (_hz : IsLocalFrobeniusLift F Y₀ x z),
    ∃ (hd : 1 ≤ Y₀.hom.degreeOver x)
      (hP : ∀ i : ℕ, DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((localFrobeniusFibre F Y₀ ell E n (localFrobeniusOrbit F Y₀ z i)).obj K.carrier.obj))
      (hP₀ : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj)),
      (∀ i : ℕ, IsLocalFrobeniusLift F Y₀ x (localFrobeniusOrbit F Y₀ z i)) ∧
      Function.Injective
        (fun i : Fin (Y₀.hom.degreeOver x) ↦ localFrobeniusOrbit F Y₀ z i.val) ∧
      (∀ w : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left,
        IsLocalFrobeniusLift F Y₀ x w →
        ∃ i : Fin (Y₀.hom.degreeOver x), localFrobeniusOrbit F Y₀ z i.val = w) ∧
      (∀ i : ℕ, localFrobeniusOrbit F Y₀ z (i + Y₀.hom.degreeOver x) =
        localFrobeniusOrbit F Y₀ z i) ∧
      (∀ i : ℕ, localFrobeniusOrbit F Y₀ z i =
        ((fun w ↦ localFrobeniusOrbit F Y₀ w 1)^[i]) z) ∧
      (∀ i j : ℕ, localFrobeniusOrbit F Y₀ (localFrobeniusOrbit F Y₀ z i) j =
        localFrobeniusOrbit F Y₀ z (i + j)) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∃! y : F.extensionPoints Y₀ m hm,
          extensionPointGeometry F Y₀ m hm y = localFrobeniusOrbit F Y₀ z i) ∧
      HEq (localFrobeniusTransport F Y₀ ell E n hn K z 0).hom
        (𝟙 ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj)) ∧
      (∀ i j : ℕ,
        HEq (localFrobeniusTransport F Y₀ ell E n hn K z (i + j)).hom
          ((localFrobeniusTransport F Y₀ ell E n hn K (localFrobeniusOrbit F Y₀ z i) j).hom ≫
            (localFrobeniusTransport F Y₀ ell E n hn K z i).hom)) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        (localFrobeniusOrbit F Y₀ z i) ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ m =
          localFrobeniusOrbit F Y₀ z i) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∀ (y₀ yᵢ : F.extensionPoints Y₀ m hm)
          (hy₀ : extensionPointGeometry F Y₀ m hm y₀ = z)
          (hyᵢ : extensionPointGeometry F Y₀ m hm yᵢ = localFrobeniusOrbit F Y₀ z i),
        localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm yᵢ _ hyᵢ =
          (localFrobeniusTransport F Y₀ ell E n hn K z i).hom ≫
            localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm y₀ z hy₀ ≫
            (localFrobeniusTransport F Y₀ ell E n hn K z i).inv ∧
        DerivedCategory.perfectCategoricalTrace _ (hP i)
            (localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm yᵢ _ hyᵢ) =
          DerivedCategory.perfectCategoricalTrace _ hP₀
            (localFrobeniusAtLift F Y₀ ell E n hn hEll K m hm y₀ z hy₀)) ∧
      (∀ w : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left,
        IsLocalFrobeniusLift F Y₀ x w →
        ∀ (y₀ y₁ : F.extensionPoints Y₀ (Y₀.hom.degreeOver x) hd)
          (hy₀ : extensionPointGeometry F Y₀ _ hd y₀ = z)
          (hy₁ : extensionPointGeometry F Y₀ _ hd y₁ = w),
        ∃ e : (localFrobeniusFibre F Y₀ ell E n w).obj K.carrier.obj ≅
            (localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj,
          localFrobeniusAtLift F Y₀ ell E n hn hEll K _ hd y₁ w hy₁ = e.hom ≫
            localFrobeniusAtLift F Y₀ ell E n hn hEll K _ hd y₀ z hy₀ ≫ e.inv) := by
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (condensedScalarRing (finiteCoefficient ell E n))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  constructor
  · exact lift_card_native F Y₀ x _hx
  · intro z hz
    obtain ⟨hd, h1, h2, h3, h4, h7, ht2⟩ :=
      local_frobenius_conjugacy_orbit F Y₀ x _hx z hz
    obtain ⟨hP, hP₀, ht0, ht1, hc⟩ :=
      local_frobenius_conjugacy_transport F Y₀ ell E n hn hEll K x _hx z hz
    refine ⟨hd, hP, hP₀, h1, h2, h3, h4,
      localFrobeniusOrbit_iterate F Y₀ z, localFrobeniusOrbit_add F Y₀ z,
      h7, ht0, ht1, ht2, ?_, ?_⟩
    · intro m hm hdm i y₀ yᵢ hy₀ hyᵢ
      have he := hc m hm hdm i y₀ yᵢ hy₀ hyᵢ
      exact ⟨he, local_trace_conjugacy (hP i) hP₀ _ _
        (localFrobeniusTransport F Y₀ ell E n hn K z i) he⟩
    · intro w hw y₀ y₁ hy₀ hy₁
      obtain ⟨i, hi⟩ := h3 w hw
      cases hi
      refine ⟨localFrobeniusTransport F Y₀ ell E n hn K z i.val, ?_⟩
      exact hc (Y₀.hom.degreeOver x) hd (dvd_refl _) i.val y₀ y₁ hy₀ hy₁

end WeilConjectures.CondensedFrobeniusOperators
