/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Defs.Filter
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import Sheaf.RingTheory.ParameterRootColimit
import WeilConjectures.RingTheory.FilteredColimitIsDomain
import Sheaf.RingTheory.HenselianParameterRootRegularity
import WeilConjectures.RingTheory.RegularSequencePowers
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic

/-! # Domains in henselian parameter-root towers

Source: ILO, Travaux de Gabber, IX Proposition 2.1, printed p.133; Stacks 00NU,
00J9, 09XI and 0AFS. The filtered coefficient and root colimits are the agent extension
recorded in the DAG (blueprint: lem-sfb-henselian-parameter-root-domain-tower).

The finite quotient is the existing `Algebra.pthRootAlgebra`, whose degree argument
is unrestricted. The full quotient is the existing `tameRootAlgebra`; setting its
order filter to 1 includes every positive order. No invertibility assumption is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace RingTheory

/-- The labelled root in the existing simultaneous quotient.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootCoordinate {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) : Algebra.pthRootAlgebra n r R t :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Evaluation at roots kills the relation ideal.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: evaluation sends X_i^n-t_i to x_i^n-g(t_i)=0. Its kernel is an ideal,
so it contains the ideal spanned by these generators. -/
theorem parameterRootRelations_vanish {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {S : Type v} [CommRing S]
    (g : R →+* S) (x : Fin r → S) (hx : ∀ i, x i ^ n = g (t i)) :
    ∀ a ∈ Ideal.span (Set.range (fun i : Fin r ↦
      (MvPolynomial.X i : MvPolynomial (Fin r) R) ^ n - MvPolynomial.C (t i))),
      MvPolynomial.eval₂Hom g x a = 0 := by
  have hle : Ideal.span (Set.range (fun i : Fin r ↦
      (MvPolynomial.X i : MvPolynomial (Fin r) R) ^ n - MvPolynomial.C (t i))) ≤
      RingHom.ker (MvPolynomial.eval₂Hom g x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simpa using sub_eq_zero.mpr (hx i)
  exact fun a ha ↦ hle ha

/-- The canonical map determined by coefficients and labelled roots.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootLift {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {S : Type v} [CommRing S]
    (g : R →+* S) (x : Fin r → S) (hx : ∀ i, x i ^ n = g (t i)) :
    Algebra.pthRootAlgebra n r R t →+* S :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom g x)
    (parameterRootRelations_vanish t n g x hx)

@[simp] private theorem parameterRootLift_coeff {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {S : Type v} [CommRing S]
    (g : R →+* S) (x : Fin r → S) (hx : ∀ i, x i ^ n = g (t i)) (a : R) :
    parameterRootLift t n g x hx (algebraMap R _ a) = g a := by
  change parameterRootLift t n g x hx (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _
  simp [parameterRootLift, Ideal.Quotient.lift_mk]

@[simp] private theorem parameterRootLift_root {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) {S : Type v} [CommRing S]
    (g : R →+* S) (x : Fin r → S) (hx : ∀ i, x i ^ n = g (t i)) (i : Fin r) :
    parameterRootLift t n g x hx (parameterRootCoordinate t n i) = x i := by
  simp [parameterRootLift, parameterRootCoordinate, Ideal.Quotient.lift_mk]

/-- The root relation after changing coefficients.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: X_i^n-s_i is a generator of the quotient ideal; its class is zero.
Replace s_i by g(t_i) using the labelled compatibility. -/
theorem parameterRootMap_relation {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {r : ℕ} (t : Fin r → R) (s : Fin r → S) (n : ℕ)
    (g : R →+* S) (h : ∀ i, g (t i) = s i) :
    ∀ i, parameterRootCoordinate s n i ^ n =
      ((algebraMap S (Algebra.pthRootAlgebra n r S s)).comp g) (t i) := by
  intro i
  simpa only [RingHom.comp_apply, h i, parameterRootCoordinate,
    Algebra.ParameterRoot.root] using Algebra.ParameterRoot.root_pow s n i

/-- Change coefficients, fixing every labelled root.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootMap {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {r : ℕ} (t : Fin r → R) (s : Fin r → S) (n : ℕ)
    (g : R →+* S) (h : ∀ i, g (t i) = s i) :
    Algebra.pthRootAlgebra n r R t →+* Algebra.pthRootAlgebra n r S s :=
  parameterRootLift t n ((algebraMap S _).comp g) (parameterRootCoordinate s n)
    (parameterRootMap_relation t s n g h)

/-- Laws for the canonical coefficient substitutions.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: both maps in each equality agree on coefficients and on all root coordinates;
polynomial extensionality and quotient surjectivity give the equalities. -/
theorem parameterRootMap_laws {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    {T : Type u} [CommRing T] {r : ℕ} (t : Fin r → R) (s : Fin r → S)
    (z : Fin r → T) (n : ℕ) (g : R →+* S) (h : S →+* T)
    (hg : ∀ i, g (t i) = s i) (hh : ∀ i, h (s i) = z i) :
    parameterRootMap t t n (RingHom.id R) (fun _ ↦ rfl) = RingHom.id _ ∧
    (parameterRootMap s z n h hh).comp (parameterRootMap t s n g hg) =
      parameterRootMap t z n (h.comp g) (fun i ↦ (congrArg h (hg i)).trans (hh i)) := by
  constructor
  · apply Algebra.ParameterRoot.ringHom_ext t n
    · ext a
      change parameterRootMap t t n (RingHom.id R) (fun _ ↦ rfl)
        (algebraMap R _ a) = algebraMap R _ a
      simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply,
        RingHom.id_apply]
    · intro i
      change parameterRootMap t t n _ _ (parameterRootCoordinate t n i) = _
      simp only [parameterRootMap, parameterRootLift_root, RingHom.id_apply]
      rfl
  · apply Algebra.ParameterRoot.ringHom_ext t n
    · ext a
      change parameterRootMap s z n h hh
        (parameterRootMap t s n g hg (algebraMap R _ a)) =
        parameterRootMap t z n (h.comp g)
          (fun i ↦ (congrArg h (hg i)).trans (hh i)) (algebraMap R _ a)
      simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply]
    · intro i
      change parameterRootMap s z n h hh
        (parameterRootMap t s n g hg (parameterRootCoordinate t n i)) =
        parameterRootMap t z n _ _ (parameterRootCoordinate t n i)
      simp only [parameterRootMap, parameterRootLift_root]

/-- The functor laws for a diagram of the finite root quotients.
Source: Stacks 04AX (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: apply the coefficient substitution laws, using the functor laws of F;
proof irrelevance removes differences between proofs of labelled compatibility. -/
theorem parameterRootDiagram_laws {I : Type u} [SmallCategory I]
    (F : I ⥤ CommRingCat.{u}) {r : ℕ} (t : ∀ j, Fin r → F.obj j)
    (ht : ∀ {j k} (a : j ⟶ k) i, (F.map a).hom (t j i) = t k i) (n : ℕ) :
    (∀ j, CommRingCat.ofHom (parameterRootMap (t j) (t j) n (F.map (𝟙 j)).hom
      (ht (𝟙 j))) = 𝟙 (CommRingCat.of (Algebra.pthRootAlgebra n r (F.obj j) (t j)))) ∧
    (∀ {j k l} (a : j ⟶ k) (b : k ⟶ l),
      CommRingCat.ofHom (parameterRootMap (t j) (t l) n (F.map (a ≫ b)).hom
        (ht (a ≫ b))) =
      CommRingCat.ofHom (parameterRootMap (t j) (t k) n (F.map a).hom (ht a)) ≫
      CommRingCat.ofHom (parameterRootMap (t k) (t l) n (F.map b).hom (ht b))) := by
  constructor
  · intro j
    have hf : (F.map (𝟙 j)).hom = RingHom.id (F.obj j) := by
      simp
    simp only [hf]
    exact congrArg CommRingCat.ofHom
      ((parameterRootMap_laws (t j) (t j) (t j) n (RingHom.id _) (RingHom.id _)
        (fun _ ↦ rfl) (fun _ ↦ rfl)).1)
  · intro j k l a b
    have hf : (F.map (a ≫ b)).hom = (F.map b).hom.comp (F.map a).hom := by
      simp
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, hf]
    exact ((parameterRootMap_laws (t j) (t k) (t l) n (F.map a).hom (F.map b).hom
      (ht a) (ht b)).2).symm

/-- The canonical coefficient diagram at a fixed root order.
Source: Stacks 04AX and ILO IX 2.1
(blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootDiagram {I : Type u} [SmallCategory I]
    (F : I ⥤ CommRingCat.{u}) {r : ℕ} (t : ∀ j, Fin r → F.obj j)
    (ht : ∀ {j k} (a : j ⟶ k) i, (F.map a).hom (t j i) = t k i) (n : ℕ) :
    I ⥤ CommRingCat.{u} where
  obj j := .of (Algebra.pthRootAlgebra n r (F.obj j) (t j))
  map a := CommRingCat.ofHom (parameterRootMap _ _ n (F.map a).hom (ht a))
  map_id j := (parameterRootDiagram_laws F t ht n).1 j
  map_comp a b := (parameterRootDiagram_laws F t ht n).2 a b

/-- Naturality of the root cocone induced by a coefficient cocone.
Source: Stacks 04AX (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: the cocone equality on coefficients and equality on labelled roots determine
both composites, by polynomial extensionality and quotient surjectivity. -/
theorem parameterRootCocone_naturality {I : Type u} [SmallCategory I]
    (F : I ⥤ CommRingCat.{u}) {r : ℕ} (t : ∀ j, Fin r → F.obj j)
    (ht : ∀ {j k} (a : j ⟶ k) i, (F.map a).hom (t j i) = t k i)
    (c : Cocone F) (s : Fin r → c.pt)
    (hs : ∀ j i, (c.ι.app j).hom (t j i) = s i) (n : ℕ) :
    ∀ {j k} (a : j ⟶ k),
      (parameterRootDiagram F t ht n).map a ≫
        CommRingCat.ofHom (parameterRootMap (t k) s n (c.ι.app k).hom (hs k)) =
      CommRingCat.ofHom (parameterRootMap (t j) s n (c.ι.app j).hom (hs j)) := by
  intro j k a
  have hf : (c.ι.app k).hom.comp (F.map a).hom = (c.ι.app j).hom := by
    exact congrArg CommRingCat.Hom.hom (c.w a)
  apply CommRingCat.hom_ext
  change (parameterRootMap (t k) s n (c.ι.app k).hom (hs k)).comp
    (parameterRootMap (t j) (t k) n (F.map a).hom (ht a)) = _
  rw [(parameterRootMap_laws (t j) (t k) s n (F.map a).hom (c.ι.app k).hom
    (ht a) (hs k)).2]
  simp only [hf]
  rfl

/-- The canonical cocone with vertex the finite root quotient of the coefficient colimit.
Source: Stacks 04AX and ILO IX 2.1
(blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootCocone {I : Type u} [SmallCategory I]
    (F : I ⥤ CommRingCat.{u}) {r : ℕ} (t : ∀ j, Fin r → F.obj j)
    (ht : ∀ {j k} (a : j ⟶ k) i, (F.map a).hom (t j i) = t k i)
    (c : Cocone F) (s : Fin r → c.pt)
    (hs : ∀ j i, (c.ι.app j).hom (t j i) = s i) (n : ℕ) :
    Cocone (parameterRootDiagram F t ht n) where
  pt := .of (Algebra.pthRootAlgebra n r c.pt s)
  ι := { app j := CommRingCat.ofHom (parameterRootMap (t j) s n (c.ι.app j).hom (hs j))
         naturality _ _ a := parameterRootCocone_naturality F t ht c s hs n a }

/-- The power substitution respects each finite-level equation.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: if n divides m then n*(m/n)=m. The m-th root relation therefore says
(x_m^(m/n))^n=t_i, including n=1 and m=n. -/
theorem parameterRootPower_relation {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : ℕ) (hn : 0 < n) (h : n ∣ m) :
    ∀ i, (parameterRootCoordinate t m i ^ (m / n)) ^ n =
      algebraMap R (Algebra.pthRootAlgebra m r R t) (t i) := by
  have _ := hn
  intro i
  rw [← pow_mul, Nat.div_mul_cancel h]
  exact Algebra.ParameterRoot.root_pow t m i

/-- The canonical divisibility transition, fixing coefficients and taking powers of roots.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootPower {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n m : ℕ) (hn : 0 < n) (h : n ∣ m) :
    Algebra.pthRootAlgebra n r R t →+* Algebra.pthRootAlgebra m r R t :=
  parameterRootLift t n (algebraMap R _) (fun i ↦ parameterRootCoordinate t m i ^ (m / n))
    (parameterRootPower_relation t n m hn h)

/-- The finite roots map to the corresponding generators of the full presentation.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: the equation X_(i,n)^n-t_i is one of tameRootRelations, hence is zero
in the full quotient. -/
theorem parameterRootFull_relation {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (p : ℕ) (n : TameRootOrder p) :
    ∀ i, (Ideal.Quotient.mk _ (MvPolynomial.X (i, n)) : tameRootAlgebra p t) ^ n.val =
      algebraMap R (tameRootAlgebra p t) (t i) := by
  exact Algebra.ParameterRoot.fullRoot_pow t p n

/-- The canonical inclusion of a finite level into the compatible-root presentation.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower). -/
def parameterRootInclusion {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (p : ℕ) (n : TameRootOrder p) :
    Algebra.pthRootAlgebra n.val r R t →+* tameRootAlgebra p t :=
  parameterRootLift t n.val (algebraMap R _)
    (fun i ↦ Ideal.Quotient.mk _ (MvPolynomial.X (i, n)))
    (parameterRootFull_relation t p n)

/-- The full quotient is the divisibility colimit, with the specified power transitions.
Here p=1 gives all positive orders; prime p gives precisely the prime-to-p orders.
Source: ILO IX 2.1 and Stacks 04AX
(blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: transitions preserve equations by n*(m/n)=m. They are identity and compose
since their values on every coefficient and root do so. The full relations give the
cocone identities. A compatible family defines evaluation on every full generator;
its equations and transition relations vanish. Quotient evaluation gives the unique
map, with uniqueness checked on coefficients and on all labelled generators. -/
theorem parameterRootFull_isColimit {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (p : ℕ) (hp : p = 1 ∨ p.Prime) :
    (∀ n : TameRootOrder p,
      parameterRootPower t n.val n.val n.property.1 (dvd_refl _) = RingHom.id _) ∧
    (∀ (n m l : TameRootOrder p) (h : n.val ∣ m.val) (h' : m.val ∣ l.val),
      (parameterRootPower t m.val l.val m.property.1 h').comp
        (parameterRootPower t n.val m.val n.property.1 h) =
      parameterRootPower t n.val l.val n.property.1 (h.trans h')) ∧
    (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
      (parameterRootInclusion t p m).comp
        (parameterRootPower t n.val m.val n.property.1 h) = parameterRootInclusion t p n) ∧
    (∀ (S : Type (max u v)) [CommRing S]
      (f : ∀ n : TameRootOrder p, Algebra.pthRootAlgebra n.val r R t →+* S),
      (∀ (n m : TameRootOrder p) (h : n.val ∣ m.val),
        (f m).comp (parameterRootPower t n.val m.val n.property.1 h) = f n) →
      ∃! g : tameRootAlgebra p t →+* S, ∀ n, g.comp (parameterRootInclusion t p n) = f n) := by
  have _ := hp
  have hpower (n m : TameRootOrder p) (h : n.val ∣ m.val) :
      parameterRootPower t n.val m.val n.property.1 h =
        (Algebra.ParameterRoot.transition t n.val m.val h).toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext <;> intro a <;>
      simp [parameterRootPower, parameterRootLift, Algebra.ParameterRoot.transition,
        Algebra.ParameterRoot.lift, MvPolynomial.aeval, Ideal.Quotient.lift_mk,
        parameterRootCoordinate]
  have hinclusion (n : TameRootOrder p) : parameterRootInclusion t p n =
      (Algebra.ParameterRoot.inclusion t p n).toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext <;> intro a <;>
      simp [parameterRootInclusion, parameterRootLift, Algebra.ParameterRoot.inclusion,
        Algebra.ParameterRoot.lift, MvPolynomial.aeval, Ideal.Quotient.lift_mk,
        Algebra.ParameterRoot.fullRoot]
  simp_rw [hpower, hinclusion]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact congrArg AlgHom.toRingHom
      (Algebra.ParameterRoot.transition_self t n.val n.property.1)
  · intro n m l h h'
    exact congrArg AlgHom.toRingHom (Algebra.ParameterRoot.transition_comp t _ _ _ h h')
  · intro n m h
    exact congrArg AlgHom.toRingHom (Algebra.ParameterRoot.inclusion_comp t p n m h)
  · intro S _ f hf
    exact Algebra.ParameterRoot.full_isColimit t p f hf

private def rootQuotientEquiv {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (hn : 0 < n) :
    (Algebra.pthRootAlgebra n r R t ⧸
      Ideal.span (Set.range (parameterRootCoordinate t n))) ≃+*
      (R ⧸ Ideal.span (Set.range t)) := by
  let B := Algebra.pthRootAlgebra n r R t
  let J := Ideal.span (Set.range t)
  let L := Ideal.span (Set.range (parameterRootCoordinate t n))
  let ev : B →+* R ⧸ J := parameterRootLift t n (Ideal.Quotient.mk J) (fun _ ↦ 0)
    (fun i ↦ by
      rw [zero_pow hn.ne']
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (show t i ∈ Set.range t from ⟨i, rfl⟩))).symm)
  have hev (i : Fin r) : ev (parameterRootCoordinate t n i) = 0 :=
    parameterRootLift_root ..
  let f : B ⧸ L →+* R ⧸ J := Ideal.Quotient.lift L ev (by
    change L ≤ RingHom.ker ev
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hev i)
  let coeff : R →+* B ⧸ L := (Ideal.Quotient.mk L).comp (algebraMap R B)
  have hcoeff (i : Fin r) : coeff (t i) = 0 := by
    change Ideal.Quotient.mk L (algebraMap R B (t i)) = 0
    rw [← Algebra.ParameterRoot.root_pow t n i, map_pow]
    have hx : Ideal.Quotient.mk L (Algebra.ParameterRoot.root t n i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [hx, zero_pow hn.ne']
  let g : R ⧸ J →+* B ⧸ L := Ideal.Quotient.lift J coeff (by
    change J ≤ RingHom.ker coeff
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hcoeff i)
  have hfg : f.comp g = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    change ev (algebraMap R B a) = Ideal.Quotient.mk J a
    exact parameterRootLift_coeff ..
  have hgf : g.comp f = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Algebra.ParameterRoot.ringHom_ext t n
    · ext a
      change g (ev (algebraMap R B a)) = Ideal.Quotient.mk L (algebraMap R B a)
      rw [parameterRootLift_coeff]
      rfl
    · intro i
      change g (ev (parameterRootCoordinate t n i)) =
        Ideal.Quotient.mk L (parameterRootCoordinate t n i)
      rw [hev, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span
        (show parameterRootCoordinate t n i ∈
        Set.range (parameterRootCoordinate t n) from ⟨i, rfl⟩))).symm
  exact RingEquiv.ofRingHom f g (by exact hfg) (by exact hgf)

@[simp] private theorem rootQuotientEquiv_coeff {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (hn : 0 < n) (a : R) :
    rootQuotientEquiv t n hn (Ideal.Quotient.mk _
      (algebraMap R (Algebra.pthRootAlgebra n r R t) a)) =
        Ideal.Quotient.mk _ a := by
  simp only [rootQuotientEquiv, RingEquiv.ofRingHom_apply, Ideal.Quotient.lift_mk,
    parameterRootLift_coeff]

private def rootLocalQuotientData {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (hn : 0 < n)
    (q : Ideal (Algebra.pthRootAlgebra n r R t)) [q.IsPrime]
    (hx : ∀ i, parameterRootCoordinate t n i ∈ q) :
    { e : (Localization.AtPrime q ⧸ Ideal.span (Set.range
      (fun i ↦ algebraMap _ (Localization.AtPrime q) (parameterRootCoordinate t n i)))) ≃+*
    (Localization.AtPrime (q.comap (algebraMap R (Algebra.pthRootAlgebra n r R t))) ⧸
      (Ideal.span (Set.range t)).map (algebraMap R
        (Localization.AtPrime (q.comap (algebraMap R (Algebra.pthRootAlgebra n r R t)))))) //
      ∀ a : R,
      e (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime q)
        (algebraMap R (Algebra.pthRootAlgebra n r R t) a))) =
        Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime
          (q.comap (algebraMap R (Algebra.pthRootAlgebra n r R t)))) a) } := by
  let B := Algebra.pthRootAlgebra n r R t
  let L := Ideal.span (Set.range (parameterRootCoordinate t n))
  let J := Ideal.span (Set.range t)
  let m := q.comap (algebraMap R B)
  let e := rootQuotientEquiv t n hn
  have hL : L ≤ q := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  let qbar := q.map (Ideal.Quotient.mk L)
  have hqbar : qbar.comap (Ideal.Quotient.mk L) = q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    simp only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hL]
  have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hL
  let mbar := qbar.comap e.symm.toRingHom
  have hmbar : mbar.comap (Ideal.Quotient.mk J) = m := by
    ext a
    change e.symm (Ideal.Quotient.mk J a) ∈ qbar ↔ algebraMap R B a ∈ q
    rw [show e.symm (Ideal.Quotient.mk J a) =
      Ideal.Quotient.mk L (algebraMap R B a) from
        (e.symm_apply_eq).mpr (rootQuotientEquiv_coeff t n hn a).symm]
    change algebraMap R B a ∈ qbar.comap (Ideal.Quotient.mk L) ↔ _
    rw [hqbar]
  have hS : Algebra.algebraMapSubmonoid (B ⧸ L) q.primeCompl = qbar.primeCompl := by
    change q.primeCompl.map (Ideal.Quotient.mk L) = _
    simpa only [hqbar] using Ideal.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective qbar
  have hT : Algebra.algebraMapSubmonoid (R ⧸ J) m.primeCompl = mbar.primeCompl := by
    change m.primeCompl.map (Ideal.Quotient.mk J) = _
    simpa only [hmbar] using Ideal.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective mbar
  let QB := Localization.AtPrime q ⧸ L.map (algebraMap B (Localization.AtPrime q))
  let QR := Localization.AtPrime m ⧸ J.map (algebraMap R (Localization.AtPrime m))
  have : IsLocalization qbar.primeCompl QB := hS ▸ inferInstance
  have : IsLocalization mbar.primeCompl QR := hT ▸ inferInstance
  have hmap : qbar.primeCompl.map e.toMonoidHom = mbar.primeCompl := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ¬ e.symm (e y) ∈ qbar
      rwa [e.symm_apply_apply]
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  have hLmap : L.map (algebraMap B (Localization.AtPrime q)) =
      Ideal.span (Set.range (fun i ↦ algebraMap B (Localization.AtPrime q)
        (parameterRootCoordinate t n i))) := by
    rw [Ideal.map_span]
    congr 1
    exact (Set.range_comp _ _).symm
  let E := (Ideal.quotEquivOfEq hLmap.symm).trans
    (IsLocalization.ringEquivOfRingEquiv QB QR e hmap)
  refine ⟨E, ?_⟩
  intro a
  change (IsLocalization.ringEquivOfRingEquiv QB QR e hmap)
    (algebraMap (B ⧸ L) QB (Ideal.Quotient.mk L (algebraMap R B a))) = _
  rw [IsLocalization.ringEquivOfRingEquiv_eq, rootQuotientEquiv_coeff]
  rfl

private def rootLocalQuotientEquiv {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (hn : 0 < n)
    (q : Ideal (Algebra.pthRootAlgebra n r R t)) [q.IsPrime]
    (hx : ∀ i, parameterRootCoordinate t n i ∈ q) :
    (Localization.AtPrime q ⧸ Ideal.span (Set.range
      (fun i ↦ algebraMap _ (Localization.AtPrime q) (parameterRootCoordinate t n i)))) ≃+*
    (Localization.AtPrime (q.comap (algebraMap R (Algebra.pthRootAlgebra n r R t))) ⧸
      (Ideal.span (Set.range t)).map (algebraMap R
        (Localization.AtPrime (q.comap (algebraMap R (Algebra.pthRootAlgebra n r R t)))))) :=
  (rootLocalQuotientData t n hn q hx).val

private theorem rootLocalQuotientEquiv_coeff {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (hn : 0 < n)
    (q : Ideal (Algebra.pthRootAlgebra n r R t)) [q.IsPrime]
    (hx : ∀ i, parameterRootCoordinate t n i ∈ q) (a : R) :
    rootLocalQuotientEquiv t n hn q hx
      (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime q)
        (algebraMap R (Algebra.pthRootAlgebra n r R t) a))) =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime
        (q.comap (algebraMap R (Algebra.pthRootAlgebra n r R t)))) a) :=
  (rootLocalQuotientData t n hn q hx).property a

private theorem regular_of_maximals {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h : ∀ (q : Ideal R) [q.IsMaximal], IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularRing R := by
  apply isRegularRing_iff.mpr
  intro p hp
  obtain ⟨q, hq, hpq⟩ := p.exists_le_maximal hp.ne_top
  have := hq
  let S := Localization.AtPrime q
  let Q := p.map (algebraMap R S)
  have hdisj : Disjoint (q.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr (fun _ hx hy ↦ hx (hpq hy))
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl S p hp hdisj
  have hcom : Q.comap (algebraMap R S) = p :=
    IsLocalization.under_map_of_isPrime_disjoint q.primeCompl S hp hdisj
  have := h q
  have := (IsRegularLocalRing.localization_at_prime_and_isRegularRing Q).1
  have hreg : IsRegularLocalRing (Localization.AtPrime (Q.comap (algebraMap R S))) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        q.primeCompl Q).toRingEquiv.symm
  have e := Localization.localRingEquiv (Q.comap (algebraMap R S)) p
    (RingEquiv.refl R) (hcom.trans (by ext; rfl))
  exact IsRegularLocalRing.of_ringEquiv e

private theorem rootLocal_regular {C : Type u} [CommRing C] [IsNoetherianRing C]
    {r : ℕ} (t : Fin r → C) (n : ℕ) (hn : 0 < n)
    [Module.Finite C (Algebra.pthRootAlgebra n r C t)]
    [Module.Free C (Algebra.pthRootAlgebra n r C t)]
    (q : Ideal (Algebra.pthRootAlgebra n r C t)) [q.IsMaximal]
    (hx : ∀ i, parameterRootCoordinate t n i ∈ q)
    (ht : RingTheory.Sequence.IsRegular
      (Localization.AtPrime (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t))))
      (List.ofFn (fun i ↦ algebraMap C (Localization.AtPrime
        (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t)))) (t i))))
    [IsRegularLocalRing (Localization.AtPrime
      (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t))) ⧸
        (Ideal.span (Set.range t)).map (algebraMap C
          (Localization.AtPrime
            (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t))))))] :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      (List.ofFn (fun i ↦ algebraMap _ (Localization.AtPrime q)
        (parameterRootCoordinate t n i))) ∧
    IsRegularLocalRing (Localization.AtPrime q) := by
  let B := Algebra.pthRootAlgebra n r C t
  have : IsNoetherianRing B := IsNoetherianRing.of_finite C B
  let m := q.comap (algebraMap C B)
  let A := Localization.AtPrime m
  let S := Localization.AtPrime q
  let f := Localization.localRingHom m q (algebraMap C B) rfl
  let : Algebra A S := f.toAlgebra
  have : Module.Flat A S := (RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat C B)) q m rfl)
  have hweak := ht.toIsWeaklyRegular.of_flat (S := S)
  have hweak' : RingTheory.Sequence.IsWeaklyRegular S
      (List.ofFn (fun i ↦ (algebraMap B S (parameterRootCoordinate t n i)) ^ n)) := by
    have heq : (List.ofFn (fun i ↦ algebraMap C A (t i))).map (algebraMap A S) =
        List.ofFn (fun i ↦ (algebraMap B S (parameterRootCoordinate t n i)) ^ n) := by
      rw [List.map_ofFn]
      congr 1
      funext i
      change f (algebraMap C A (t i)) = _
      rw [Localization.localRingHom_to_map]
      change algebraMap B S (algebraMap C B (t i)) =
        algebraMap B S (Algebra.ParameterRoot.root t n i) ^ n
      rw [← map_pow, Algebra.ParameterRoot.root_pow]
    exact heq ▸ hweak
  have hmem : ∀ x ∈ List.ofFn (fun i ↦
      (algebraMap B S (parameterRootCoordinate t n i)) ^ n), x ∈ IsLocalRing.maximalIdeal S := by
    intro x hx'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
    exact (IsLocalRing.maximalIdeal S).pow_mem_of_mem
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff S q _).mpr (hx i)) n hn
  have hpowers : RingTheory.Sequence.IsRegular S
      (List.ofFn (fun i ↦ (algebraMap B S (parameterRootCoordinate t n i)) ^ n)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hweak'
  have hseq := (RingTheory.Sequence.isRegular_ofFn_pow_iff S
    (fun i ↦ algebraMap B S (parameterRootCoordinate t n i)) (fun _ ↦ n)
    (fun _ ↦ hn)).mpr hpowers
  have hquot : IsRegularLocalRing (S ⧸ Ideal.span (Set.range
      (fun i ↦ algebraMap B S (parameterRootCoordinate t n i)))) :=
    IsRegularLocalRing.of_ringEquiv (rootLocalQuotientEquiv t n hn q hx).symm
  have he : Ideal.ofList (List.ofFn (fun i ↦
      algebraMap B S (parameterRootCoordinate t n i))) =
        Ideal.span (Set.range (fun i ↦ algebraMap B S (parameterRootCoordinate t n i))) := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_ofFn
  have : IsRegularLocalRing (S ⧸ Ideal.ofList (List.ofFn (fun i ↦
      algebraMap B S (parameterRootCoordinate t n i)))) := he ▸ hquot
  refine ⟨hseq, RingTheory.isRegularLocalRing_of_regularSequence_quotient S _ ?_ hseq⟩
  intro x hx'
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S q _).mpr (hx i)

private theorem spec_idempotents {R : Type u} [CommRing R]
    (h : ConnectedSpace (Spec (.of R))) (e : R) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have := h
  let E := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have H := (Scheme.connectedSpace_iff_isIdempotentElem (Spec (.of R))).mp h
    (E.symm e) (he.map E.symm.toRingHom)
  rcases H with H | H
  · left
    simpa only [map_zero, E.apply_symm_apply] using congrArg E H
  · right
    simpa only [map_one, E.apply_symm_apply] using congrArg E H

private theorem domain_of_regular_idempotents {R : Type u} [CommRing R]
    [IsRegularRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : IsDomain R := by
  let X := Spec (.of R)
  let E := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have : ConnectedSpace X := (Scheme.connectedSpace_iff_isIdempotentElem X).mpr (by
    intro e he
    rcases h (E e) (he.map E.toRingHom) with H | H
    · left
      exact E.injective (H.trans (map_zero E).symm)
    · right
      exact E.injective (H.trans (map_one E).symm))
  have : AlgebraicGeometry.IsRegular X := ⟨fun z ↦ IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (.of R) z).commRingCatIsoToRingEquiv.symm⟩
  have : IsIntegral X := AlgebraicGeometry.IsRegular.isIntegral X
  exact (AlgebraicGeometry.affine_isIntegral_iff (.of R)).mp inferInstance

private theorem root_idempotents {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) [HenselianRing R (Ideal.span (Set.range t))]
    (h : ConnectedSpace (Spec (.of (R ⧸ Ideal.span (Set.range t)))))
    (n : ℕ) (hn : 0 < n)
    [Module.Finite R (Algebra.pthRootAlgebra n r R t)]
    (e : Algebra.pthRootAlgebra n r R t) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  let B := Algebra.pthRootAlgebra n r R t
  let J := Ideal.span (Set.range t)
  let I := J.map (algebraMap R B)
  let L := Ideal.span (Set.range (parameterRootCoordinate t n))
  have hrad : L ≤ I.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_radical_iff.mpr ⟨n, (Algebra.ParameterRoot.root_pow t n i).symm ▸
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)⟩
  have hinj (a b : B) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
      (hab : Ideal.Quotient.mk L a = Ideal.Quotient.mk L b) : a = b := by
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp (hrad (Ideal.Quotient.eq.mp hab))
    have hnil : IsNilpotent (Ideal.Quotient.mk I a - Ideal.Quotient.mk I b) := by
      refine ⟨k, ?_⟩
      rw [← map_sub, ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
    have hmod := eq_of_isNilpotent_sub_of_isIdempotentElem
      (ha.map (Ideal.Quotient.mk I)) (hb.map (Ideal.Quotient.mk I)) hnil
    obtain ⟨c, hc, hu⟩ := Algebra.existsUnique_isIdempotentElem_of_henselianRing R J B
      (Ideal.Quotient.mk I b) (hb.map (Ideal.Quotient.mk I))
    exact (hu a ⟨ha, hmod⟩).trans (hu b ⟨hb, rfl⟩).symm
  let E := rootQuotientEquiv t n hn
  rcases spec_idempotents h (E (Ideal.Quotient.mk L e))
      ((he.map (Ideal.Quotient.mk L)).map E.toRingHom) with hz | ho
  · left
    exact hinj e 0 he .zero (E.injective (hz.trans (map_zero E).symm) |>.trans (map_zero _).symm)
  · right
    exact hinj e 1 he .one (E.injective (ho.trans (map_one E).symm) |>.trans (map_one _).symm)

/-- Finite root algebras of a henselian pair are regular domains, with the stated basis
and the exact local quotient at every maximal ideal.
Source: ILO IX 2.1, Stacks 09XI, 00J9, 00NU and 0AFS
(blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof:
1. HenselianRing.jac puts (t_i) in every maximal ideal. The nonempty residual
spectrum excludes the zero ring.
2. Successive monic division gives the bounded-monomial basis, finiteness, freeness,
injectivity of the coefficient map and Noetherianity (monic-quotient-free,
finite-type-algebra-noetherian).
3. Integral contraction of maximal ideals and x_i^n=t_i put all roots in every
maximal ideal. Eliminating the roots gives C/(t_i); localization gives the displayed
quotient (integral-algebra-ideal-in-radical, localization-at-prime-of-quotient).
4. The finite free coefficient map induces a flat map on the maximal localizations.
Flat base change preserves weak regularity of the parameter sequence, whose images
are the positive powers of the roots. These powers lie in the maximal ideal, so
they form a regular sequence. Reflect regularity through positive powers to get
the regular sequence of roots.
5. Lift regularity from its regular quotient by regular-local-lift-regular-sequence-
quotient, then localize regular local rings (regular-local-localization).
6. The root ideal lies in the radical of the extended parameter ideal. Two
idempotents congruent modulo the roots therefore have equal images modulo the
parameters, by uniqueness modulo nil ideals, and are equal by henselian uniqueness
of idempotent lifts. The root quotient is C/(t_i), whose spectrum is connected.
Thus the root algebra has only the idempotents zero and one, and its spectrum is
connected nonempty.
7. A connected regular scheme is integral (regular-connected-integral); affine
stalk localization identifies the ring with a nonzero domain. For n=1 this is C.
Regularity of the parameter sequence makes each t_i nonzero, so their product is
nonzero in C and remains nonzero under the injective coefficient map. -/
theorem henselianParameterRoot_finite {C : Type u} [CommRing C] [IsNoetherianRing C]
    {r : ℕ} (t : Fin r → C) [HenselianRing C (Ideal.span (Set.range t))]
    (hconnected : ConnectedSpace (Spec (.of (C ⧸ Ideal.span (Set.range t)))))
    (hlocal : ∀ (m : Ideal C) [m.IsMaximal],
      RingTheory.Sequence.IsRegular (Localization.AtPrime m)
        (List.ofFn (fun i ↦ algebraMap C (Localization.AtPrime m) (t i))) ∧
      IsRegularLocalRing (Localization.AtPrime m ⧸
        Ideal.map (algebraMap C (Localization.AtPrime m)) (Ideal.span (Set.range t))))
    (n : ℕ) (hn : 0 < n) :
    (∃ b : Module.Basis (Fin r → Fin n) C (Algebra.pthRootAlgebra n r C t),
      ∀ a, b a = ∏ i, parameterRootCoordinate t n i ^ (a i).val) ∧
    Module.Finite C (Algebra.pthRootAlgebra n r C t) ∧
    Module.Free C (Algebra.pthRootAlgebra n r C t) ∧
    IsRegularRing (Algebra.pthRootAlgebra n r C t) ∧
    IsDomain (Algebra.pthRootAlgebra n r C t) ∧
    (∀ (q : Ideal (Algebra.pthRootAlgebra n r C t)) [q.IsMaximal],
      (∀ i, parameterRootCoordinate t n i ∈ q) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime q)
        (List.ofFn (fun i ↦ algebraMap _ (Localization.AtPrime q)
          (parameterRootCoordinate t n i))) ∧
      (∃ e : (Localization.AtPrime q ⧸ Ideal.span (Set.range
          (fun i ↦ algebraMap _ (Localization.AtPrime q) (parameterRootCoordinate t n i)))) ≃+*
          (Localization.AtPrime (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t))) ⧸
            Ideal.map (algebraMap C (Localization.AtPrime
              (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t)))))
              (Ideal.span (Set.range t))),
        ∀ a : C, e (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime q)
          (algebraMap C (Algebra.pthRootAlgebra n r C t) a))) =
          Ideal.Quotient.mk _ (algebraMap C (Localization.AtPrime
            (q.comap (algebraMap C (Algebra.pthRootAlgebra n r C t)))) a))) ∧
    IsDomain C ∧ (∏ i, t i) ≠ 0 ∧
    algebraMap C (Algebra.pthRootAlgebra n r C t) (∏ i, t i) ≠ 0 := by
  classical
  let B := Algebra.pthRootAlgebra n r C t
  let J := Ideal.span (Set.range t)
  have : ConnectedSpace (Spec (.of (C ⧸ J))) := hconnected
  have : Nontrivial (C ⧸ J) := PrimeSpectrum.nonempty_iff_nontrivial.mp
    (show Nonempty (Spec (.of (C ⧸ J))) from hconnected.toNonempty)
  have : Nontrivial C := (Ideal.Quotient.mk_surjective (I := J)).nontrivial
  obtain ⟨b, hb⟩ := Algebra.ParameterRoot.exists_basis t n hn
  have : Module.Finite C B := Module.Finite.of_basis b
  have : Module.Free C B := Module.Free.of_basis b
  have : IsNoetherianRing B := IsNoetherianRing.of_finite C B
  have : Module.FaithfullyFlat C B := (Algebra.ParameterRoot.finite_faithfullyFlat t n hn).2
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have : Nontrivial B := hinj.nontrivial
  have hroots (q : Ideal B) [q.IsMaximal] :
      ∀ i, parameterRootCoordinate t n i ∈ q := by
    let m := q.comap (algebraMap C B)
    have : m.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
    have hJ : J ≤ m := HenselianRing.jac.trans (sInf_le ⟨bot_le, inferInstance⟩)
    intro i
    apply Ideal.IsPrime.mem_of_pow_mem (inferInstance : q.IsPrime) n
    change Algebra.ParameterRoot.root t n i ^ n ∈ q
    rw [Algebra.ParameterRoot.root_pow t n i]
    exact hJ (Ideal.subset_span ⟨i, rfl⟩)
  have hloc (q : Ideal B) [q.IsMaximal] := by
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := C) q
    have := (hlocal (q.comap (algebraMap C B))).2
    exact rootLocal_regular t n hn q (hroots q) (hlocal _).1
  have : IsRegularRing B := regular_of_maximals (fun q _ ↦ (hloc q).2)
  have : IsDomain B := domain_of_regular_idempotents (root_idempotents t hconnected n hn)
  have : IsDomain C := Function.Injective.isDomain (algebraMap C B) hinj
  have hprod : (∏ i, t i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hz
    obtain ⟨m, hm⟩ := Ideal.exists_maximal C
    have := hm
    let A := Localization.AtPrime m
    have hmem : algebraMap C A (t i) ∈ List.ofFn (fun i ↦ algebraMap C A (t i)) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    have H := IsLocalRing.isRegular_of_perm (hlocal m).1 (List.perm_cons_erase hmem)
    have hreg := ((RingTheory.Sequence.isRegular_cons_iff A _ _).mp H).1
    exact one_ne_zero (hreg (by simp [hz]))
  refine ⟨⟨b, hb⟩, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    inferInstance, hprod, fun hz ↦ hprod (hinj (hz.trans (map_zero _).symm))⟩
  intro q _
  exact ⟨hroots q, (hloc q).1, rootLocalQuotientEquiv t n hn q (hroots q),
    rootLocalQuotientEquiv_coeff t n hn q (hroots q)⟩


private def rootCocone_isColimit {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) {r : ℕ} (t : ∀ j, Fin r → F.obj j)
    (ht : ∀ {j k} (a : j ⟶ k) i, (F.map a).hom (t j i) = t k i)
    (c : Cocone F) (hc : IsColimit c) (s : Fin r → c.pt)
    (hs : ∀ j i, (c.ι.app j).hom (t j i) = s i) (n : ℕ) :
    IsColimit (parameterRootCocone F t ht c s hs n) := by
  classical
  let j₀ : I := Classical.choice (IsFiltered.nonempty : Nonempty I)
  have hcoeff (d : Cocone (parameterRootDiagram F t ht n)) :
      ∀ {j k} (a : j ⟶ k),
        ((d.ι.app k).hom.comp (algebraMap (F.obj k)
          (Algebra.pthRootAlgebra n r (F.obj k) (t k)))).comp (F.map a).hom =
          (d.ι.app j).hom.comp (algebraMap (F.obj j)
            (Algebra.pthRootAlgebra n r (F.obj j) (t j))) := by
    intro j k a
    ext b
    have he := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (d.w a))
      (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j)) b)
    change (d.ι.app k).hom (parameterRootMap (t j) (t k) n (F.map a).hom (ht a)
      (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j)) b)) =
        (d.ι.app j).hom (algebraMap (F.obj j)
          (Algebra.pthRootAlgebra n r (F.obj j) (t j)) b) at he
    simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply] at he
    convert! he using 1
  let coeff (d : Cocone (parameterRootDiagram F t ht n)) : Cocone F :=
    { pt := d.pt
      ι := { app j := CommRingCat.ofHom ((d.ι.app j).hom.comp
               (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j))))
             naturality j k a := by
               apply CommRingCat.hom_ext
               exact hcoeff d a } }
  let g (d : Cocone (parameterRootDiagram F t ht n)) : c.pt →+* d.pt :=
    (hc.desc (coeff d)).hom
  have hg (d : Cocone (parameterRootDiagram F t ht n)) (j : I) (b : F.obj j) :
      g d ((c.ι.app j).hom b) = (d.ι.app j).hom
        (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j)) b) :=
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hc.fac (coeff d) j)) b
  let x (d : Cocone (parameterRootDiagram F t ht n)) (i : Fin r) :=
    (d.ι.app j₀).hom (parameterRootCoordinate (t j₀) n i)
  have hxj (d : Cocone (parameterRootDiagram F t ht n)) (j : I) (i : Fin r) :
      (d.ι.app j).hom (parameterRootCoordinate (t j) n i) = x d i := by
    have he {a b : I} (f : a ⟶ b) :
        (d.ι.app b).hom (parameterRootCoordinate (t b) n i) =
          (d.ι.app a).hom (parameterRootCoordinate (t a) n i) := by
      have H := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (d.w f))
        (parameterRootCoordinate (t a) n i)
      change (d.ι.app b).hom (parameterRootMap (t a) (t b) n (F.map f).hom (ht f)
        (parameterRootCoordinate (t a) n i)) =
          (d.ι.app a).hom (parameterRootCoordinate (t a) n i) at H
      simpa only [parameterRootMap, parameterRootLift_root] using H
    exact (he (IsFiltered.leftToMax j j₀)).symm.trans (he (IsFiltered.rightToMax j j₀))
  have hx (d : Cocone (parameterRootDiagram F t ht n)) (i : Fin r) :
      x d i ^ n = g d (s i) := by
    rw [← hs j₀ i, hg]
    change ((d.ι.app j₀).hom (parameterRootCoordinate (t j₀) n i)) ^ n = _
    rw [← map_pow]
    congr 1
    exact Algebra.ParameterRoot.root_pow (t j₀) n i
  let desc (d : Cocone (parameterRootDiagram F t ht n)) :=
    CommRingCat.ofHom (parameterRootLift s n (g d) (x d) (hx d))
  have hfac (d : Cocone (parameterRootDiagram F t ht n)) (j : I) :
      (parameterRootCocone F t ht c s hs n).ι.app j ≫ desc d = d.ι.app j := by
    apply CommRingCat.hom_ext
    apply Algebra.ParameterRoot.ringHom_ext (t j) n
    · ext a
      change parameterRootLift s n (g d) (x d) (hx d)
        (parameterRootMap (t j) s n (c.ι.app j).hom (hs j)
          (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j)) a)) = _
      simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply]
      exact hg d j a
    · intro i
      change parameterRootLift s n (g d) (x d) (hx d)
        (parameterRootMap (t j) s n (c.ι.app j).hom (hs j)
          (parameterRootCoordinate (t j) n i)) = _
      simp only [parameterRootMap, parameterRootLift_root]
      exact (hxj d j i).symm
  refine ⟨desc, hfac, ?_⟩
  intro d m hm
  apply CommRingCat.hom_ext
  apply Algebra.ParameterRoot.ringHom_ext s n
  · have he : CommRingCat.ofHom (m.hom.comp (algebraMap c.pt (Algebra.pthRootAlgebra n r c.pt s))) =
        hc.desc (coeff d) := by
      apply hc.hom_ext
      intro j
      apply CommRingCat.hom_ext
      ext a
      have H := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hm j))
        (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j)) a)
      change m.hom (parameterRootMap (t j) s n (c.ι.app j).hom (hs j)
        (algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j)) a)) =
          (d.ι.app j).hom (algebraMap (F.obj j)
            (Algebra.pthRootAlgebra n r (F.obj j) (t j)) a) at H
      rw [hc.fac]
      change m.hom (algebraMap c.pt (Algebra.pthRootAlgebra n r c.pt s)
        ((c.ι.app j).hom a)) =
          (d.ι.app j).hom (algebraMap (F.obj j)
            (Algebra.pthRootAlgebra n r (F.obj j) (t j)) a)
      simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply] at H
      convert! H using 1
    ext a
    change m.hom (algebraMap c.pt (Algebra.pthRootAlgebra n r c.pt s) a) =
      parameterRootLift s n (g d) (x d) (hx d)
        (algebraMap c.pt (Algebra.pthRootAlgebra n r c.pt s) a)
    rw [parameterRootLift_coeff]
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he) a
  · intro i
    have H := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hm j₀))
      (parameterRootCoordinate (t j₀) n i)
    change m.hom (parameterRootMap (t j₀) s n (c.ι.app j₀).hom (hs j₀)
      (parameterRootCoordinate (t j₀) n i)) = _ at H
    change m.hom (parameterRootCoordinate s n i) =
      parameterRootLift s n (g d) (x d) (hx d)
        (parameterRootCoordinate s n i)
    rw [parameterRootLift_root]
    simp only [parameterRootMap, parameterRootLift_root] at H
    exact H.trans (hxj d j₀ i)

private theorem filteredNonzero {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (a : ∀ j, F.obj j) (ha : ∀ {j k} (f : j ⟶ k), (F.map f).hom (a j) = a k)
    (hne : ∀ j, a j ≠ 0) (z : c.pt) (hz : ∀ j, (c.ι.app j).hom (a j) = z) :
    z ≠ 0 := by
  obtain ⟨j⟩ := (IsFiltered.nonempty : Nonempty I)
  intro he
  have he' : (c.ι.app j).hom (a j) = (c.ι.app j).hom 0 := by rw [hz, he, map_zero]
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ he'
  exact hne k (by simpa only [ha, map_zero] using hfg)

private theorem fullRoot_domain {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (p : ℕ) (hp : p = 1 ∨ p.Prime)
    (hd : ∀ n : ℕ, 0 < n → IsDomain (Algebra.pthRootAlgebra n r R t))
    (a : R) (ha : ∀ n : ℕ, 0 < n →
      algebraMap R (Algebra.pthRootAlgebra n r R t) a ≠ 0) :
    IsDomain (tameRootAlgebra p t) ∧ algebraMap R (tameRootAlgebra p t) a ≠ 0 := by
  classical
  have _ := hp
  let J := ULift.{u} (Algebra.ParameterRoot.DirectedIndex p)
  let order (j : J) := j.down.order
  let D : J ⥤ CommRingCat.{u} :=
    { obj j := .of (Algebra.pthRootAlgebra (order j).val r R t)
      map {j k} f := CommRingCat.ofHom
        (Algebra.ParameterRoot.transition t _ _ (leOfHom f)).toRingHom
      map_id j := by
        apply CommRingCat.hom_ext
        exact congrArg AlgHom.toRingHom
          (Algebra.ParameterRoot.transition_self t _ (order j).property.1)
      map_comp {j k l} f g := by
        apply CommRingCat.hom_ext
        exact (congrArg AlgHom.toRingHom
          (Algebra.ParameterRoot.transition_comp t _ _ _ (leOfHom f) (leOfHom g))).symm }
  let c : Cocone D :=
    { pt := .of (tameRootAlgebra p t)
      ι := { app j := CommRingCat.ofHom
               (Algebra.ParameterRoot.inclusion t p (order j)).toRingHom
             naturality j k f := by
               apply CommRingCat.hom_ext
               exact congrArg AlgHom.toRingHom
                 (Algebra.ParameterRoot.inclusion_comp t p (order j) (order k) (leOfHom f)) } }
  let index (n : TameRootOrder p) : J := ⟨⟨n⟩⟩
  have hex (d : Cocone D) : ∃! g : tameRootAlgebra p t →+* d.pt,
      ∀ j, g.comp (Algebra.ParameterRoot.inclusion t p (order j)).toRingHom =
        (d.ι.app j).hom := by
    obtain ⟨g, hg, hu⟩ := Algebra.ParameterRoot.full_isColimit t p (S := d.pt)
      (fun n ↦ show Algebra.ParameterRoot.Ring t n.val →+* d.pt from
        (d.ι.app (index n)).hom) (by
        intro n m h
        have H := congrArg CommRingCat.Hom.hom
          (d.w (homOfLE h : index n ⟶ index m))
        change (d.ι.app (index m)).hom.comp
          (Algebra.ParameterRoot.transition t n.val m.val h).toRingHom =
            (d.ι.app (index n)).hom at H
        exact H)
    refine ⟨g, ?_, ?_⟩
    · intro j
      exact hg (order j)
    · intro g' hg'
      exact hu g' (fun n ↦ hg' (index n))
  have hc : IsColimit c :=
    { desc d := CommRingCat.ofHom (hex d).exists.choose
      fac d j := by
        apply CommRingCat.hom_ext
        exact (hex d).exists.choose_spec j
      uniq d m hm := by
        apply CommRingCat.hom_ext
        exact (hex d).unique (fun j ↦ congrArg CommRingCat.Hom.hom (hm j))
          (hex d).exists.choose_spec }
  refine ⟨CommRingCat.isDomain_of_filtered_colimit_cocone D c hc
    (fun j ↦ hd _ (order j).property.1) rfl, ?_⟩
  apply filteredNonzero D c hc
    (fun j ↦ algebraMap R (Algebra.pthRootAlgebra (order j).val r R t) a)
  · intro j k f
    exact (Algebra.ParameterRoot.transition t _ _ (leOfHom f)).commutes a
  · exact fun j ↦ ha _ (order j).property.1
  · intro j
    exact (Algebra.ParameterRoot.inclusion t p (order j)).commutes a

/-- Finite roots commute with the filtered coefficient colimit; all resulting rings
and both choices of full root tower are nonzero domains with nonzero parameter product.
Source: ILO IX 2.1, agent extension using Stacks 04AX
(blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof:
8. Represent elements and equalities at common stages by
filtered-colimit-commrings-elementwise. A zero product then has a zero factor at a
domain stage; 1=0 and vanishing of the labelled product would hold at a later
stage, contradicting the finite-pair result. No transition injectivity is used.
9. Compatible maps out of the root quotients are exactly a map out of the
coefficient colimit and the labelled roots satisfying their equations. This proves
that parameterRootCocone is colimiting, so its vertex is colim K_(lambda,n).
The common-stage argument proves its domain and nonvanishing assertions.
10. Positive orders, and orders prime to a fixed prime, are directed by their
product and contain 1. The canonical power transitions and full universal property
above identify the full quotient with this filtered colimit. Apply the same
common-stage argument to preserve domains and the parameter product. -/
theorem henselianParameterRoot_filtered {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) {r : ℕ} (t : ∀ j, Fin r → F.obj j)
    (ht : ∀ {j k} (a : j ⟶ k) i, (F.map a).hom (t j i) = t k i)
    (hpair : ∀ j, IsNoetherianRing (F.obj j) ∧
      HenselianRing (F.obj j) (Ideal.span (Set.range (t j))) ∧
      ConnectedSpace (Spec (.of (F.obj j ⧸ Ideal.span (Set.range (t j))))) ∧
      ∀ (m : Ideal (F.obj j)) [m.IsMaximal],
        RingTheory.Sequence.IsRegular (Localization.AtPrime m)
          (List.ofFn (fun i ↦ algebraMap (F.obj j) (Localization.AtPrime m) (t j i))) ∧
        IsRegularLocalRing (Localization.AtPrime m ⧸
          Ideal.map (algebraMap (F.obj j) (Localization.AtPrime m))
            (Ideal.span (Set.range (t j)))))
    (c : Cocone F) (hc : IsColimit c) (s : Fin r → c.pt)
    (hs : ∀ j i, (c.ι.app j).hom (t j i) = s i) :
    IsDomain c.pt ∧ (∏ i, s i) ≠ 0 ∧
    (∀ n : ℕ, 0 < n →
      Nonempty (IsColimit (parameterRootCocone F t ht c s hs n)) ∧
      IsDomain (Algebra.pthRootAlgebra n r c.pt s) ∧
      algebraMap c.pt (Algebra.pthRootAlgebra n r c.pt s) (∏ i, s i) ≠ 0) ∧
    (∀ p : ℕ, p = 1 ∨ p.Prime →
      IsDomain (tameRootAlgebra p s) ∧
      algebraMap c.pt (tameRootAlgebra p s) (∏ i, s i) ≠ 0) := by
  classical
  have hfinite (j : I) (n : ℕ) (hn : 0 < n) := by
    have := (hpair j).1
    have := (hpair j).2.1
    exact henselianParameterRoot_finite (t j) (hpair j).2.2.1 (hpair j).2.2.2 n hn
  have hd : IsDomain c.pt := CommRingCat.isDomain_of_filtered_colimit_cocone F c hc
    (fun j ↦ (hfinite j 1 (by omega)).2.2.2.2.2.2.1) rfl
  have hsprod (j : I) : (c.ι.app j).hom (∏ i, t j i) = ∏ i, s i := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ ↦ hs j i)
  have hnonzero : (∏ i, s i) ≠ 0 := by
    apply filteredNonzero F c hc (fun j ↦ ∏ i, t j i)
    · intro j k a
      simp [map_prod, ht]
    · intro j
      exact (hfinite j 1 (by omega)).2.2.2.2.2.2.2.1
    · exact hsprod
  have hroots (n : ℕ) (hn : 0 < n) :
      Nonempty (IsColimit (parameterRootCocone F t ht c s hs n)) ∧
      IsDomain (Algebra.pthRootAlgebra n r c.pt s) ∧
      algebraMap c.pt (Algebra.pthRootAlgebra n r c.pt s) (∏ i, s i) ≠ 0 := by
    let D := parameterRootDiagram F t ht n
    let q := parameterRootCocone F t ht c s hs n
    have hq : IsColimit q := rootCocone_isColimit F t ht c hc s hs n
    refine ⟨⟨hq⟩, CommRingCat.isDomain_of_filtered_colimit_cocone D q hq
      (fun j ↦ (hfinite j n hn).2.2.2.2.1) rfl, ?_⟩
    apply filteredNonzero D q hq
      (fun j ↦ algebraMap (F.obj j) (Algebra.pthRootAlgebra n r (F.obj j) (t j))
        (∏ i, t j i))
    · intro j k a
      change parameterRootMap (t j) (t k) n (F.map a).hom (ht a)
        (algebraMap (F.obj j) _ (∏ i, t j i)) = _
      simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply, map_prod, ht]
    · intro j
      exact (hfinite j n hn).2.2.2.2.2.2.2.2
    · intro j
      change parameterRootMap (t j) s n (c.ι.app j).hom (hs j)
        (algebraMap (F.obj j) _ (∏ i, t j i)) = _
      simp only [parameterRootMap, parameterRootLift_coeff, RingHom.comp_apply]
      exact congrArg (algebraMap c.pt _) (hsprod j)
  exact ⟨hd, hnonzero, hroots, fun p hp ↦ fullRoot_domain s p hp
    (fun n hn ↦ (hroots n hn).2.1) (∏ i, s i) (fun n hn ↦ (hroots n hn).2.2)⟩

/-- The separate local-ring assertion needs henselianness only at the maximal ideal,
not at the ideal generated by the chosen partial parameter list.
Source: ILO IX 2.1 and Stacks 00NQ
(blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: extend the list to a full regular system of parameters. Apply
henselian-parameter-root-regularity at each finite order: these are henselian
regular local domains and the coefficient maps are injective. Apply
regular-local-generators-regular-sequence to see that the product of the chosen
parameters is nonzero. The common-stage domain and nonvanishing argument applies
to the divisibility colimit of these finite levels, over either set of orders.
This argument uses the maximal-ideal henselian pair throughout. -/
theorem henselianParameterRoot_local {R : Type u} [CommRing R]
    [HenselianLocalRing R] [IsRegularLocalRing R] {r : ℕ} (t : Fin r → R)
    (ht : ∃ rest : List R, IsLocalRing.IsRegularSystemOfParameters (List.ofFn t ++ rest)) :
    IsDomain R ∧ (∏ i, t i) ≠ 0 ∧
    (∀ n : ℕ, 0 < n → IsDomain (Algebra.pthRootAlgebra n r R t) ∧
      algebraMap R (Algebra.pthRootAlgebra n r R t) (∏ i, t i) ≠ 0) ∧
    (∀ p : ℕ, p = 1 ∨ p.Prime → IsDomain (tameRootAlgebra p t) ∧
      algebraMap R (tameRootAlgebra p t) (∏ i, t i) ≠ 0) := by
  classical
  obtain ⟨tail, ht⟩ := ht
  have hdom : IsDomain R := IsRegularLocalRing.isDomain R
  have hnonzero : (∏ i, t i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hi : t i ∈ List.ofFn t ++ tail := List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have hp := (IsRegularLocalRing.isRegular_and_quotients_of_generators R
      (List.ofFn t ++ tail).length ht.2.symm _ ht).2.2 _ (List.perm_cons_erase hi)
    have hreg := (RingTheory.Sequence.isRegular_cons_iff R (t i) _).mp hp.2 |>.1
    intro hz
    have h10 : (1 : R) = 0 := hreg (by simp [hz])
    exact one_ne_zero h10
  have hroots (n : ℕ) (hn : 0 < n) :
      IsDomain (Algebra.pthRootAlgebra n r R t) ∧
      algebraMap R (Algebra.pthRootAlgebra n r R t) (∏ i, t i) ≠ 0 := by
    let ts := List.ofFn t ++ tail
    let d := ts.length
    let v : Fin d → R := ts.get
    have hv : List.ofFn v = ts := List.ofFn_get ts
    have hr : r ≤ d := by simp [d, ts]
    have he : v ∘ Fin.castLE hr = t := by
      funext i
      simp [v, ts, List.get_eq_getElem]
    have ht' : IsLocalRing.IsRegularSystemOfParameters (List.ofFn v) := by
      rw [hv]
      exact ht
    obtain ⟨b, hb, hfin, hinj, hint, hreg, hhen, hrest⟩ :=
      Algebra.henselian_parameter_root_regularity R d v ht' r hr n hn
    rw [he] at hinj hreg
    let := hreg
    exact ⟨IsRegularLocalRing.isDomain _, fun hz ↦ hnonzero (hinj (hz.trans (map_zero _).symm))⟩
  exact ⟨hdom, hnonzero, hroots, fun p hp ↦ fullRoot_domain t p hp
    (fun n hn ↦ (hroots n hn).1) (∏ i, t i) (fun n hn ↦ (hroots n hn).2)⟩

/-- Every ring above and its puncture have nonempty connected qcqs spectra.
ConnectedSpace includes nonemptiness. Apply this to C, K_n, H, H_n and H_infinity,
using the domain and nonvanishing conclusions above, and to the separate local case.
Source: Stacks 00CM, 00E8, 01KN and 01KO
(blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: localization at nonzero f in a domain is a nonzero domain by the fraction
zero criterion. The zero prime is a dense point of the spectrum of a domain, so
that spectrum is nonempty irreducible and hence connected. Both spectra are affine,
hence quasi-compact and quasi-separated (affine-scheme-qcqs). -/
theorem henselianParameterRoot_spectra (R : Type u) [CommRing R] [IsDomain R]
    (f : R) (hf : f ≠ 0) :
    IsDomain (Localization.Away f) ∧
    ConnectedSpace (Spec (.of R)) ∧ CompactSpace (Spec (.of R)) ∧
    QuasiSeparatedSpace (Spec (.of R)) ∧
    ConnectedSpace (Spec (.of (Localization.Away f))) ∧
    CompactSpace (Spec (.of (Localization.Away f))) ∧
    QuasiSeparatedSpace (Spec (.of (Localization.Away f))) := by
  have hdom : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  refine ⟨hdom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IrreducibleSpace.connectedSpace _
  · exact Scheme.compactSpace_of_isAffine _
  · exact AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _
  · exact IrreducibleSpace.connectedSpace _
  · exact Scheme.compactSpace_of_isAffine _
  · exact AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _

/-- Order one and the empty parameter tuple give exactly the base ring canonically.
Source: ILO IX 2.1 (blueprint: lem-sfb-henselian-parameter-root-domain-tower).
Proof: at order one substitute X_i=t_i, giving inverse maps to the coefficient map.
For the empty tuple there are no variables or relations, at finite or full level;
the empty product is 1. These constructions are inverse to the coefficient maps. -/
theorem henselianParameterRoot_degenerate {R : Type u} [CommRing R]
    {r : ℕ} (t : Fin r → R) :
    Function.Bijective (algebraMap R (Algebra.pthRootAlgebra 1 r R t)) ∧
    (r = 0 → (∏ i, t i) = 1 ∧
      (∀ n : ℕ, 0 < n →
        Function.Bijective (algebraMap R (Algebra.pthRootAlgebra n r R t))) ∧
      ∀ p : ℕ, p = 1 ∨ p.Prime →
        Function.Bijective (algebraMap R (tameRootAlgebra p t))) := by
  refine ⟨?_, ?_⟩
  · exact (Algebra.ParameterRoot.oneEquiv t).symm.bijective
  · intro hr
    subst r
    refine ⟨by simp, ?_, ?_⟩
    · intro n hn
      exact (Algebra.ParameterRoot.emptyEquiv n t).symm.bijective
    · intro p hp
      exact Algebra.ParameterRoot.full_empty_bijective p t

end RingTheory
