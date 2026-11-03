/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.ZetaSeries

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
  ((geometricFrobeniusGeometry F Y₀).b.pow i).inv ≫
    (z ≫ ((geometricFrobeniusGeometry F Y₀).h.pow i).hom)

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
      (z ≫ ((geometricFrobeniusGeometry F Y₀).h.pow i).hom)
      ((geometricFrobeniusGeometry F Y₀).b.pow i).inv).symm.app K.carrier.obj ≪≫
    (Γ (finiteCoefficient ell E n) (Spec (.of F.k))).mapIso
      ((leftDerivedUpperStarComp (finiteCoefficient ell E n) z
        ((geometricFrobeniusGeometry F Y₀).h.pow i).hom).app K.carrier.obj) ≪≫
    (localFrobeniusFibre F Y₀ ell E n z).mapIso (iteratedWeil F Y₀ ell E n hn K i)

/-- The owning local operator in the coordinates of an equal chosen geometric lift.
This changes only equality coordinates; the operator is exactly condensedLocalFrobenius.
Source: clause 3, identifying bar(y_i) with z_i
(blueprint: lem-trf-local-frobenius-conjugacy). -/
def localFrobeniusAtLift (hEll : ell ≠ F.p)
    (K : FiniteStrictWeilComplex F Y₀ ell E n hn) (m : ℕ) (hm : 1 ≤ m)
    (y : F.extensionPoints Y₀ m hm)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (hy : localExtensionPoint F Y₀ m hm y = z) :
    End ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj) :=
  let e := eqToIso (congrArg
    (fun w ↦ (localFrobeniusFibre F Y₀ ell E n w).obj K.carrier.obj) hy)
  e.inv ≫ condensedLocalFrobenius F Y₀ ell hEll E n hn m hm ⟨y⟩ K ≫ e.hom

/-- All clauses of local Frobenius conjugacy, on the native condensed finite coefficient
category and on literal point-fibre complexes.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-c-proper-global/
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
          localExtensionPoint F Y₀ m hm y = localFrobeniusOrbit F Y₀ z i) ∧
      HEq (localFrobeniusTransport F Y₀ ell E n hn K z 0).hom
        (𝟙 ((localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj)) ∧
      (∀ i j : ℕ,
        HEq (localFrobeniusTransport F Y₀ ell E n hn K z (i + j)).hom
          ((localFrobeniusTransport F Y₀ ell E n hn K (localFrobeniusOrbit F Y₀ z i) j).hom ≫
            (localFrobeniusTransport F Y₀ ell E n hn K z i).hom)) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        (localFrobeniusOrbit F Y₀ z i) ≫ F.schemeFrobeniusIterate Y₀ m =
          localFrobeniusOrbit F Y₀ z i) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m → ∀ i : ℕ,
        ∀ (y₀ yᵢ : F.extensionPoints Y₀ m hm)
          (hy₀ : localExtensionPoint F Y₀ m hm y₀ = z)
          (hyᵢ : localExtensionPoint F Y₀ m hm yᵢ = localFrobeniusOrbit F Y₀ z i),
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
          (hy₀ : localExtensionPoint F Y₀ _ hd y₀ = z)
          (hy₁ : localExtensionPoint F Y₀ _ hd y₁ = w),
        ∃ e : (localFrobeniusFibre F Y₀ ell E n w).obj K.carrier.obj ≅
            (localFrobeniusFibre F Y₀ ell E n z).obj K.carrier.obj,
          localFrobeniusAtLift F Y₀ ell E n hn hEll K _ hd y₁ w hy₁ = e.hom ≫
            localFrobeniusAtLift F Y₀ ell E n hn hEll K _ hd y₀ z hy₀ ≫ e.inv) := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
