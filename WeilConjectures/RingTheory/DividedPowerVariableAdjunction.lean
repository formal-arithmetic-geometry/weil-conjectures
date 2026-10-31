/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.GradedDividedPowers
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Data.Finset.Card

/-!
# Adjoining exterior and divided-power variables

Source: Stacks Project, Tags 09PH, 09PI and 0F4I, in `dpa.tex`, section Tate resolutions.
(blueprint: lem-sfb-divided-power-variable-adjunction)

The presentation structures record actual free-module coordinates, multiplication and grading.
They package the constructions asserted by the theorem; no algebra is selected from an existence
proof. Divided powers always mean the recorded `GradedAlgebra.GradedDividedPowers`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v₁ v₂ v₃

namespace GradedAlgebra
namespace VariableAdjunction

/-- An algebra with its nonnegative strict grading, packaged for towers of adjunctions.
Source: Stacks, 09PF and 09PH--0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure AlgebraData (R : Type u) [CommRing R] where
  Carrier : Type v
  [ring : Ring Carrier]
  [algebra : Algebra R Carrier]
  grade : ℕ → Submodule R Carrier
  [graded : GradedAlgebra grade]
  [strict : IsStrictlyGradedCommutative grade]

attribute [instance] AlgebraData.ring AlgebraData.algebra AlgebraData.graded AlgebraData.strict

/-- A graded algebra map between presentation algebras.
Source: Stacks, 09PH--0F4I, inclusions and comparison maps.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure Hom {R : Type u} [CommRing R] (A : AlgebraData.{u, v₁} R)
    (B : AlgebraData.{u, v₂} R) where
  toAlgHom : A.Carrier →ₐ[R] B.Carrier
  homogeneous : ∀ (m : ℕ) (x : A.Carrier), x ∈ A.grade m → toAlgHom x ∈ B.grade m

/-- Preservation of divided powers, tested on the positive even ideal.
The equality specifying `y` identifies its even-subalgebra value without choosing a lift.
Source: Stacks, 09PG and the compatibility requirements in 09PH--0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
def Preserves {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {B : AlgebraData.{u, v₂} R} (f : Hom A B)
    (γ : GradedDividedPowers A.grade) (δ : GradedDividedPowers B.grade) : Prop :=
  ∀ (n : ℕ) (x : evenSubalgebra A.grade) (y : evenSubalgebra B.grade),
    x ∈ positiveEvenIdeal A.grade → (y : B.Carrier) = f.toAlgHom (x : A.Carrier) →
      (δ.dpow n y : B.Carrier) = f.toAlgHom (γ.dpow n x : A.Carrier)

/-- Coordinates for the odd-variable construction `A ⊕ AT`.
Multiplication is specified with a homogeneous right constant coefficient, which determines
all products by bilinearity and the direct-sum grading. Negative components are zero.
Source: Stacks, 09PH.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure OddPresentation {R : Type u} [CommRing R] (A : AlgebraData.{u, v₁} R)
    (B : AlgebraData.{u, v₂} R) (e : ℕ) where
  coordinates : B.Carrier ≃ₗ[R] A.Carrier × A.Carrier
  inclusion : Hom A B
  inclusion_coordinates : ∀ x : A.Carrier, coordinates (inclusion.toAlgHom x) = (x, 0)
  unit_coordinates : coordinates 1 = (1, 0)
  multiplication : ∀ (j : ℕ) (a b c d : A.Carrier), c ∈ A.grade j →
    coordinates (coordinates.symm (a, b) * coordinates.symm (c, d)) =
      (a * c, a * d + (-1 : A.Carrier) ^ j * (b * c))
  grading : ∀ (m : ℕ) (z : B.Carrier), z ∈ B.grade m ↔
    (coordinates z).1 ∈ A.grade m ∧
      (coordinates z).2 ∈ integerComponent A.grade ((m : ℤ) - e)

/-- Coordinates for the even-variable construction, free on the divided monomials.
The binomial coefficient is a natural-number multiple, so no division is used in the ring.
Source: Stacks, 09PI, with the iterate coefficient required by 09PG(7).
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure EvenPresentation {R : Type u} [CommRing R] (A : AlgebraData.{u, v₁} R)
    (B : AlgebraData.{u, v₂} R) (e : ℕ) where
  coordinates : B.Carrier ≃ₗ[R] (ℕ →₀ A.Carrier)
  inclusion : Hom A B
  inclusion_coordinates : ∀ x : A.Carrier,
    coordinates (inclusion.toAlgHom x) = Finsupp.single 0 x
  unit_coordinates : coordinates 1 = Finsupp.single 0 1
  multiplication : ∀ (a a' : ℕ) (b c : A.Carrier),
    coordinates (coordinates.symm (Finsupp.single a b) *
      coordinates.symm (Finsupp.single a' c)) =
        Finsupp.single (a + a') (Nat.choose (a + a') a • (b * c))
  grading : ∀ (m : ℕ) (z : B.Carrier), z ∈ B.grade m ↔
    ∀ a : ℕ, coordinates z a ∈ integerComponent A.grade ((m : ℤ) - (a * e : ℕ))

/-- The prescribed powers of the new even generator. `y` is exactly the corresponding
basis monomial as an element of the even subalgebra.
Source: Stacks, 09PI and 09PG(7).
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
def EvenNormalized {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {B : AlgebraData.{u, v₂} R} {e : ℕ} (p : EvenPresentation A B e)
    (δ : GradedDividedPowers B.grade) : Prop :=
  ∀ (a : ℕ) (t : evenSubalgebra B.grade), 0 < a →
    (t : B.Carrier) = p.coordinates.symm (Finsupp.single 1 1) →
      (δ.dpow a t : B.Carrier) = p.coordinates.symm (Finsupp.single a 1)

/-- Adjoining one odd variable gives the specified algebra and its unique extension of
all divided powers, with the explicit formula on an arbitrary positive even element.
Source: Stacks, 09PH.
(blueprint: lem-sfb-divided-power-variable-adjunction).

Proof: The signed multiplication on pairs is associative, with unit (1,0), and has the
stated grading and odd squares zero. Its even ring is the split square-zero extension
C ⊕ OT, where C is the even ring of A and O is its odd part. Apply
`lem-sfb-split-square-zero-divided-powers` to its ideal I ⊕ OT. It gives the displayed
formula. Degree bookkeeping proves homogeneity. For the extra odd-product axiom, use
homogeneous old odd elements and T as generators of the odd part. Higher powers of
products of two generators vanish. Expand first one odd factor, then the other: cross
products share an odd factor and vanish because every odd element squares to zero.
The addition formula then proves vanishing for arbitrary odd products. The same odd-product
axiom forces higher powers of yT to vanish; the addition formula forces the asserted formula
for every extension, proving uniqueness. -/
theorem odd_variable (R : Type u) [CommRing R] (A : AlgebraData.{u, v} R)
    (γ : GradedDividedPowers A.grade) (e : ℕ) (he : 0 < e) (heodd : Odd e) :
    ∃ (B : AlgebraData.{u, v} R) (p : OddPresentation A B e)
      (δ : GradedDividedPowers B.grade),
      Preserves p.inclusion γ δ ∧
      (∀ δ' : GradedDividedPowers B.grade, Preserves p.inclusion γ δ' → δ' = δ) ∧
      ∀ (n : ℕ) (x : evenSubalgebra A.grade) (y : A.Carrier)
        (z : evenSubalgebra B.grade), 0 < n → x ∈ positiveEvenIdeal A.grade →
        y ∈ oddPart A.grade → (z : B.Carrier) = p.coordinates.symm ((x : A.Carrier), y) →
          (δ.dpow n z : B.Carrier) =
            p.coordinates.symm ((γ.dpow n x : A.Carrier), (γ.dpow (n - 1) x : A.Carrier) * y)
    := by
  sorry

/-- Adjoining one even variable gives the binomial-multiplication algebra and its unique
normalized divided powers, including the iterate and even-coefficient formulas.
Source: Stacks, 09PI, corrected as required by the iterate axiom 09PG(7).
(blueprint: lem-sfb-divided-power-variable-adjunction).

Proof: Define multiplication on basis monomials using binomial coefficients. Associativity
is the integer multinomial identity; the degree is additive, and signs and vanishing odd
squares follow from those of the coefficients. The even ring is C⟨T⟩ with positive ideal
IC⟨T⟩ + C⟨T⟩₊. Apply `lem-sfb-ordinary-pd-polynomial-extension`. The iterate and scalar
axioms give the two formulas, with coefficient (na)!/(n!(a!)^n). Expand divided powers of
a finite sum by the addition formula: each term has the claimed degree. The old homogeneous
odd generators generate the new odd part over the even ring. Expand the two odd factors
successively; terms sharing an odd factor have zero product, so the addition formula and
the old odd-product axiom give the new odd-product axiom. Ordinary uniqueness gives graded
uniqueness subject to the prescribed divided powers of T. -/
theorem even_variable (R : Type u) [CommRing R] (A : AlgebraData.{u, v} R)
    (γ : GradedDividedPowers A.grade) (e : ℕ) (he : 0 < e) (heeven : Even e) :
    ∃ (B : AlgebraData.{u, v} R) (p : EvenPresentation A B e)
      (δ : GradedDividedPowers B.grade),
      Preserves p.inclusion γ δ ∧ EvenNormalized p δ ∧
      (∀ δ' : GradedDividedPowers B.grade,
        Preserves p.inclusion γ δ' → EvenNormalized p δ' → δ' = δ) ∧
      (∀ (n a : ℕ) (t : evenSubalgebra B.grade), 0 < n → 0 < a →
        (t : B.Carrier) = p.coordinates.symm (Finsupp.single a 1) →
          (δ.dpow n t : B.Carrier) =
            p.coordinates.symm (Finsupp.single (n * a) (Nat.uniformBell n a • (1 : A.Carrier)))) ∧
      ∀ (n a : ℕ) (b : evenSubalgebra A.grade) (t : evenSubalgebra B.grade),
        0 < n → 0 < a →
        (t : B.Carrier) = p.coordinates.symm (Finsupp.single a (b : A.Carrier)) →
          (δ.dpow n t : B.Carrier) =
            p.coordinates.symm
              (Finsupp.single (n * a) (Nat.uniformBell n a • ((b : A.Carrier) ^ n)))
    := by
  sorry

/-- One step of a finite adjunction, carrying the extended divided powers and the generator.
The parity-dependent presentations are data, with precisely the coordinates above.
Source: Stacks, 09PH, 09PI and 0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure Step {R : Type u} [CommRing R] (A : AlgebraData.{u, v₁} R)
    (B : AlgebraData.{u, v₂} R) (γ : GradedDividedPowers A.grade)
    (δ : GradedDividedPowers B.grade) (e : ℕ) where
  inclusion : Hom A B
  generator : B.Carrier
  preserves : Preserves inclusion γ δ
  oddModel : Odd e → OddPresentation A B e
  odd_inclusion : ∀ h : Odd e, (oddModel h).inclusion = inclusion
  odd_variable : ∀ h : Odd e, (oddModel h).coordinates generator = (0, 1)
  evenModel : Even e → EvenPresentation A B e
  even_inclusion : ∀ h : Even e, (evenModel h).inclusion = inclusion
  even_variable : ∀ h : Even e,
    (evenModel h).coordinates generator = Finsupp.single 1 1
  even_normalized : ∀ h : Even e, EvenNormalized (evenModel h) δ

/-- A finite sequence of single-variable adjunctions, with its coherent inclusion maps.
The initial map is an isomorphism onto stage zero, allowing harmless changes of carriers.
Source: Stacks, 0F4I, finite adjunctions in any order.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure FiniteTower {R : Type u} [CommRing R] (A : AlgebraData.{u, v₁} R)
    (γ : GradedDividedPowers A.grade) (e n : ℕ) where
  stage : Fin (n + 1) → AlgebraData.{u, v₂} R
  dp : ∀ i : Fin (n + 1), GradedDividedPowers (stage i).grade
  base : Hom A (stage 0)
  base_bijective : Function.Bijective base.toAlgHom
  base_preserves : Preserves base γ (dp 0)
  transport : ∀ i j : Fin (n + 1), i ≤ j → Hom (stage i) (stage j)
  transport_identity : ∀ (i : Fin (n + 1)) (h : i ≤ i),
    (transport i i h).toAlgHom = AlgHom.id R (stage i).Carrier
  transport_comp : ∀ (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k),
    (transport i k (hij.trans hjk)).toAlgHom =
      (transport j k hjk).toAlgHom.comp (transport i j hij).toAlgHom
  transport_preserves : ∀ (i j : Fin (n + 1)) (h : i ≤ j),
    Preserves (transport i j h) (dp i) (dp j)
  step : ∀ i : Fin n, Step (stage i.castSucc) (stage i.succ)
    (dp i.castSucc) (dp i.succ) e
  transport_step : ∀ (i : Fin n) (h : i.castSucc ≤ i.succ),
    (transport i.castSucc i.succ h).toAlgHom = (step i).inclusion.toAlgHom

/-- The last algebra in a finite adjunction.
Source: Stacks, 0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
def FiniteTower.top {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {γ : GradedDividedPowers A.grade} {e n : ℕ} (F : FiniteTower.{u, v₁, v₂} A γ e n) :
    AlgebraData.{u, v₂} R :=
  F.stage (Fin.last n)

/-- The original coefficient map into the last stage.
Source: Stacks, 0F4I, identification of the coefficient algebra.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
def FiniteTower.coefficients {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {γ : GradedDividedPowers A.grade} {e n : ℕ} (F : FiniteTower.{u, v₁, v₂} A γ e n) :
    A.Carrier →ₐ[R] F.top.Carrier :=
  (F.transport 0 (Fin.last n) (Fin.zero_le _)).toAlgHom.comp F.base.toAlgHom

/-- Each adjoined generator, transported to the last stage.
Source: Stacks, 0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
def FiniteTower.variables {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {γ : GradedDividedPowers A.grade} {e n : ℕ} (F : FiniteTower.{u, v₁, v₂} A γ e n)
    (i : Fin n) : F.top.Carrier :=
  (F.transport i.succ (Fin.last n) (Fin.le_last _)).toAlgHom (F.step i).generator

/-- Divided monomials of one generator, transported to the last stage in the even case.
Source: Stacks, 09PI and 0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
noncomputable def FiniteTower.symbols {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {γ : GradedDividedPowers A.grade} {e n : ℕ} (F : FiniteTower.{u, v₁, v₂} A γ e n)
    (h : Even e) (i : Fin n) (a : ℕ) : F.top.Carrier :=
  (F.transport i.succ (Fin.last n) (Fin.le_last _)).toAlgHom
    (((F.step i).evenModel h).coordinates.symm (Finsupp.single a 1))

/-- The unique comparison between two orders of finite adjunction, fixing coefficients
and the relabelled generators, as a bijective graded divided-power algebra map.
Source: Stacks, 0F4I, with preservation of divided powers in the comparison requirement.
(blueprint: lem-sfb-divided-power-variable-adjunction).

Proof: Assign each old coefficient and each variable to its namesake in the other tower.
For odd variables their square-zero relations and graded signs respect multiplication;
for even variables send each divided symbol to the corresponding divided power. The
binomial identity proves multiplicativity. The odd formula and the finite-sum expansion
from the even case show preservation of divided powers at each step. The reverse assignment
is inverse: both composites fix all coefficient basis monomials. Every divided-power map
fixing a variable fixes all its divided symbols, so induction over the tower and linearity
on the free-module coordinates prove uniqueness. -/
theorem finite_order_comparison (R : Type u) [CommRing R] (A : AlgebraData.{u, v} R)
    (γ : GradedDividedPowers A.grade) (e n : ℕ) (he : 0 < e)
    (F : FiniteTower.{u, v, v₁} A γ e n) (G : FiniteTower.{u, v, v₂} A γ e n)
    (σ : Equiv.Perm (Fin n)) :
    ∃! f : Hom F.top G.top,
      Function.Bijective f.toAlgHom ∧
      Preserves f (F.dp (Fin.last n)) (G.dp (Fin.last n)) ∧
      f.toAlgHom.comp F.coefficients = G.coefficients ∧
      ∀ i : Fin n, f.toAlgHom (F.variables i) = G.variables (σ i) := by
  sorry

/-- A directed union of the finite adjunctions indexed by finite subsets of a set of labels.
The maps are injective, preserve coefficients and labelled generators, and their ranges
increase with the subsets and cover the algebra. The last field specifies the union grading.
Source: Stacks, 0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure SetPresentation {R : Type u} [CommRing R] (A : AlgebraData.{u, v₁} R)
    (γ : GradedDividedPowers A.grade) (e : ℕ) (J : Type w)
    (B : AlgebraData.{u, v₂} R) where
  inclusion : Hom A B
  generator : J → B.Carrier
  symbols : J → ℕ → B.Carrier
  finite : ∀ S : Finset J, FiniteTower.{u, v₁, v₂} A γ e S.card
  labels : ∀ S : Finset J, Fin S.card ≃ {j : J // j ∈ S}
  into : ∀ S : Finset J, Hom (finite S).top B
  injective : ∀ S : Finset J, Function.Injective (into S).toAlgHom
  coefficients : ∀ S : Finset J,
    (into S).toAlgHom.comp (finite S).coefficients = inclusion.toAlgHom
  generators : ∀ (S : Finset J) (i : Fin S.card),
    (into S).toAlgHom ((finite S).variables i) = generator (labels S i).val
  divided_symbols : ∀ (h : Even e) (S : Finset J) (i : Fin S.card) (a : ℕ),
    (into S).toAlgHom ((finite S).symbols h i a) = symbols (labels S i).val a
  increasing : ∀ S T : Finset J, S ⊆ T →
    Set.range (into S).toAlgHom ⊆ Set.range (into T).toAlgHom
  covers : ∀ x : B.Carrier, ∃ (S : Finset J) (y : (finite S).top.Carrier),
    (into S).toAlgHom y = x
  grading : ∀ (m : ℕ) (x : B.Carrier), x ∈ B.grade m ↔
    ∃ (S : Finset J) (y : (finite S).top.Carrier),
      y ∈ (finite S).top.grade m ∧ (into S).toAlgHom y = x

/-- Extension and normalization for a set of generators.
Source: Stacks, 0F4I and 09PI.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
def SetNormalized {R : Type u} [CommRing R] {A : AlgebraData.{u, v₁} R}
    {γ : GradedDividedPowers A.grade} {e : ℕ} {J : Type w}
    {B : AlgebraData.{u, v₂} R} (p : SetPresentation A γ e J B)
    (δ : GradedDividedPowers B.grade) : Prop :=
  Preserves p.inclusion γ δ ∧
    ∀ (_h : Even e) (j : J) (a : ℕ) (t : evenSubalgebra B.grade), 0 < a →
      (t : B.Carrier) = p.generator j → (δ.dpow a t : B.Carrier) = p.symbols j a

/-- An arbitrary, possibly empty, set of variables can be adjoined by the directed union
of finite adjunctions. Its divided powers are uniquely determined by extension and the
even-generator normalization, and agree with every finite stage.
Source: Stacks, 0F4I.
(blueprint: lem-sfb-divided-power-variable-adjunction).

Proof: Induct over the number of finite generators, starting from A. The single-variable
constructions give the successor. The comparison maps of `finite_order_comparison` identify
different orders, and their uniqueness makes these identifications coherent. Inclusions
are injective because coordinates include exactly the monomials with zero new exponent.
Form the free module on finite-support monomials, with odd exponents at most one. Compute
operations in any finite algebra containing the support; coherence makes them independent
of the finite subset. Every algebra identity and divided-power axiom has finitely many
inputs, all lying in one finite union of supports, where it holds. The same argument gives
the union grading and its direct-sum property. Restriction of a putative extension to each
finite algebra is the unique finite extension, so every operation is forced. -/
theorem set_variables (R : Type u) [CommRing R] (A : AlgebraData.{u, v} R)
    (γ : GradedDividedPowers A.grade) (e : ℕ) (he : 0 < e) (J : Type w) :
    ∃ (B : AlgebraData.{u, max v w} R) (p : SetPresentation A γ e J B)
      (δ : GradedDividedPowers B.grade),
      SetNormalized p δ ∧
      (∀ δ' : GradedDividedPowers B.grade, SetNormalized p δ' → δ' = δ) ∧
      ∀ S : Finset J, Preserves (p.into S) ((p.finite S).dp (Fin.last S.card)) δ := by
  sorry

/-- An increasing union of a sequence of adjunction algebras, with the union grading.
The compatibility equation expresses the actual inclusions from one stage to the next.
Source: Stacks, 0F4I finite-stage argument and the union in section Tate resolutions.
(blueprint: lem-sfb-divided-power-variable-adjunction). -/
structure UnionPresentation {R : Type u} [CommRing R]
    (A : ℕ → AlgebraData.{u, v₁} R) (γ : ∀ k : ℕ, GradedDividedPowers (A k).grade)
    (e : ℕ → ℕ) (J : ℕ → Type w)
    (p : ∀ k : ℕ, SetPresentation (A k) (γ k) (e k) (J k) (A (k + 1)))
    (B : AlgebraData.{u, v₂} R) where
  into : ∀ k : ℕ, Hom (A k) B
  injective : ∀ k : ℕ, Function.Injective (into k).toAlgHom
  compatibility : ∀ k : ℕ,
    (into (k + 1)).toAlgHom.comp (p k).inclusion.toAlgHom = (into k).toAlgHom
  covers : ∀ x : B.Carrier, ∃ (k : ℕ) (y : (A k).Carrier), (into k).toAlgHom y = x
  grading : ∀ (m : ℕ) (x : B.Carrier), x ∈ B.grade m ↔
    ∃ (k : ℕ) (y : (A k).Carrier), y ∈ (A k).grade m ∧ (into k).toAlgHom y = x

/-- Increasing unions of successive set adjunctions have the union grading and exactly
one divided-power structure extending all stages.
Source: Stacks, 0F4I and section Tate resolutions, the increasing-union construction.
(blueprint: lem-sfb-divided-power-variable-adjunction).

Proof: Identify the stages through their injective coefficient inclusions and take their
union. Define every operation on an element in a stage containing it. The inclusions
preserve the operations, so this is independent of the stage. Finitely many inputs belong
to one stage, taking the maximum of their indices; all ring, algebra and divided-power
identities follow there. For the union grading, a finite sum of components which is zero
already vanishes at one stage, where each component vanishes separately. Thus the union
grading is a nonnegative direct-sum grading and remains strictly graded commutative.
Every alternative divided-power structure agrees at every stage, hence on every element
of the union, proving uniqueness. -/
theorem increasing_union (R : Type u) [CommRing R] (A : ℕ → AlgebraData.{u, v} R)
    (γ : ∀ k : ℕ, GradedDividedPowers (A k).grade) (e : ℕ → ℕ)
    (he : ∀ k : ℕ, 0 < e k) (J : ℕ → Type w)
    (p : ∀ k : ℕ, SetPresentation (A k) (γ k) (e k) (J k) (A (k + 1)))
    (hp : ∀ k : ℕ, SetNormalized (p k) (γ (k + 1))) :
    ∃ (B : AlgebraData.{u, v} R) (q : UnionPresentation A γ e J p B),
      ∃! δ : GradedDividedPowers B.grade, ∀ k : ℕ, Preserves (q.into k) (γ k) δ := by
  sorry

end VariableAdjunction
end GradedAlgebra
