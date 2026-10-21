/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.Paper.FinitePullbackTensorComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.SixFunctors.OpenTensorNormalization
/-!
# Unit and coefficient associativity for a fixed compactification
Source: Stacks Project, sites-cohomology.tex, Tags 0B56 and 0GL1;
current blueprint sk-prop-cohsm, equation (G13)
(blueprint: lem-pur-projection-formula-coefficient-coherence).
The fixed-ring coordinates below use the canonical intrinsic realization solely to
express the recorded constructibility predicates. All arrows are the ordinary
constant-coefficient derived arrows at the specified compactification.

## Main definitions

* `inverseCompactificationProjection`: the symmetry-conjugate canonical inverse.
* `CompactificationProjectionUnit`, `CompactificationProjectionAssoc`: the two equations.
* `CompactificationProjectionDomains`: all their constructible tensor inputs.

## Main statements

* `compactificationProjection_coefficient_coherence`: both laws and their domains.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
/-- The canonical Koszul symmetry of the existing derived tensor, descended through
K-flat localization. No arbitrary choice of a braiding is made.
Source: Stacks 0FPT, signed total tensor symmetry
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def projectionCoherenceSymmetry
    (C : Type v) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (K L : DerivedCategory C) : K ⊗ L ≅ L ⊗ K :=
  DerivedMonoidal.braiding' DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) K L
/-- The existing finite-ring Noetherian instance exposed at the positive quotient.
This makes the fixed-ring flat-pullback interface available without a long general search.
Source: finite coefficient convention; a finite ring is Noetherian
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
instance projectionCoherenceCoefficientNoetherian
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    IsNoetherianRing (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  isNoetherian_of_finite _ _

/-- Canonical derived realization from fixed-ring sheaves to intrinsic constant-ring
modules. The positive quotient's finiteness is supplied by its recorded theorem.
Source: Stacks 00YV, constant-coefficient realization
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def projectionCoherenceRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)).functor
/-- The recorded bounded constructibility predicate in canonical fixed-ring coordinates.
Source: blueprint finite-torsion convention and Stacks 00YV
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
abbrev projectionCoherenceConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))) : Prop :=
  Scheme.intrinsicFiniteTorsionConstructible l E n hn X
    ((projectionCoherenceRealization l E n hn X).obj M)
/-- The recorded finite-Tor constructibility predicate in the same coordinates.
Source: blueprint def-weil-finite-tor-amplitude and Stacks 00YV
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
abbrev projectionCoherenceFiniteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))) : Prop :=
  WeilConjectures.finiteTorConstructible l E n hn X
    ((projectionCoherenceRealization l E n hn X).obj M)
/-- The unit equation, written in diagrammatic composition order. Parameters name the
specified maps, so specialization below supplies only the canonical compactification maps.
Source: blueprint def-sfb-projection-formula, unit equation; Stacks 0B56/0GL1
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionUnit
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {T : Type v₁} [Category.{w₁} T] [MonoidalCategory T]
    (P : C ⥤ T) (S : T ⥤ C) (e : S.obj (𝟙_ T) ⟶ 𝟙_ C) (M : C)
    (pi : P.obj (S.obj (𝟙_ T) ⊗ M) ⟶ (𝟙_ T) ⊗ P.obj M) : Prop :=
  pi ≫ (λ_ (P.obj M)).hom = P.map (e ▷ M ≫ (λ_ M).hom)
/-- The coefficient-associativity equation for its three specified components.
Source: blueprint def-sfb-projection-formula, associativity equation; Stacks 0B56/0GL1
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionAssoc
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {T : Type v₁} [Category.{w₁} T] [MonoidalCategory T]
    (P : C ⥤ T) (S : T ⥤ C) (B B' : T) (M : C)
    (delta : S.obj (B ⊗ B') ⟶ S.obj B ⊗ S.obj B')
    (piprod : P.obj (S.obj (B ⊗ B') ⊗ M) ⟶ (B ⊗ B') ⊗ P.obj M)
    (pileft : P.obj (S.obj B ⊗ (S.obj B' ⊗ M)) ⟶ B ⊗ P.obj (S.obj B' ⊗ M))
    (piright : P.obj (S.obj B' ⊗ M) ⟶ B' ⊗ P.obj M) : Prop :=
  piprod ≫ (α_ B B' (P.obj M)).hom =
    P.map (delta ▷ M ≫ (α_ (S.obj B) (S.obj B') M).hom) ≫ pileft ≫ B ◁ piright
section Arrows
variable (V : Type v) [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
  [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
  [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
  (c : Compactification f)
/-- The symmetry-conjugate inverse of precisely the counit/open compactification map.
Only its supplied component is inverted; no isomorphism is chosen independently.
Source: Stacks 0B56/0GL1 and the displayed definition of pi in the node
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
@[irreducible] def inverseCompactificationProjection
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      V))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      V))
    (h : IsIso (((projectionMapOfCompactification
      V c).app M).app B)) :
    (rightDerivedLowerShriekOfCompactification
      V c).obj
        ((L((f)^*[V])).obj B ⊗ M) ⟶
      B ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M :=
  letI := h
  (rightDerivedLowerShriekOfCompactification
    V c).map (projectionCoherenceSymmetry _ _ _).hom ≫
      inv (((projectionMapOfCompactification
        V c).app M).app B) ≫
        (projectionCoherenceSymmetry _ _ _).hom
/-- The exact list of constructible and finite-Tor tensor inputs in the two equations.
The predicates are supplied below by the recorded intrinsic predicates through the
canonical realization, so they introduce neither a replacement category nor assumptions.
Source: the node's last domain clause, blueprint (G13), Stacks 0GL0
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionDomains
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      V)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      V)) : Prop :=
  (∀ K ∈ [𝟙_ _, B ⊗ B'], ty K) ∧
    (∀ K ∈ [(L((f)^*[V])).obj (𝟙_ _),
      (L((f)^*[V])).obj B,
      (L((f)^*[V])).obj B',
      (L((f)^*[V])).obj (B ⊗ B'),
      (L((f)^*[V])).obj B ⊗ (L((f)^*[V])).obj B'], tx K) ∧
    (∀ K ∈ [(L((f)^*[V])).obj (𝟙_ _) ⊗ M,
      (L((f)^*[V])).obj B' ⊗ M,
      (L((f)^*[V])).obj (B ⊗ B') ⊗ M,
      ((L((f)^*[V])).obj B ⊗
        (L((f)^*[V])).obj B') ⊗ M,
      (L((f)^*[V])).obj B ⊗
        ((L((f)^*[V])).obj B' ⊗ M),
      M ⊗ (L((f)^*[V])).obj (𝟙_ _),
      M ⊗ (L((f)^*[V])).obj (B ⊗ B'),
      ((L((f)^*[V])).obj B' ⊗ M) ⊗ (L((f)^*[V])).obj B,
      M ⊗ (L((f)^*[V])).obj B'], cx K) ∧
    (∀ K ∈ [(rightDerivedLowerShriekOfCompactification
      V c).obj M,
      𝟙_ _ ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M,
      B' ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M,
      (B ⊗ B') ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M,
      B ⊗ (B' ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj (𝟙_ _) ⊗ M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj B' ⊗ M),
      B ⊗ (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj B' ⊗ M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj (B ⊗ B') ⊗ M),
      (rightDerivedLowerShriekOfCompactification
        V c).obj
          ((L((f)^*[V])).obj B ⊗
            ((L((f)^*[V])).obj B' ⊗ M)),
      (rightDerivedLowerShriekOfCompactification V c).obj M ⊗ 𝟙_ _,
      (rightDerivedLowerShriekOfCompactification V c).obj M ⊗ (B ⊗ B'),
      (rightDerivedLowerShriekOfCompactification V c).obj
        ((L((f)^*[V])).obj B' ⊗ M) ⊗ B,
      (rightDerivedLowerShriekOfCompactification V c).obj M ⊗ B',
      (rightDerivedLowerShriekOfCompactification V c).obj
        (M ⊗ (L((f)^*[V])).obj (𝟙_ _)),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (M ⊗ (L((f)^*[V])).obj (B ⊗ B')),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (((L((f)^*[V])).obj B' ⊗ M) ⊗ (L((f)^*[V])).obj B),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (M ⊗ (L((f)^*[V])).obj B'),
      (rightDerivedLowerShriekOfCompactification V c).obj
        (((L((f)^*[V])).obj B ⊗ (L((f)^*[V])).obj B') ⊗ M)], cy K)
/-- The complete coefficient-coherence assertion for the actual canonical maps.
Keeping its quantifiers at the coefficient-category interface avoids repeated expansion
of the specialized derived monoidal structure; it adds no hypothesis or choice.
Source: Stacks 0B56/0GL1, blueprint (G13)
(blueprint: lem-pur-projection-formula-coefficient-coherence). -/
def CompactificationProjectionCoefficientCoherence
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V))) : Prop :=
  ∀ (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)),
    cx M → ty B → ty B' →
    ∀ (hunit : IsIso (((projectionMapOfCompactification V c).app M).app (𝟙_ _)))
      (hprod : IsIso (((projectionMapOfCompactification V c).app M).app (B ⊗ B')))
      (hleft : IsIso (((projectionMapOfCompactification V c).app
        ((L((f)^*[V])).obj B' ⊗ M)).app B))
      (hright : IsIso (((projectionMapOfCompactification V c).app M).app B')),
      CompactificationProjectionUnit (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) (leftDerivedUpperStarUnitIso V f).hom M
        (inverseCompactificationProjection V c (𝟙_ _) M hunit) ∧
      CompactificationProjectionAssoc (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) B B' M (leftDerivedUpperStarTensorIso V f B B').hom
        (inverseCompactificationProjection V c (B ⊗ B') M hprod)
        (inverseCompactificationProjection V c B ((L((f)^*[V])).obj B' ⊗ M) hleft)
        (inverseCompactificationProjection V c B' M hright) ∧
      CompactificationProjectionDomains V c cx tx cy ty M B B'

end Arrows
/-- The fixed-compactification inverse projection maps satisfy the unit and
coefficient-associativity equations, with all displayed inputs in their stated domains.
Source: Stacks 0B56 and 0GL1; current blueprint sk-prop-cohsm, (G13)
(blueprint: lem-pur-projection-formula-coefficient-coherence).
Proof:
1. Work in the ambient ordinary derived categories. Write F = Lr*, R = Rr*,
Q = Lj*, J = j!, P = RJ, S = QF. Use the canonical pullback tensor, unit,
signed symmetry and composition comparisons of lem-pur-derived-pullback-tensor-iso,
and structural coherence (lem-coef-monoidal-structural-coherence).
2. Conjugate the proper and open forward projection maps by symmetry to obtain
left-coefficient maps t and v. Transposition through F adjoint to R identifies t
with delta followed by identity tensor counit (def-exchange-projection and
lem-weil-pbc-adjunction-of-natural-bijection). The compactification map becomes R(v)t.
3. Transpose its proper unit equation. Counit naturality and the unit constraint
of F identify both transposes; injectivity of the adjunction bijection proves equality.
4. Transpose its proper two-coefficient equation twice. Naturality of delta and
its associativity constraint identify both transposes with counit tensor two identities.
5. For J use lem-sf-open-tensor-normalization: its unit is invertible, J is fully
faithful, and v restricts to the identity. Restriction detects these equations
between objects in its essential image, giving the open unit and associativity laws.
6. Expand R(v)t in the unit equation. Naturality of v and e_S = e_Q Q(e_F)
reduce it successively to the open unit law and proper unit law.
7. Expand R(v)t for two coefficients. Move v through t by naturality; apply the
proper law, then the open law and delta_S = delta_Q Q(delta_F). This gives the
forward associativity law of the specified compactification map.
8. Invert only the four components assumed below. Symmetry squared is identity,
so their conjugate inverses are inverseCompactificationProjection. Cancellation
in the forward equations gives precisely CompactificationProjectionUnit and Assoc.
9. lem-sf-pullback-tor-amplitude preserves the coefficients' finite Tor amplitude;
lem-sf-tensor-ctf gives bounded constructibility with M, and finite Tor amplitude
for the coefficient product. prop-finite-compact-support-constructibility treats
all compact-support images. The unit is flat in degree zero. Thus every tensor
input displayed in the equations belongs to the claimed domain; M needs no
finite Tor amplitude. This applies equally to empty schemes, zero inputs and units. -/
theorem compactificationProjection_coefficient_coherence
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    CompactificationProjectionCoefficientCoherence
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c
      (projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) X)
      (projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) X)
      (projectionCoherenceConstructible l E (n + 1) (Nat.succ_pos n) Y)
      (projectionCoherenceFiniteTor l E (n + 1) (Nat.succ_pos n) Y) := by
  sorry

end AlgebraicGeometry.ProEtale
