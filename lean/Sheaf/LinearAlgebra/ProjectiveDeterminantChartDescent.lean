/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.LinearAlgebra.ProjectiveDeterminantModule
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.RingTheory.CoverModuleExact
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.InvariantBasisNumber
import WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization
import Sheaf.RingTheory.FiniteProjectiveOfStandardCover

/-! # Descent of determinant charts and tensor isomorphisms

Source: Stacks Project, More on Algebra, Tags 0FJ9, 0FJA
(`remark-determinant-as-socle`) and 0FJB (`lemma-det-ses`, first proof);
Algebra, Tag 00EK (`lemma-cover-module`).
(blueprint: lem-trf-projective-determinant-chart-descent)

The charts are characterized by inclusion in the exterior algebra. Transitions use
localizations of the same intrinsic socle; no rank equality is required on zero overlaps.
The auxiliary definitions below encode this node's charts and their descent equations.
-/

@[expose] public section

set_option autoImplicit false
universe u v w z t k

open scoped TensorProduct

namespace Module

/-- A chart's top exterior module. Source: Stacks 0FJ9--0FJA, local top wedges
(blueprint: lem-trf-projective-determinant-chart-descent). -/
abbrev determinantChartLine {R : Type u} [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E] (f : R) (n : ℕ) :=
  ⋀[Localization.Away f]^n (LocalizedModule.Away f E)

/-- The canonical restriction on principal localizations, using the already recorded
00EK localization lift. Source: Stacks 00EK, the maps to the pairwise overlaps
(blueprint: lem-trf-projective-determinant-chart-descent). -/
noncomputable def determinantChartRestriction {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (a h : R) (ha : a ∣ h) :
    LocalizedModule.Away a M →ₗ[R] LocalizedModule.Away h M :=
  IsLocalizedModule.lift (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
    (RingTheory.localizationAway_map_units_of_dvd a h ha)

/-- A system of determinant charts with its exterior inclusion formula. The last field
records that restricting a chart to any smaller principal open is still localization of
the same socle. It is a property of the chart maps, rather than an extra choice of maps.
Source: Stacks 0FJA and the descent portion of 0FJB
(blueprint: lem-trf-projective-determinant-chart-descent). -/
structure DeterminantCharts {R : Type u} [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    {r : ℕ} (f : Fin r → R) (n : Fin r → ℕ) where
  map : ∀ a : Fin r, determinantModule R E →ₗ[R] determinantChartLine E (f a) (n a)
  inclusion : ∀ (a : Fin r) (x : determinantModule R E),
    (map a x).val = ExteriorAlgebra.scalarExtensionMap
      (LocalizedModule.mkLinearMap (Submonoid.powers (f a)) E) x.val
  localizes : ∀ a : Fin r, IsLocalizedModule (Submonoid.powers (f a)) (map a)
  restricts : ∀ (a : Fin r) (h : R), f a ∣ h →
    IsLocalizedModule (Submonoid.powers h)
      ((LocalizedModule.mkLinearMap (Submonoid.powers h)
        (determinantChartLine E (f a) (n a))).comp (map a))

namespace DeterminantCharts

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]
variable {r : ℕ} {f : Fin r → R} {n : Fin r → ℕ}

/-- A chart identification, uniquely induced by its localization map. Source: Stacks
0FJA, inclusion of the top wedge (blueprint: lem-trf-projective-determinant-chart-descent). -/
noncomputable def iso (C : DeterminantCharts E f n) (a : Fin r) :
    LocalizedModule.Away (f a) (determinantModule R E) ≃ₗ[R]
      determinantChartLine E (f a) (n a) :=
  @IsLocalizedModule.iso R _ (Submonoid.powers (f a)) _ _ _ _ _ _ (C.map a)
    (C.localizes a)

/-- Identify a restricted chart with the restriction of the intrinsic determinant.
Localizing at h rather than at the complementary factor gives the same restriction,
since f a already acts invertibly on this chart. Source: Stacks 0FJA and 00EK
(blueprint: lem-trf-projective-determinant-chart-descent). -/
noncomputable def restrictedIso (C : DeterminantCharts E f n)
    (a : Fin r) (h : R) (ha : f a ∣ h) :
    LocalizedModule.Away h (determinantModule R E) ≃ₗ[R]
      LocalizedModule.Away h (determinantChartLine E (f a) (n a)) :=
  @IsLocalizedModule.iso R _ (Submonoid.powers h) _ _ _ _ _ _
    ((LocalizedModule.mkLinearMap (Submonoid.powers h)
      (determinantChartLine E (f a) (n a))).comp (C.map a)) (C.restricts a h ha)

/-- The transition on a common principal restriction, including between two different
covers. Its maps are transported through the same localized socle. Source: Stacks 0FJA
and the descent portion of 0FJB
(blueprint: lem-trf-projective-determinant-chart-descent). -/
noncomputable def transition {s : ℕ} {g : Fin s → R} {m : Fin s → ℕ}
    (C : DeterminantCharts E f n) (C' : DeterminantCharts E g m)
    (a : Fin r) (b : Fin s) (h : R) (ha : f a ∣ h) (hb : g b ∣ h) :
    LocalizedModule.Away h (determinantChartLine E (f a) (n a)) ≃ₗ[R]
      LocalizedModule.Away h (determinantChartLine E (g b) (m b)) :=
  (C.restrictedIso a h ha).symm.trans (C'.restrictedIso b h hb)

end DeterminantCharts

/-- The chart part of determinant descent, with normalization and arbitrary localization.
Source: Stacks 0FJ9, 0FJA, 0FJB (first proof), and Algebra 00EK
(blueprint: lem-trf-projective-determinant-chart-descent).

Proof, steps 1--2: exterior-power localization, degree by degree, assembles into exterior
algebra localization (new-v2-generic-exterior-power-localization). Finite supports allow
common denominators. Test the socle equations on finitely many generators of E; clearing
the product of their denominators proves localization of the socle, even when 0 is inverted.
Step 3: expand in the exterior basis (lem-weil-pbc-exterior-power-free-basis). Annihilation
by each basis vector kills every term except the full-index wedge. Only signs occur, so
this works in characteristic two, rank zero, and the zero ring.
Step 4: these inclusions give the unique chart maps. Invariant basis number
(lem-sfb-commutative-ring-invariant-basis-number) equates ranks on nonzero overlaps.
Transport through the common localized socle gives identity transitions and the cocycle.
Step 5: each localized socle is a free line; the finite principal-cover criterion
(lem-sc-affine-standard-cover-finite-projective) gives finite projectivity. Taking D to
be the intrinsic socle realizes descent. Any other realization has a unique comparison:
glue its local comparisons and their inverses using lem-weil-pbc-cover-module-exact.
Step 6: inclusion characterizes every chart without a basis choice. Two covers agree on
their product refinement; uniqueness in 00EK identifies their comparisons. The same
exterior localization formula gives compatibility with every S and successive localization.
For E = 0, only degree zero remains and the empty wedge is the scalar 1. -/
theorem determinant_chart_descent {R : Type u} [CommRing R]
    {E : Type v} [AddCommGroup E] [Module R E]
    [Module.Finite R E] [Module.Projective R E]
    {r : ℕ} (f : Fin r → R) (hcover : Ideal.span (Set.range f) = ⊤)
    (n : Fin r → ℕ)
    (basis : ∀ a : Fin r,
      Module.Basis (Fin (n a)) (Localization.Away (f a)) (LocalizedModule.Away (f a) E)) :
    (∃! C : DeterminantCharts E f n, True) ∧
    Module.Finite R (determinantModule R E) ∧
    Module.Projective R (determinantModule R E) ∧
    (∀ a : Fin r, Nonempty (LocalizedModule.Away (f a) (determinantModule R E) ≃ₗ[
      Localization.Away (f a)] Localization.Away (f a))) ∧
    (∀ (a b : Fin r), Nontrivial (Localization.Away (f a * f b)) → n a = n b) ∧
    (∀ (C : DeterminantCharts E f n)
      (P : Type t) [AddCommGroup P] [Module R P]
      (p : ∀ a : Fin r, P →ₗ[R] determinantChartLine E (f a) (n a)),
      (∀ a : Fin r, IsLocalizedModule (Submonoid.powers (f a)) (p a)) →
      (∀ (a b : Fin r) (x : P),
        determinantChartRestriction (determinantModule R E) (f a) (f a * f b)
          (dvd_mul_right (f a) (f b)) ((C.iso a).symm (p a x)) =
        determinantChartRestriction (determinantModule R E) (f b) (f a * f b)
          (dvd_mul_left (f b) (f a)) ((C.iso b).symm (p b x))) →
      ∃! d : P ≃ₗ[R] determinantModule R E,
        ∀ (a : Fin r) (x : P), C.map a (d x) = p a x) ∧
    (∀ (C : DeterminantCharts E f n) (a b : Fin r) (h : R)
      (ha : f a ∣ h) (hb : f b ∣ h) (x : determinantModule R E),
      C.transition C a b h ha hb
        (LocalizedModule.mk (C.map a x) (1 : Submonoid.powers h)) =
          LocalizedModule.mk (C.map b x) (1 : Submonoid.powers h)) ∧
    (∀ (C : DeterminantCharts E f n) (a : Fin r) (h : R) (ha : f a ∣ h),
      C.transition C a a h ha ha = LinearEquiv.refl R _) ∧
    (∀ (C : DeterminantCharts E f n) (a b c : Fin r) (h : R)
      (ha : f a ∣ h) (hb : f b ∣ h) (hc : f c ∣ h),
      (C.transition C a b h ha hb).trans (C.transition C b c h hb hc) =
        C.transition C a c h ha hc) ∧
    (∀ (S : Submonoid R),
      ∃! q : determinantModule R E →ₗ[R]
        determinantModule (Localization S) (LocalizedModule S E),
        (∀ x : determinantModule R E, (q x).val = ExteriorAlgebra.scalarExtensionMap
          (LocalizedModule.mkLinearMap S E) x.val) ∧ IsLocalizedModule S q) ∧
    (Subsingleton E → ∃! e : determinantModule R E ≃ₗ[R] R,
      ∀ a : R, (e.symm a).val = algebraMap R (ExteriorAlgebra R E) a) := sorry

/-- The canonical tensor map to localized coefficient modules. This is the tensor map
of the recorded localization-tensor-product interface, followed by its change-of-ring
comparison; on pure tensors it is x tensor y mapped to q₁ x tensor q₂ y.
Source: Stacks Algebra 00DL, used in the descent portion of 0FJB
(blueprint: lem-trf-projective-determinant-chart-descent). -/
noncomputable def determinantLocalizedTensorMap {R : Type u} [CommRing R]
    (S : Submonoid R) (A : Type t) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {N₁ : Type z} [AddCommGroup N₁] [Module R N₁] [Module A N₁]
    [IsScalarTower R A N₁]
    {N₂ : Type k} [AddCommGroup N₂] [Module R N₂] [Module A N₂]
    [IsScalarTower R A N₂] (q₁ : M₁ →ₗ[R] N₁) (q₂ : M₂ →ₗ[R] N₂) :
    (M₁ ⊗[R] M₂) →ₗ[R] (N₁ ⊗[A] N₂) :=
  ((IsLocalization.moduleTensorEquiv S A N₁ N₂).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.map q₁ q₂)

namespace DeterminantCharts

variable {R : Type u} [CommRing R]
variable {E₁ : Type v} [AddCommGroup E₁] [Module R E₁]
variable {E₂ : Type w} [AddCommGroup E₂] [Module R E₂]
variable {E₃ : Type z} [AddCommGroup E₃] [Module R E₃]
variable {r : ℕ} {f : Fin r → R} {n₁ n₂ n₃ : Fin r → ℕ}

/-- The local tensor pairing, viewed as a section of the localization of the target
socle. This uses the canonical tensor comparison and the inverse chart of the third
module. Source: Stacks 00DL and the descent portion of 0FJB
(blueprint: lem-trf-projective-determinant-chart-descent). -/
noncomputable def pairingSection
    (C₁ : DeterminantCharts E₁ f n₁) (C₂ : DeterminantCharts E₂ f n₂)
    (C₃ : DeterminantCharts E₃ f n₃)
    (lam : ∀ a : Fin r,
      (determinantChartLine E₁ (f a) (n₁ a) ⊗[Localization.Away (f a)]
        determinantChartLine E₂ (f a) (n₂ a)) ≃ₗ[Localization.Away (f a)]
          determinantChartLine E₃ (f a) (n₃ a)) (a : Fin r) :
    (determinantModule R E₁ ⊗[R] determinantModule R E₂) →ₗ[R]
      LocalizedModule.Away (f a) (determinantModule R E₃) :=
  (C₃.iso a).symm.toLinearMap.comp (((lam a).restrictScalars R).toLinearMap.comp
    (determinantLocalizedTensorMap (Submonoid.powers (f a)) (Localization.Away (f a))
      (C₁.map a) (C₂.map a)))

/-- The exact overlap compatibility equation for the supplied tensor pairings. Testing
on the original tensor module suffices because its fractions generate every overlap.
Source: Stacks 00EK, transported by the preceding determinant transitions and 00DL
(blueprint: lem-trf-projective-determinant-chart-descent). -/
def PairingsCompatible
    (C₁ : DeterminantCharts E₁ f n₁) (C₂ : DeterminantCharts E₂ f n₂)
    (C₃ : DeterminantCharts E₃ f n₃)
    (lam : ∀ a : Fin r,
      (determinantChartLine E₁ (f a) (n₁ a) ⊗[Localization.Away (f a)]
        determinantChartLine E₂ (f a) (n₂ a)) ≃ₗ[Localization.Away (f a)]
          determinantChartLine E₃ (f a) (n₃ a)) : Prop :=
  ∀ (a b : Fin r) (p : determinantModule R E₁ ⊗[R] determinantModule R E₂),
    determinantChartRestriction (determinantModule R E₃) (f a) (f a * f b)
      (dvd_mul_right (f a) (f b)) (pairingSection C₁ C₂ C₃ lam a p) =
    determinantChartRestriction (determinantModule R E₃) (f b) (f a * f b)
      (dvd_mul_left (f b) (f a)) (pairingSection C₁ C₂ C₃ lam b p)

/-- A global isomorphism has precisely the supplied chart maps. Equality of these
R-linear maps says equality of their entire localized maps, by the universal property
of localization; it includes all fractions, not only selected basis generators.
Source: Stacks 00EK and 0FJB, descent of maps
(blueprint: lem-trf-projective-determinant-chart-descent). -/
def IsPairingDescent
    (C₁ : DeterminantCharts E₁ f n₁) (C₂ : DeterminantCharts E₂ f n₂)
    (C₃ : DeterminantCharts E₃ f n₃)
    (lam : ∀ a : Fin r,
      (determinantChartLine E₁ (f a) (n₁ a) ⊗[Localization.Away (f a)]
        determinantChartLine E₂ (f a) (n₂ a)) ≃ₗ[Localization.Away (f a)]
          determinantChartLine E₃ (f a) (n₃ a))
    (e : (determinantModule R E₁ ⊗[R] determinantModule R E₂) ≃ₗ[R]
      determinantModule R E₃) : Prop :=
  ∀ a : Fin r, pairingSection C₁ C₂ C₃ lam a =
    (LocalizedModule.mkLinearMap (Submonoid.powers (f a))
      (determinantModule R E₃)).comp e.toLinearMap

end DeterminantCharts

/-- Compatible local tensor isomorphisms descend uniquely, together with their inverses;
common refinements and every multiplicative-subset localization preserve the result.
Source: Stacks 0FJB, first proof's descent, and Algebra 00DL and 00EK
(blueprint: lem-trf-projective-determinant-chart-descent).

Proof, step 7: use the tensor localization comparison
(lem-weil-pbc-localization-tensor-product) to transport each local lambda to a map from
the global tensor module to the localized third socle. The compatibility hypothesis
is exactly the equalizer condition of lem-weil-pbc-cover-module-exact. Glue each
argument's images uniquely. Uniqueness proves additivity and scalar linearity. The
localized map agrees on all fractions, as it agrees on the original module. The same
injectivity clause gives uniqueness among all global linear maps, hence isomorphisms.
Step 8: invert the overlap equations and glue the local inverses by the same lemma.
Their composites are locally identities, and 00EK detects equality, so they are inverse.
Step 9: on any common principal refinement, the section equations are unchanged;
uniqueness in 00EK identifies both descended maps. After any localization S, the images
of f still cover. The exterior and tensor comparisons commute with localization on
pure wedges and pure tensors. The localized map therefore has exactly the localized
chart pairings. Gluing over the localized ring, with the localized inverse, again gives
the unique map. All arguments allow an empty cover over a zero ring, zero overlaps,
rank-zero modules, characteristic two and 0 in S. -/
theorem determinant_chart_tensor_descent {R : Type u} [CommRing R]
    {E₁ : Type v} [AddCommGroup E₁] [Module R E₁]
    [Module.Finite R E₁] [Module.Projective R E₁]
    {E₂ : Type w} [AddCommGroup E₂] [Module R E₂]
    [Module.Finite R E₂] [Module.Projective R E₂]
    {E₃ : Type z} [AddCommGroup E₃] [Module R E₃]
    [Module.Finite R E₃] [Module.Projective R E₃]
    {r : ℕ} (f : Fin r → R) (hcover : Ideal.span (Set.range f) = ⊤)
    (n₁ n₂ n₃ : Fin r → ℕ)
    (basis₁ : ∀ a : Fin r, Module.Basis (Fin (n₁ a)) (Localization.Away (f a))
      (LocalizedModule.Away (f a) E₁))
    (basis₂ : ∀ a : Fin r, Module.Basis (Fin (n₂ a)) (Localization.Away (f a))
      (LocalizedModule.Away (f a) E₂))
    (basis₃ : ∀ a : Fin r, Module.Basis (Fin (n₃ a)) (Localization.Away (f a))
      (LocalizedModule.Away (f a) E₃))
    (C₁ : DeterminantCharts E₁ f n₁) (C₂ : DeterminantCharts E₂ f n₂)
    (C₃ : DeterminantCharts E₃ f n₃)
    (lam : ∀ a : Fin r,
      (determinantChartLine E₁ (f a) (n₁ a) ⊗[Localization.Away (f a)]
        determinantChartLine E₂ (f a) (n₂ a)) ≃ₗ[Localization.Away (f a)]
          determinantChartLine E₃ (f a) (n₃ a))
    (hcompat : DeterminantCharts.PairingsCompatible C₁ C₂ C₃ lam) :
    ∃ e : (determinantModule R E₁ ⊗[R] determinantModule R E₂) ≃ₗ[R]
      determinantModule R E₃,
      DeterminantCharts.IsPairingDescent C₁ C₂ C₃ lam e ∧
      (∀ e' : (determinantModule R E₁ ⊗[R] determinantModule R E₂) ≃ₗ[R]
        determinantModule R E₃,
        DeterminantCharts.IsPairingDescent C₁ C₂ C₃ lam e' → e' = e) ∧
      (∀ (a : Fin r) (x : determinantModule R E₃),
        determinantLocalizedTensorMap (Submonoid.powers (f a)) (Localization.Away (f a))
          (C₁.map a) (C₂.map a) (e.symm x) = (lam a).symm (C₃.map a x)) ∧
      (∀ (s : ℕ) (g : Fin s → R), Ideal.span (Set.range g) = ⊤ →
        ∀ (m₁ m₂ m₃ : Fin s → ℕ)
          (C₁' : DeterminantCharts E₁ g m₁) (C₂' : DeterminantCharts E₂ g m₂)
          (C₃' : DeterminantCharts E₃ g m₃)
          (mu : ∀ b : Fin s,
            (determinantChartLine E₁ (g b) (m₁ b) ⊗[Localization.Away (g b)]
              determinantChartLine E₂ (g b) (m₂ b)) ≃ₗ[Localization.Away (g b)]
                determinantChartLine E₃ (g b) (m₃ b)),
        (∀ (a : Fin r) (b : Fin s)
          (p : determinantModule R E₁ ⊗[R] determinantModule R E₂),
          determinantChartRestriction (determinantModule R E₃) (f a) (f a * g b)
            (dvd_mul_right (f a) (g b))
            (DeterminantCharts.pairingSection C₁ C₂ C₃ lam a p) =
          determinantChartRestriction (determinantModule R E₃) (g b) (f a * g b)
            (dvd_mul_left (g b) (f a))
            (DeterminantCharts.pairingSection C₁' C₂' C₃' mu b p)) →
          DeterminantCharts.IsPairingDescent C₁' C₂' C₃' mu e) ∧
      (∀ (S : Submonoid R)
        (q₁ : determinantModule R E₁ →ₗ[R]
          determinantModule (Localization S) (LocalizedModule S E₁))
        (q₂ : determinantModule R E₂ →ₗ[R]
          determinantModule (Localization S) (LocalizedModule S E₂))
        (q₃ : determinantModule R E₃ →ₗ[R]
          determinantModule (Localization S) (LocalizedModule S E₃))
        (l₁ : IsLocalizedModule S q₁) (l₂ : IsLocalizedModule S q₂)
        (l₃ : IsLocalizedModule S q₃),
        (∀ x, (q₁ x).val = ExteriorAlgebra.scalarExtensionMap
          (LocalizedModule.mkLinearMap S E₁) x.val) →
        (∀ x, (q₂ x).val = ExteriorAlgebra.scalarExtensionMap
          (LocalizedModule.mkLinearMap S E₂) x.val) →
        (∀ x, (q₃ x).val = ExteriorAlgebra.scalarExtensionMap
          (LocalizedModule.mkLinearMap S E₃) x.val) →
        ∃ eS : (determinantModule (Localization S) (LocalizedModule S E₁) ⊗[Localization S]
          determinantModule (Localization S) (LocalizedModule S E₂)) ≃ₗ[Localization S]
            determinantModule (Localization S) (LocalizedModule S E₃),
          (∀ p, q₃ (e p) = eS (determinantLocalizedTensorMap S (Localization S) q₁ q₂ p)) ∧
          (∀ eS' : (determinantModule (Localization S) (LocalizedModule S E₁) ⊗[Localization S]
            determinantModule (Localization S) (LocalizedModule S E₂)) ≃ₗ[Localization S]
              determinantModule (Localization S) (LocalizedModule S E₃),
            (∀ p, q₃ (e p) = eS' (determinantLocalizedTensorMap S (Localization S) q₁ q₂ p)) →
              eS' = eS) ∧
          (∀ x, eS.symm (q₃ x) =
            determinantLocalizedTensorMap S (Localization S) q₁ q₂ (e.symm x)) ∧
          (∀ (a : Fin r) (x : determinantModule R E₁) (y : determinantModule R E₂),
            (@IsLocalizedModule.map R _ S _ _ _ _ _ _
              q₃ l₃ _ _ _ _ _ _
              (LocalizedModule.mkLinearMap S (determinantChartLine E₃ (f a) (n₃ a)))
                inferInstance (C₃.map a)) (eS (q₁ x ⊗ₜ[Localization S] q₂ y)) =
              LocalizedModule.mk
                (lam a (C₁.map a x ⊗ₜ[Localization.Away (f a)] C₂.map a y)) 1)) := sorry

end Module
