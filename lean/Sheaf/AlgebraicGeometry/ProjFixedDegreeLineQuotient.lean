/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Sheaf.RingTheory.VeroneseGradedRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists

/-! # Fixed-degree line quotients and morphisms to Proj

Source: Stacks Project, Constructions, Tags 01MS, 01N8 and 01N9,
equations Ud and psi-d (blueprint: lem-sfb-proj-fixed-degree-line-quotient).

The grading is by integer submodules: every additive subgroup has its unique integer
module structure, so this imposes no algebra or generation hypothesis on the ring.
The Veronese ring, twists, section ring and tensor pullback are the existing constructions.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry.Proj

variable {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedRing 𝒜] (d : ℕ+)

/-- The union of the standard opens of degree d, Stacks equation Ud.
(blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def fixedDegreeOpen : (Proj 𝒜).Opens :=
  ⨆ a : 𝒜 (d : ℕ), basicOpen 𝒜 a.val

/-- The actual restriction of the kd-th twist, including k = 0; Stacks equation Ud.
(blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def fixedDegreeTwist (k : ℕ) : (fixedDegreeOpen 𝒜 d).toScheme.Modules :=
  (twist 𝒜 (0 + ((k * (d : ℕ) : ℕ) : ℤ))).restrict (fixedDegreeOpen 𝒜 d).ι

/-- The degree-d line, as the literal restriction of O(d); Stacks equation Ud.
(blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def fixedDegreeLine : (fixedDegreeOpen 𝒜 d).toScheme.Modules :=
  (twist 𝒜 (0 + (d : ℕ))).restrict (fixedDegreeOpen 𝒜 d).ι

/-- The restriction of the canonical homogeneous section b/1. Stacks equation psi-d.
(blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def fixedDegreeCanonicalSection (k : ℕ) (b : GradedAlgebra.veroneseGrade 𝒜 d k) :
    Γ(fixedDegreeTwist 𝒜 d k, ⊤) :=
  ((twist 𝒜 (0 + ((k * (d : ℕ) : ℕ) : ℤ))).restrictAppIso
    (fixedDegreeOpen 𝒜 d).ι ⊤).inv
      ((unitToTwist (𝒜 := 𝒜) b.property).app
        ((fixedDegreeOpen 𝒜 d).ι ''ᵁ ⊤) (1 : Γ(Proj 𝒜, _)))

/-- The existing type of graded unital maps from the actual Veronese ring to the actual
section ring. The explicit proof argument permits dependent existential conclusions.
Source: Stacks equation psi-d (blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
abbrev FixedDegreeMap {T : Scheme.{u}} (L : T.Modules) (hL : L.IsInvertible) :=
  letI := hL
  GradedAlgebra.veroneseGrade 𝒜 d →+*ᵍ sectionRingGrade L

/-- Evaluate the kth homogeneous component of a section-ring map.
Source: Stacks 01N8 (blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def fixedDegreeImage {T : Scheme.{u}} (L : T.Modules) (hL : L.IsInvertible)
    (φ : FixedDegreeMap 𝒜 d L hL) (k : ℕ)
    (b : GradedAlgebra.veroneseGrade 𝒜 d k) : Γ(L.tensorPow k, ⊤) :=
  (φ b.val) k

/-- Degree one is identified with L by its canonical right unitor.
Source: Stacks 01N8 (blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def fixedDegreeLinearSection {T : Scheme.{u}} (L : T.Modules) (hL : L.IsInvertible)
    (φ : FixedDegreeMap 𝒜 d L hL) (a : GradedAlgebra.veroneseGrade 𝒜 d 1) : Γ(L, ⊤) :=
  (ρ_ L).hom.app ⊤ (fixedDegreeImage 𝒜 d L hL φ 1 a)

/-- For an invertible module, sheaf generation by these sections is exactly coverage by
nonvanishing opens; no finite subcover is required.
Source: Stacks 01N8 (blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def FixedDegreeGenerates {T : Scheme.{u}} (L : T.Modules) (hL : L.IsInvertible)
    (φ : FixedDegreeMap 𝒜 d L hL) : Prop :=
  (⨆ a : GradedAlgebra.veroneseGrade 𝒜 d 1,
    generatingLocus (fixedDegreeLinearSection 𝒜 d L hL φ a)) = ⊤

/-- Compatibility in every degree, with canonical tensor-pullback comparisons. HEq only
identifies the inverse image of the top open with the top open of the source.
Source: Stacks 01N8, diagram (blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def FixedDegreeCompatible (hM : (fixedDegreeLine 𝒜 d).IsInvertible)
    (η : FixedDegreeMap 𝒜 d (fixedDegreeLine 𝒜 d) hM)
    {T : Scheme.{u}} (L : T.Modules) (hL : L.IsInvertible)
    (φ : FixedDegreeMap 𝒜 d L hL) (g : T ⟶ (fixedDegreeOpen 𝒜 d).toScheme)
    (α : (tensorPullback g).obj (fixedDegreeLine 𝒜 d) ≅ L) : Prop :=
  ∀ (k : ℕ) (b : GradedAlgebra.veroneseGrade 𝒜 d k),
    HEq (((boundaryPullbackPowIso g (fixedDegreeLine 𝒜 d) k ≪≫
      boundaryTensorPowIso α k).hom).app (g ⁻¹ᵁ ⊤)
        (tensorPullbackSection g ((fixedDegreeLine 𝒜 d).tensorPow k) ⊤
          (fixedDegreeImage 𝒜 d (fixedDegreeLine 𝒜 d) hM η k b)))
      (fixedDegreeImage 𝒜 d L hL φ k b)

/-- The chart preimage and fraction formula. Multiplying by the free generator expresses
exactly division on its nonvanishing open; no cancellation outside that open is asserted.
Source: Stacks 01N8, first proof paragraph
(blueprint: lem-sfb-proj-fixed-degree-line-quotient). -/
def FixedDegreeCharts {T : Scheme.{u}} (L : T.Modules) (hL : L.IsInvertible)
    (φ : FixedDegreeMap 𝒜 d L hL) (g : T ⟶ (fixedDegreeOpen 𝒜 d).toScheme) : Prop :=
  ∀ a : GradedAlgebra.veroneseGrade 𝒜 d 1,
    ((g ≫ (fixedDegreeOpen 𝒜 d).ι) ⁻¹ᵁ basicOpen 𝒜 a.val.val =
      generatingLocus (fixedDegreeLinearSection 𝒜 d L hL φ a)) ∧
    ∀ (k : ℕ) (b : GradedAlgebra.veroneseGrade 𝒜 d k),
      ((g ≫ (fixedDegreeOpen 𝒜 d).ι).app (basicOpen 𝒜 a.val.val)
        (awayToSection 𝒜 a.val.val
          (HomogeneousLocalization.Away.mk 𝒜 a.property k b.val.val
            (by
              have hb : b.val.val ∈ 𝒜 (k * (d : ℕ)) := b.property
              simpa only [smul_eq_mul, Nat.one_mul] using hb)))) •
          (L.tensorPow k).presheaf.map (homOfLE le_top).op ((φ a.val ^ k) k) =
        (L.tensorPow k).presheaf.map
          (homOfLE (le_top :
            (g ≫ (fixedDegreeOpen 𝒜 d).ι) ⁻¹ᵁ basicOpen 𝒜 a.val.val ≤ ⊤)).op
          (fixedDegreeImage 𝒜 d L hL φ k b)

/-- The fixed-degree classification, including canonical multiplication, degree-zero
compatibility, uniqueness of the entire pair, the converse and the chart formula.
Source: Stacks 01MS, 01N8, 01N9 and equations Ud, psi-d
(blueprint: lem-sfb-proj-fixed-degree-line-quotient).

Proof:
1. The homogeneous sections a freely generate the restricted degree-d twist on D_+(a),
   so it is invertible. Multiply homogeneous fractions on standard opens. The bilinear
   universal property
   lem-pc-sites-sheaf-tensor-bilinear-universal and sheaf-morphism-on-basis construct
   multiplication. The frame a^k from lem-trf-proj-product-chart-twist-frame gives its
   inverse on D_+(a); restriction-tensor-comparison and glue-sheaves-of-modules glue
   these inverses. The zeroth power is the structure sheaf and the first comparison
   is the right unitor. These are the theta isomorphisms.
2. Restrict the canonical sections b/1 and transport by theta. Fraction multiplication,
   addition and the unit show that the resulting eta is graded and unital. Its degree-one
   sections generate the line, and their generating loci are D_+(a).
3. For phi, put W_a = T_s, s = phi_1(a). These opens cover T by generation. Define
   A_(a) -> Gamma(W_a,O_T) by b/a^k -> phi_k(b)/s^k. Equality of fractions is preserved:
   a^N(a^l b-a^k c)=0 becomes the same section identity, and s is a free generator
   on W_a. Addition, multiplication and the degree-zero unit follow by common denominators.
   The affine Hom bijection gives g_a : W_a -> D_+(a).
4. On overlaps the common ring map out of A_(ac) sends z/(ac)^n to
   phi_(2n)(z)/(s tensor t)^n. Restrictions agree by multiplying numerators by c^k
   or a^k. Such maps are determined after restriction from A_(a): c/a becomes a
   unit, with inverse a^2/(ac), and z/(ac)^n=(z/a^(2n))(a^2/(ac))^n.
   Affine Hom uniqueness and scheme-morphism-gluing glue the g_a. Basic-open-intersection
   gives the inverse-image assertion globally.
5. The generators g^*a and s on W_a are the frames of
   lem-trf-proj-generated-pullback-frames. Send r g^*a to r s. The ratio c/a
   proves overlap agreement, and glue-sheaves-of-modules glues this map and its inverse.
6. The pure-section formula of lem-weil-pbc-module-pullback-tensor gives compatibility
   in every positive degree; at zero it is the scalar ring map. The sheaf axiom glues
   the equalities over the arbitrary cover W_a.
7. Any other compatible pair has the same nonvanishing opens, because local ring maps
   preserve and reflect units. Its chart maps are forced by the fractions, so affine
   Hom and gluing uniqueness give the same g. Agreement on generating sections forces
   the same alpha. This is uniqueness among all compatible pairs, independently of charts.
8. Conversely tensor pullback preserves invertibility and the graded ring operations.
   Pulling back the generating sections gives a generating family and the displayed
   compatibility with the identity line comparison. No quasi-compactness is used. -/
theorem fixedDegreeLine_quotient_classification :
    (fixedDegreeLine 𝒜 d).IsInvertible ∧
    ∀ hM : (fixedDegreeLine 𝒜 d).IsInvertible,
    ∃ (θ : ∀ k : ℕ, (fixedDegreeLine 𝒜 d).tensorPow k ≅ fixedDegreeTwist 𝒜 d k)
      (η : FixedDegreeMap 𝒜 d (fixedDegreeLine 𝒜 d) hM),
      HEq (θ 1).hom (ρ_ (fixedDegreeLine 𝒜 d)).hom ∧
      (∀ (k : ℕ) (b : GradedAlgebra.veroneseGrade 𝒜 d k),
        (θ k).hom.app ⊤ (fixedDegreeImage 𝒜 d (fixedDegreeLine 𝒜 d) hM η k b) =
          fixedDegreeCanonicalSection 𝒜 d k b) ∧
      FixedDegreeGenerates 𝒜 d (fixedDegreeLine 𝒜 d) hM η ∧
      (∀ (T : Scheme.{u}) (L : T.Modules) (hL : L.IsInvertible)
        (φ : FixedDegreeMap 𝒜 d L hL), FixedDegreeGenerates 𝒜 d L hL φ →
          (∃! q : Σ g : T ⟶ (fixedDegreeOpen 𝒜 d).toScheme,
            (tensorPullback g).obj (fixedDegreeLine 𝒜 d) ≅ L,
              FixedDegreeCompatible 𝒜 d hM η L hL φ q.1 q.2) ∧
          (∀ (g : T ⟶ (fixedDegreeOpen 𝒜 d).toScheme)
            (α : (tensorPullback g).obj (fixedDegreeLine 𝒜 d) ≅ L),
            FixedDegreeCompatible 𝒜 d hM η L hL φ g α →
              FixedDegreeCharts 𝒜 d L hL φ g)) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ (fixedDegreeOpen 𝒜 d).toScheme),
        ∃ hL : ((tensorPullback g).obj (fixedDegreeLine 𝒜 d)).IsInvertible,
          ∃ φ : FixedDegreeMap 𝒜 d ((tensorPullback g).obj (fixedDegreeLine 𝒜 d)) hL,
            FixedDegreeGenerates 𝒜 d ((tensorPullback g).obj (fixedDegreeLine 𝒜 d)) hL φ ∧
            FixedDegreeCompatible 𝒜 d hM η ((tensorPullback g).obj (fixedDegreeLine 𝒜 d))
              hL φ g (Iso.refl _)) := by
  sorry

end AlgebraicGeometry.Proj
