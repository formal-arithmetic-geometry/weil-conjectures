/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.StandardProjTwistTensor
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Tensor-power and Proj-twist section localizations

Source: Stacks Project, properties.tex, Tag 0AG5 (lemma-proj-quasi-coherent),
the formal localization comparison in its proof, and constructions.tex,
Tags 01MS, 01MT and 01MV (blueprint: lem-sfb-proj-section-tensor-localization-comparison).

The structures below package the specified maps and their equations. In particular,
no map is chosen from a mere existence assertion. The tensor-section localization is
exactly the existing `SectionFractionPresentation`; the other localization is an
additive subgroup of the ordinary `LocalizedModule`, with its exact homogeneous carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite LocalizedModule
open AlgebraicGeometry.Scheme.Modules
open scoped DirectSum

namespace AlgebraicGeometry.Proj

/-- The integer tensor powers used in this comparison: negative powers are positive
powers of the actual sheaf dual. This only combines `tensorPow` and `dual`.
Source: Stacks 01MT and 01PW
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
noncomputable def projSectionTensorPower {X : Scheme.{u}} (L : X.Modules) : ℤ → X.Modules
  | .ofNat n => L.tensorPow n
  | .negSucc n => L.dual.tensorPow (n + 1)

/-- Contract one copy of L against one dual factor, retaining the remaining dual factors.
The associators and braiding bring the pair to the actual evaluation map; no twist or
beta comparison occurs. Source: Stacks 01PW, tensor powers of the dual, and 01MT.
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
noncomputable def projSectionDualContractOne {X : Scheme.{u}} (L : X.Modules) (a : ℕ) :
    L.dual.tensorPow (a + 1) ⊗ L ⟶ L.dual.tensorPow a :=
  (α_ L.dual (L.dual.tensorPow a) L).hom ≫
    L.dual ◁ (β_ (L.dual.tensorPow a) L).hom ≫
    (α_ L.dual L (L.dual.tensorPow a)).inv ≫
    ((β_ L.dual L).hom ≫ dualEvaluation L) ▷ L.dual.tensorPow a ≫
    (λ_ (L.dual.tensorPow a)).hom

/-- Multiply an integer tensor power by one copy of L. In negative degree this is
contraction with the dual; in nonnegative degree it is tensor multiplication.
Source: Stacks 01PW and 01MT
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
noncomputable def projSectionTensorStep {X : Scheme.{u}} (L : X.Modules) :
    ∀ n : ℤ, projSectionTensorPower L n ⊗ L ⟶ projSectionTensorPower L (n + 1)
  | .ofNat a =>
    (β_ (L.tensorPow a) L).hom ≫
      eqToHom (congrArg (projSectionTensorPower L)
        (by omega : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1))
  | .negSucc 0 =>
    projSectionDualContractOne L 0 ≫
      eqToHom (congrArg (projSectionTensorPower L)
        (by omega : (0 : ℤ) = Int.negSucc 0 + 1))
  | .negSucc (a + 1) =>
    projSectionDualContractOne L (a + 1) ≫
      eqToHom (congrArg (projSectionTensorPower L)
        (by omega : Int.negSucc a = Int.negSucc (a + 1) + 1))

/-- Iterated contraction/tensor multiplication of a signed power with a nonnegative power.
Recursion consumes actual L factors using `projSectionTensorStep`, including when the
running exponent passes through zero. It never uses beta or a Proj twist.
Source: Stacks 01PW and 01MT
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
noncomputable def projSectionTensorContract {X : Scheme.{u}} (L : X.Modules) :
    ∀ (e : ℕ) (n : ℤ),
      projSectionTensorPower L n ⊗ L.tensorPow e ⟶ projSectionTensorPower L (n + e)
  | 0, n =>
    (ρ_ (projSectionTensorPower L n)).hom ≫
      eqToHom (congrArg (projSectionTensorPower L) (by omega : n = n + (0 : ℕ)))
  | e + 1, n =>
    (α_ (projSectionTensorPower L n) L (L.tensorPow e)).inv ≫
      projSectionTensorStep L n ▷ L.tensorPow e ≫
      projSectionTensorContract L e (n + 1) ≫
      eqToHom (congrArg (projSectionTensorPower L)
        (by omega : (n + 1) + e = n + (e + 1 : ℕ)))

/-- The usual product of signed tensor powers with a nonnegative tensor power:
`tensorPowAddIso` in nonnegative degree and evaluation contraction in negative degree.
This is defined independently of all beta comparisons and Proj twists.
Source: Stacks 01PW and 01MT
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
noncomputable def projSectionTensorMultiply {X : Scheme.{u}} (L : X.Modules) :
    ∀ (n : ℤ) (e : ℕ),
      projSectionTensorPower L n ⊗ L.tensorPow e ⟶ projSectionTensorPower L (n + e)
  | .ofNat a, e =>
    (L.tensorPowAddIso a e).inv ≫
      eqToHom (congrArg (projSectionTensorPower L)
        (by omega : ((a + e : ℕ) : ℤ) = (a : ℤ) + e))
  | .negSucc a, e => projSectionTensorContract L e (Int.negSucc a)

variable {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- The local comparison data, including the scalar structures, their coefficient-fraction
formulas, the common-power relation, and restriction followed by division. `N` is the
actual direct sum in the theorem below and `ι` is its summand inclusion.
Source: Stacks 0AG5, formal comparison, and 01MS, inverse frames
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
structure ProjSectionLocalizedComparison (F : (Proj 𝒜).Modules)
    (N : Type u) [AddCommGroup N] [Module S N]
    (ι : ∀ n : ℤ, Γ(F ⊗ twist 𝒜 n, ⊤) →+ N)
    (β : ∀ n : ℤ, projSectionTensorPower (twist 𝒜 1) n ≅ twist 𝒜 n)
    (f : S) (hf : f ∈ 𝒜 1) where
  /-- The actual homogeneous degree-zero submodule of the ordinary localization. -/
  Z : AddSubgroup (LocalizedModule.Away f N)
  /-- Its carrier consists exactly of homogeneous fractions of degree zero. -/
  carrier_eq : (Z : Set (LocalizedModule.Away f N)) = degreeZeroFractions
    (fun d : ℕ ↦ (𝒜 d : Set S))
    (fun d : ℕ ↦ Set.range (ι (d : ℤ))) (Submonoid.powers f)
  /-- The coefficient-ring action on the first localization. -/
  scalarZ : Module (HomogeneousLocalization.Away 𝒜 f) Z
  /-- The coefficient-ring action on the tensor-section fraction presentation. -/
  scalarQ : Module (HomogeneousLocalization.Away 𝒜 f)
    (SectionFractionPresentation (twist 𝒜 1) F
      ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
  /-- The actual S_(f)-linear equivalence, using the two specified scalar structures. -/
  θ : @LinearEquiv (HomogeneousLocalization.Away 𝒜 f)
    (HomogeneousLocalization.Away 𝒜 f) _ _ (RingHom.id _) (RingHom.id _) _ _
    Z (SectionFractionPresentation (twist 𝒜 1) F
      ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1))) _ _ scalarZ scalarQ
  /-- Scalar multiplication on Z is multiplication of the two ordinary fractions. -/
  scalarZ_fraction : ∀ (b : ℕ) (v : S) (hv : v ∈ 𝒜 b) (z : Z),
    ((@SMul.smul _ _ scalarZ.toSMul
      (HomogeneousLocalization.Away.mk 𝒜 hf b v (by simpa using hv)) z : Z) :
        LocalizedModule.Away f N) =
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)
        (HomogeneousLocalization.Away.mk 𝒜 hf b v (by simpa using hv))) •
          (z : LocalizedModule.Away f N)
  /-- Restriction of scalars along S_(f) to B_(s), specified on all coefficient fractions. -/
  scalarQ_fraction : ∀ (a b : ℕ) (v : S) (hv : v ∈ 𝒜 b)
      (t : Γ(F ⊗ (twist 𝒜 1).tensorPow a, ⊤)),
    @SMul.smul _ _ scalarQ.toSMul (HomogeneousLocalization.Away.mk 𝒜 hf b v (by simpa using hv))
      (sectionFraction (twist 𝒜 1) F
        ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) a t) =
      sectionFraction (twist 𝒜 1) F
        ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) (a + b)
        (((α_ F ((twist 𝒜 1).tensorPow a) ((twist 𝒜 1).tensorPow b)).hom ≫
          F ◁ ((twist 𝒜 1).tensorPowAddIso a b).inv).app ⊤
            (tmulSection t
              (((eqToHom (congrArg (twist 𝒜) (zero_add (b : ℤ)))) ≫
                (β (b : ℤ)).inv).app ⊤
                  ((unitToTwist hv).app ⊤ (unitSectionsEquiv ⊤ 1)))))
  /-- The required formula t/f^a ↦ beta_a^{-1}(t)/s^a. -/
  fraction : ∀ (a : ℕ) (t : Γ(F ⊗ twist 𝒜 (a : ℤ), ⊤)) (z : Z),
    (z : LocalizedModule.Away f N) =
      mk (ι (a : ℤ) t) (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f) →
    θ z = sectionFraction (twist 𝒜 1) F
      ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) a
      ((F ◁ (β (a : ℤ)).inv).app ⊤ t)
  /-- Every homogeneous numerator gives a fraction in Z. -/
  fraction_mem : ∀ (a : ℕ) (t : Γ(F ⊗ twist 𝒜 (a : ℤ), ⊤)),
    mk (ι (a : ℤ) t) (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f) ∈ Z
  /-- The common-power relation on both sides, without cancelling any denominator. -/
  common_power : ∀ (a b : ℕ) (t : Γ(F ⊗ twist 𝒜 (a : ℤ), ⊤))
      (v : Γ(F ⊗ twist 𝒜 (b : ℤ), ⊤)),
    (mk (ι (a : ℤ) t) (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f) =
        mk (ι (b : ℤ) v) (⟨f ^ b, ⟨b, rfl⟩⟩ : Submonoid.powers f) ↔
      ∃ c : ℕ, f ^ c • (f ^ b • ι (a : ℤ) t - f ^ a • ι (b : ℤ) v) = 0) ∧
    (sectionFraction (twist 𝒜 1) F
        ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) a
        ((F ◁ (β (a : ℤ)).inv).app ⊤ t) =
      sectionFraction (twist 𝒜 1) F
        ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) b
        ((F ◁ (β (b : ℤ)).inv).app ⊤ v) ↔
      ∃ c : ℕ, f ^ c • (f ^ b • ι (a : ℤ) t - f ^ a • ι (b : ℤ) v) = 0)
  /-- Restriction and division by s^a on the existing tensor-fraction presentation. -/
  divide : SectionFractionPresentation (twist 𝒜 1) F
    ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) →+ Γ(F, basicOpen 𝒜 f)
  /-- Its defining division equation on every numerator, without any bijectivity claim. -/
  divide_fraction : ∀ (a : ℕ) (t : Γ(F ⊗ (twist 𝒜 1).tensorPow a, ⊤)),
    tmulSection (divide (sectionFraction (twist 𝒜 1) F
      ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) a t))
      (tensorPowSectionOne (unitToTwist hf) a (basicOpen 𝒜 f)) =
    (F ⊗ (twist 𝒜 1).tensorPow a).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 f ≤ ⊤)).op t
  /-- The composite with θ is t|_D ⊗ f^{-a}, expressed by multiplying by the frame f^a. -/
  restriction_compatibility : ∀ (a : ℕ) (t : Γ(F ⊗ twist 𝒜 (a : ℤ), ⊤)) (z : Z),
    (z : LocalizedModule.Away f N) =
      mk (ι (a : ℤ) t) (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f) →
    tmulSection (divide (θ z)) (twistPowSection (a : ℤ) hf) =
      (F ⊗ twist 𝒜 (a : ℤ)).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 f ≤ ⊤)).op t

/-- Global comparison data. All graded objects in the theorem are actual additive direct
sums; the summand formulas specify the canonical actions, ring map and comparison.
The beta equations fix the canonical iterated multiplication maps in positive degrees
and their evaluation-normalized dual counterparts in negative degrees.
Source: Stacks 01MT, 01MV and the formal comparison in 0AG5
(blueprint: lem-sfb-proj-section-tensor-localization-comparison). -/
structure ProjSectionTensorComparison
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (F : (Proj 𝒜).Modules) [(twist 𝒜 1).IsInvertible]
    (N P : Type u) [AddCommGroup N] [AddCommGroup P] [mN : Module S N]
    (ιN : ∀ n : ℤ, Γ(F ⊗ twist 𝒜 n, ⊤) →+ N)
    (ιP : ∀ n : ℤ, Γ(F ⊗ projSectionTensorPower (twist 𝒜 1) n, ⊤) →+ P) where
  /-- Canonical multiplication identifications in every integer degree. -/
  β : ∀ n : ℤ, projSectionTensorPower (twist 𝒜 1) n ≅ twist 𝒜 n
  /-- The degree-zero unit normalization. -/
  beta_zero : (β 0).hom = unitIsoTwistZero.hom
  /-- Iterated canonical multiplication in nonnegative degrees. -/
  beta_succ : ∀ n : ℕ, (β ((n + 1 : ℕ) : ℤ)).hom =
    (𝟙 (twist 𝒜 1) ⊗ₘ (β (n : ℤ)).hom) ≫
      (twistTensorIso 𝒜 cover 1 (n : ℤ)).hom ≫
      eqToHom (congrArg (twist 𝒜) (by omega : 1 + (n : ℤ) = ((n + 1 : ℕ) : ℤ)))
  /-- Evaluation fixes the identification of the dual with O(-1). -/
  beta_dual :
    (twist 𝒜 1 ◁ ((ρ_ (twist 𝒜 1).dual).inv ≫ (β (-1)).hom)) ≫
      (twistTensorIso 𝒜 cover 1 (-1)).hom ≫ unitIsoTwistZero.inv =
        dualEvaluation (twist 𝒜 1)
  /-- Iterated multiplication of the dual gives all remaining negative powers. -/
  beta_neg_succ : ∀ n : ℕ, (β (Int.negSucc (n + 1))).hom =
    (((ρ_ (twist 𝒜 1).dual).inv ≫ (β (-1)).hom) ⊗ₘ (β (Int.negSucc n)).hom) ≫
      (twistTensorIso 𝒜 cover (-1) (Int.negSucc n)).hom ≫
      eqToHom (congrArg (twist 𝒜)
        (by omega : -1 + Int.negSucc n = Int.negSucc (n + 1)))
  /-- Canonical graded S-action on the actual twisted-section sum N. -/
  actionN : ∀ (e : ℕ) (n : ℤ) (v : S) (hv : v ∈ 𝒜 e)
      (t : Γ(F ⊗ twist 𝒜 n, ⊤)),
    v • ιN n t = ιN (n + e) ((F ◁ twistMul n hv).app ⊤ t)
  /-- The canonical graded coefficient map S → B. -/
  φ : S →+* InvertibleSectionRing (twist 𝒜 1)
  /-- Its value on every homogeneous coefficient fixes it on all of S. -/
  phi_homogeneous : ∀ (e : ℕ) (v : S) (hv : v ∈ 𝒜 e),
    φ v = DirectSum.of (SectionRingComponent (twist 𝒜 1)) e
      (((eqToHom (congrArg (twist 𝒜) (zero_add (e : ℤ)))) ≫ (β (e : ℤ)).inv).app ⊤
        ((unitToTwist hv).app ⊤ (unitSectionsEquiv ⊤ 1)))
  /-- The tensor-section B-action, specified by its homogeneous multiplication formula. -/
  scalarP : Module (InvertibleSectionRing (twist 𝒜 1)) P
  /-- Ordinary tensor multiplication in nonnegative degree and actual dual evaluation
  contraction in negative degree, independent of beta and the twist multiplication maps. -/
  actionP : ∀ (e : ℕ) (n : ℤ) (b : Γ((twist 𝒜 1).tensorPow e, ⊤))
      (p : Γ(F ⊗ projSectionTensorPower (twist 𝒜 1) n, ⊤)),
    @SMul.smul _ _ scalarP.toSMul
        (DirectSum.of (SectionRingComponent (twist 𝒜 1)) e b) (ιP n p) =
      ιP (n + e)
        (((α_ F (projSectionTensorPower (twist 𝒜 1) n)
          ((twist 𝒜 1).tensorPow e)).hom ≫
            F ◁ projSectionTensorMultiply (twist 𝒜 1) n e).app ⊤ (tmulSection p b))
  /-- The direct-sum additive isomorphism induced by id_F tensor beta_n. -/
  γ : P ≃+ N
  /-- Its homogeneous components are exactly the specified beta maps. -/
  gamma_homogeneous : ∀ (n : ℤ)
      (p : Γ(F ⊗ projSectionTensorPower (twist 𝒜 1) n, ⊤)),
    γ (ιP n p) = ιN n ((F ◁ (β n).hom).app ⊤ p)
  /-- Graded S-linearity after restriction of scalars along the canonical S → B. -/
  gamma_linear : ∀ (v : S) (p : P),
    γ (@SMul.smul _ _ scalarP.toSMul (φ v) p) = v • γ p
  /-- Gamma transports exactly the common-power relation with f to the same one with s.
  The image phi(f) is s in degree one, by phi_homogeneous and beta_succ at zero. -/
  common_power_transport : ∀ (f : S) (_hf : f ∈ 𝒜 1) (a b : ℕ)
      (t : Γ(F ⊗ twist 𝒜 (a : ℤ), ⊤)) (v : Γ(F ⊗ twist 𝒜 (b : ℤ), ⊤)),
    (∃ c : ℕ, f ^ c • (f ^ b • ιN (a : ℤ) t - f ^ a • ιN (b : ℤ) v) = 0) ↔
      ∃ c : ℕ, @SMul.smul _ _ scalarP.toSMul (φ f ^ c)
        (@SMul.smul _ _ scalarP.toSMul (φ f ^ b)
            (ιP (a : ℤ) ((F ◁ (β (a : ℤ)).inv).app ⊤ t)) -
          @SMul.smul _ _ scalarP.toSMul (φ f ^ a)
            (ιP (b : ℤ) ((F ◁ (β (b : ℤ)).inv).app ⊤ v))) = 0
  /-- The canonical section has precisely the stated stalk nonvanishing locus. -/
  nonvanishing : ∀ (f : S) (hf : f ∈ 𝒜 1),
    nonvanishingLocus (twist 𝒜 1) ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)) =
      (basicOpen 𝒜 f : Set (Proj 𝒜))
  /-- That same canonical section freely generates O(1) on D_+(f). -/
  generator : ∀ (f : S) (hf : f ∈ 𝒜 1),
    IsFreeGenerator ((twist 𝒜 1).presheaf.map
      (homOfLE (le_top : basicOpen 𝒜 f ≤ ⊤)).op
        ((unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
  /-- Local comparison, scalar and evaluation formulas at every degree-one element. -/
  localization : ∀ (f : S) (hf : f ∈ 𝒜 1),
    Nonempty (ProjSectionLocalizedComparison 𝒜 F N ιN β f hf)

/-- Tensor-power and Proj-twist section localizations agree for every module sheaf.
No compactness, separatedness, quasi-separatedness or quasi-coherence is assumed.
The invertibility instance is concluded first; the subsequent forall over its proof
only permits Lean to use the existing section-ring instance, without adding a hypothesis.

Source: Stacks Project, properties.tex, Tag 0AG5 (lemma-proj-quasi-coherent),
the formal comparison in its proof specialized to degree one; constructions.tex,
Tags 01MS, 01MT and 01MV
(blueprint: lem-sfb-proj-section-tensor-localization-comparison).

Proof:
1. Apply lem-sfb-standard-proj-twist-tensor to the degree-one cover. All twist
   multiplication maps are unital associative isomorphisms and O(1) is invertible.
   Use lem-pc-tensor-dual-invertible for the negative powers and
   lem-pc-sheaf-modules-tensor-closed for the tensor associators and unitors.
2. On D_+(g), g^n and g^{-n} are inverse frames. Use
   lem-weil-pbc-proj-standard-open-inclusion for localization restrictions and
   lem-weil-pbc-sheaf-morphism-on-basis to extend these frames from the standard basis.
3. Tensor the frame and its dual to obtain the tensor-power frames. On overlaps,
   g = (g/h)h, so the frames on both sides change by (g/h)^n, for all integer n.
   Glue their identifications to beta_n; positive powers are iterated multiplication,
   and the negative identification is fixed by evaluation.
4. The beta maps preserve multiplication: on every frame both products give the
   frame in degree a+b, including mixed signs by evaluation. The induced phi is a
   graded unital ring map; tensoring beta with F and taking direct sums gives gamma.
   Check gamma(phi(v)p)=v gamma(p) on the cover, hence globally by sheaf separation.
5. Apply lem-trf-proj-twist-section-basic-open with W_1=X, supplied by step 1,
   to obtain X_s=D_+(f). The canonical section is f/1, the free frame from step 2.
6. Set delta=gamma^{-1}. It satisfies delta(f^c t)=s^c delta(t).
   Send t/f^a to delta_a(t)/s^a. The common-power relation is carried by delta to
   s^c(s^b delta_a(t)-s^a delta_b(v))=0 and back by gamma. No power is cancelled.
   Thus this is a well-defined additive bijection, with the displayed inverse formula.
7. Coefficient fractions v/f^b act by phi(v)/s^b. The same common-power argument
   makes this action well-defined; the homogeneous multiplication formula proves
   theta is S_(f)-linear, so its inverse is linear too.
8. On D_+(f), divide tensor-power numerators by the free frame s^a. The fraction
   relations vanish after this division, giving the additive divide map. Since beta_a
   carries this frame to f^a, divide composed with theta is t|_D tensor f^{-a},
   equivalently the displayed equation after tensoring with f^a. This is a formal
   comparison only; no bijectivity of division or finiteness of the cover is used.
-/
theorem projSectionTensorLocalizationComparison
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (F : (Proj 𝒜).Modules) :
    (twist 𝒜 1).IsInvertible ∧
    ∀ [(twist 𝒜 1).IsInvertible],
      ∃ mN : Module S (⨁ n : ℤ, Γ(F ⊗ twist 𝒜 n, ⊤)),
        @Nonempty (ProjSectionTensorComparison 𝒜 cover F
          (⨁ n : ℤ, Γ(F ⊗ twist 𝒜 n, ⊤))
          (⨁ n : ℤ, Γ(F ⊗ projSectionTensorPower (twist 𝒜 1) n, ⊤))
          (fun n ↦ DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) n)
          (fun n ↦ DirectSum.of
            (fun k : ℤ ↦ Γ(F ⊗ projSectionTensorPower (twist 𝒜 1) k, ⊤)) n)
          (mN := mN)) := by
  sorry

end AlgebraicGeometry.Proj
