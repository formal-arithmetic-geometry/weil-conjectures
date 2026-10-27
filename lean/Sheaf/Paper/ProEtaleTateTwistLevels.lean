/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Sheaf.Paper.TateTwistFiniteLocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.PadicIntegersInvertEll
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

import Sheaf.Paper.ConstantZModScalarTensor
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-! # Finite levels and integral and rational Tate twist objects

Source: blueprint `sk-def-sp-tate-twist`. The index n denotes exponent n+1.
The integral levels use the finite quotient tensor with the roots, restricted
along O_X -> B_X. The integral object is their limit in O_X-modules, and the
rational object is its specified extension of scalars. These are the original
constructions re-exported by `ProEtaleTateTwists`, with unchanged data and names.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The standard size witness at the coefficient universe, used with explicit universes.
This merely exposes Mathlib's existing small-category witness to instance search;
it avoids selecting an unrelated instance with an unconstrained extra universe.
Source: def-weil-size-convention and the small pro-etale site
(blueprint: sk-def-sp-tate-twist). -/
instance spProEtEssentiallySmall : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} X.ProEt

/-- The finite twist uses the unique unital quotient homomorphism to A.
The positive index r represents the annihilating exponent r+1; its vanishing
on 1 is equivalent to annihilation of every A-module scalar.
Source: blueprint finite twist formula (blueprint: sk-def-sp-tate-twist). -/
def spFiniteTwist (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : A) = 0) :=
  Scheme.tateFiniteLine X ℓ A r
    (ZMod.castHom (ringChar.dvd (by simpa only [Nat.cast_pow] using hA)) A)

/-- Every finite twist is locally free of rank one, including the zero coefficient ring.
Source: blueprint finite local-generator paragraph (blueprint: sk-def-sp-tate-twist).
Proof: clause 1 of det-def-sp-tate-twist-locally-free provides a pro-etale cover
and a generator of the root module at exponent r+1. Tensor its normalized
isomorphism with A along the unique quotient scalar map. Extension of scalars
sends the free rank-one root module to the free rank-one A module. Local
freeness follows by descent; this also works for the zero ring. -/
theorem spFiniteTwist_locallyFree
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (hA : (ℓ ^ (r + 1) : A) = 0) :
    (spFiniteTwist X ℓ A r hA).IsFiniteLocallyFreeOfRank 1 := by
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, hf⟩ := Scheme.tateTwist_finite_locallyFree X ℓ
  obtain ⟨a, _, hL, _⟩ := hf A r (fun b ↦ by
    rw [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul])
  have ha : a = ZMod.castHom
      (ringChar.dvd (by simpa only [Nat.cast_pow] using hA)) A := Subsingleton.elim _ _
  simpa only [spFiniteTwist, ha] using hL

set_option backward.isDefEq.respectTransparency false in
/-- The two recorded integer-ring models agree as subrings of the fixed finite field.
Source: blueprint coefficient convention and def-weil-l-adic-coefficient-extension
(blueprint: sk-def-sp-tate-twist).
Proof: the coefficient-extension absolute value and the norm restricted from the
fixed algebraic closure both extend the p-adic absolute value. Uniqueness in
lem-weil-l-adic-extension-absolute-value makes them equal. The DVR witness
characterizes coefficientExtensionIntegers by value at most one, precisely the
membership predicate of PadicAlgCl.integers. Extensionality gives equality. -/
theorem spIntegers_eq (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Padic.coefficientExtensionIntegers ℓ E.1 = (PadicAlgCl.integers ℓ E.1).toSubring := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra (Padic ℓ) E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          norm_algebraMap'] }
  have hmem (x : E.1) : x ∈ Padic.coefficientExtensionIntegers ℓ E.1 ↔
      (Padic.coefficientExtensionAbsoluteValue ℓ E.1) x ≤ 1 :=
    (Padic.extension_integers_dvr ℓ E.1
      (Padic.coefficientExtensionAbsoluteValue ℓ E.1)
      (spectralNorm_extends (K := Padic ℓ) (L := E.1))).choose_spec.choose_spec.1 x
  apply Subring.ext
  intro x
  rw [hmem x]
  change spectralNorm (Padic ℓ) E.1 x ≤ 1 ↔
    ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊ ≤ 1
  rw [← NormedAlgebra.norm_eq_spectralNorm (Padic ℓ)]
  change ‖algebraMap E.1 (PadicAlgCl ℓ) x‖ ≤ 1 ↔
    ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊ ≤ 1
  simpa only [NNReal.coe_one, coe_nnnorm] using
    (NNReal.coe_le_coe (r₁ := ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊) (r₂ := 1))

/-- The cofinal ell-power ideals in the ring of integers.
Source: blueprint integral-twist formula (blueprint: sk-def-sp-tate-twist). -/
def spTateEllIdeal (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Ideal (PadicAlgCl.integers ℓ E.1) :=
  Ideal.span { (ℓ : PadicAlgCl.integers ℓ E.1) ^ (n + 1) }

/-- The finite coefficient B_E,n+1 = O_E / ell^(n+1).
Source: blueprint integral-twist formula (blueprint: sk-def-sp-tate-twist). -/
abbrev spEllQuotient (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (PadicAlgCl.integers ℓ E.1) ⧸ spTateEllIdeal ℓ E n

/-- The integer-ring topology inherited from its specified embedding in Qbar.
Source: blueprint coefficient convention (blueprint: sk-def-sp-tate-twist). -/
@[instance_reducible] def spIntegersTopology (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    TopologicalSpace (PadicAlgCl.integers ℓ E.1) :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  inferInstance

/-- Positive ell-power quotients are finite and their quotient maps are continuous
for the discrete target topology.
Source: blueprint cofinal-ideal paragraph (blueprint: sk-def-sp-tate-twist).
Proof: write ell = v*pi^e with v a unit and e positive, using the DVR of the
coefficient-extension node. Then (ell^(n+1)) = (pi^(e*(n+1))). Finiteness is the
finite-quotient theorem for that positive exponent. The ideal is open in the
valuation topology, so each quotient fibre is open. This is continuity into the
discrete quotient, for the same extending valuation. -/
theorem spEllQuotient_finite_continuous (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) :
    Finite (spEllQuotient ℓ E n) ∧
    @Continuous _ _ (spIntegersTopology ℓ E) ⊥
      (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedSpace (Padic ℓ) E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let : ProperSpace E.1 := FiniteDimensional.proper (Padic ℓ) E.1
  let : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  let : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  have hq : Continuous (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) :=
    PadicAlgCl.continuous_integersModPowMk ℓ E.1 (n + 1)
  refine ⟨?_, hq⟩
  have hclosed : IsCompact (PadicAlgCl.integers ℓ E.1 : Set E.1) := by
    have heq : (PadicAlgCl.integers ℓ E.1 : Set E.1) = Metric.closedBall 0 1 := by
      ext x
      change ‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
      rw [dist_zero_right]
      exact NNReal.coe_le_coe.symm
    rw [heq]
    exact isCompact_closedBall 0 1
  have : CompactSpace (PadicAlgCl.integers ℓ E.1) :=
    isCompact_iff_compactSpace.mp hclosed
  have himage : IsCompact (Set.univ : Set (spEllQuotient ℓ E n)) := by
    rw [← Set.range_eq_univ.mpr (Ideal.Quotient.mk_surjective
      (I := spTateEllIdeal ℓ E n))]
    exact isCompact_range hq
  have : CompactSpace (spEllQuotient ℓ E n) := ⟨himage⟩
  exact finite_of_compact_of_discrete

/-- The discrete finite coefficient as a continuous-function condensed ring.
It is canonically the constant finite ring sheaf, since continuous maps to a
finite discrete set are locally constant.
Source: blueprint finite-coefficient convention (blueprint: sk-def-sp-tate-twist). -/
def spEllPointRing (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing
  Profinite.continuousMapRingSheaf (spEllQuotient ℓ E n)

/-- The abelian ring object underlying the finite condensed coefficient.
Source: blueprint finite-coefficient convention (blueprint: sk-def-sp-tate-twist). -/
abbrev spEllPointRingObj (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (spEllPointRing ℓ E n)

set_option backward.isDefEq.respectTransparency false in
/-- The actual continuous quotient map on condensed coefficients.
Source: blueprint coordinatewise quotient action (blueprint: sk-def-sp-tate-twist). -/
def spEllPointReduction (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ spEllPointRingObj ℓ E n :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk (spTateEllIdeal ℓ E n))
        (spEllQuotient_finite_continuous ℓ E n).2)

attribute [local irreducible] spEllPointReduction

set_option backward.isDefEq.respectTransparency false in
/-- The condensed finite quotient map preserves the ring structure.
Source: blueprint quotient action (blueprint: sk-def-sp-tate-twist).
Proof: its maps are postcomposition with a ring homomorphism, so preserve one
and multiplication sectionwise; forgetting to abelian sheaves retains these laws. -/
@[instance] theorem spEllPointReduction_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllPointReduction.{u} ℓ E n) := by
  unfold spEllPointReduction
  infer_instance

/-- The pulled-back reduction O_E,X -> (B_E,n+1)_X.
Source: blueprint quotient action (blueprint: sk-def-sp-tate-twist). -/
abbrev spEllReduction (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  coefficientMap.{u} (spEllPointReduction.{u} ℓ E n) X

/-- Successive positive ell-power ideals are nested.
Source: blueprint quotient transitions (blueprint: sk-def-sp-tate-twist).
Proof: ell^(n+2) = ell^(n+1)*ell lies in the ideal generated by ell^(n+1).
The span universal property gives the inclusion. -/
theorem spTateEllIdeal_succ_le (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spTateEllIdeal ℓ E (n + 1) ≤ spTateEllIdeal ℓ E n := by
  exact Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (ℓ : PadicAlgCl.integers ℓ E.1) (Nat.le_succ (n + 1)))

/-- The finite coefficient reduction at the point, induced by the identity on O_E.
Source: blueprint quotient transitions (blueprint: sk-def-sp-tate-twist). -/
def spEllPointTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllPointRingObj.{u} ℓ E (n + 1) ⟶ spEllPointRingObj ℓ E n :=
  letI : TopologicalSpace (spEllQuotient ℓ E (n + 1)) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E (n + 1)) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E (n + 1)) := DiscreteTopology.topologicalRing
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Ideal.Quotient.factor (spTateEllIdeal_succ_le ℓ E n)) continuous_of_discreteTopology)

attribute [local irreducible] spEllPointTransition

set_option backward.isDefEq.respectTransparency false in
/-- Finite reduction preserves one and multiplication.
Source: blueprint quotient transitions (blueprint: sk-def-sp-tate-twist).
Proof: it is postcomposition with the quotient ring homomorphism; ring operations
on continuous functions are pointwise. -/
@[instance] theorem spEllPointTransition_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllPointTransition.{u} ℓ E n) := by
  unfold spEllPointTransition
  infer_instance

/-- The finite twist, regarded as an O_E,X-module through the quotient map.
Since mu is killed by ell^(n+1), B_X tensor_Z mu is precisely its extension
from (Z/ell^(n+1))_X to B_X.
Source: blueprint finite-level integral twist (blueprint: sk-def-sp-tate-twist). -/
def spIntegralTwistLevel (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (Mod.comap (spEllReduction X ℓ E n)).obj
    ((Mod.free (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X)).obj
      (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))

private theorem spFreeTensor_linear
    {C : Type*} [Category C] [MonoidalCategory C]
    {R B D : C} [MonObj R] [MonObj B] [MonObj D]
    (p : R ⟶ B) [IsMonHom p] (q : R ⟶ D) [IsMonHom q]
    (r : B ⟶ D) [IsMonHom r] (h : p ≫ r = q)
    {U V : C} (v : U ⟶ V) :
    ∃! f : (Mod.comap p).obj ((Mod.free B).obj U) ⟶
        (Mod.comap q).obj ((Mod.free D).obj V), f.hom = r ⊗ₘ v := by
  let f : (Mod.comap p).obj ((Mod.free B).obj U) ⟶
      (Mod.comap q).obj ((Mod.free D).obj V) := Mod.homMk (r ⊗ₘ v) (by
    change (p ▷ (B ⊗ U) ≫ (α_ B B U).inv ≫ MonObj.mul ▷ U) ≫ (r ⊗ₘ v) =
      R ◁ (r ⊗ₘ v) ≫ q ▷ (D ⊗ V) ≫ (α_ D D V).inv ≫ MonObj.mul ▷ V
    have hm : (p ⊗ₘ 𝟙 B) ≫ MonObj.mul ≫ r =
        (q ⊗ₘ r) ≫ MonObj.mul := by
      rw [IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, h, Category.id_comp]
    calc
      _ = (α_ R B U).inv ≫ (((p ⊗ₘ 𝟙 B) ≫ MonObj.mul ≫ r) ⊗ₘ v) := by
        simp only [Category.assoc]
        rw [associator_inv_naturality_left_assoc]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
      _ = (α_ R B U).inv ≫ (((q ⊗ₘ r) ≫ MonObj.mul) ⊗ₘ v) := by rw [hm]
      _ = (q ⊗ₘ (r ⊗ₘ v)) ≫ (α_ D D V).inv ≫ MonObj.mul ▷ V := by
        rw [associator_inv_naturality_assoc]
        simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      _ = _ := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id])
  refine ⟨f, rfl, ?_⟩
  intro g hg
  exact Mod.hom_ext _ _ hg

set_option backward.isDefEq.respectTransparency false in
/-- The normalized transition is linear over O_E,X.
Source: blueprint u tensor a -> u^ell tensor a-bar (blueprint: sk-def-sp-tate-twist).
Proof: reduce the scalar factor and apply the root power transition. Both commute
with restrictions. Reduction commutes with the O_E action, so the tensor map is
O_E-linear. The forgetful functor is faithful, giving uniqueness. -/
theorem spIntegralLevelTransition_existsUnique (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) :
    ∃! f : spIntegralTwistLevel X ℓ E (n + 1) ⟶ spIntegralTwistLevel X ℓ E n,
      f.hom = coefficientMap.{u} (spEllPointTransition ℓ E n) X ⊗ₘ
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) := by
  have hq : spEllReduction X ℓ E (n + 1) ≫
      coefficientMap.{u} (spEllPointTransition ℓ E n) X = spEllReduction X ℓ E n := by
    rw [← coefficientMap_comp]
    apply congrArg (fun f ↦ coefficientMap.{u} f X)
    unfold spEllPointReduction spEllPointTransition
    rw [← Functor.map_comp]
    rfl
  exact spFreeTensor_linear (spEllReduction X ℓ E (n + 1)) (spEllReduction X ℓ E n)
    (coefficientMap.{u} (spEllPointTransition ℓ E n) X) hq
    (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.le_succ (n + 1))))

/-- The specified finite-level transition, with its reduction and Kummer factors.
Source: blueprint integral inverse system (blueprint: sk-def-sp-tate-twist). -/
def spIntegralLevelTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spIntegralTwistLevel X ℓ E (n + 1) ⟶ spIntegralTwistLevel X ℓ E n :=
  (spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose

/-- The positive finite-level twist system in O_E,X-modules.
Source: blueprint integral inverse system (blueprint: sk-def-sp-tate-twist). -/
def spIntegralTwistSystem (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ℕᵒᵖ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  Functor.ofOpSequence (spIntegralLevelTransition X ℓ E)

/-- The finite-level twist is the displayed constant-ring scalar extension.
Source: blueprint finite-level formula (blueprint: sk-def-sp-tate-twist).
Proof: a finite discrete B has continuous-function condensed sheaf equal to its
constant sheaf: a section is a finite clopen partition labelled by B. Pullback
from the point preserves this description, including the ring operations.
For an N-torsion abelian sheaf M, B tensor_Z M is B tensor_(Z/N) M whenever N*B=0:
the integer balancing relations already imply the Z/N balancing relations.
Apply this with N=ell^(n+1) and M=mu_N, using the recorded root module action.
The inclusion of the ideal generator gives N=0 in the quotient. These comparisons
commute with reduction of B and the root power maps, since each map applies to
its indicated tensor factor. Thus the actual integral system has exactly the
finite levels and transitions in the blueprint, with no replacement of the roots. -/
theorem spIntegralTwistLevel_comparison (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    ∃ a : ZMod (ℓ ^ (n + 1)) →+* ULift.{u + 1} (spEllQuotient ℓ E n),
      Nonempty ((spIntegralTwistLevel X ℓ E n).X ≅
        (SheafOfModules.toSheaf _).obj
          (Scheme.tateFiniteLine X ℓ (ULift.{u + 1} (spEllQuotient ℓ E n)) n a)) := by
  let : CommRing (PadicAlgCl.integers ℓ E.1) := inferInstance
  let B := spEllQuotient ℓ E n
  let : CommRing B := Ideal.Quotient.commRing _
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := DiscreteTopology.topologicalRing
  let : Finite B := (spEllQuotient_finite_continuous ℓ E n).1
  have hB : (ℓ ^ (n + 1) : B) = 0 := by
    have h : (Ideal.Quotient.mk (spTateEllIdeal ℓ E n)) (ℓ ^ (n + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_pow, map_natCast] using h
  have hB' : ((ℓ ^ (n + 1) : ℕ) : B) = 0 :=
    (Nat.cast_pow ℓ (n + 1)).trans hB
  let : CharP B (ringChar B) := ringChar.charP B
  let b : ZMod (ℓ ^ (n + 1)) →+* B :=
    ZMod.castHom (ringChar.dvd (R := B) hB') B
  let a : ZMod (ℓ ^ (n + 1)) →+* ULift.{u + 1} B :=
    ULift.ringEquiv.symm.toRingHom.comp b
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  obtain ⟨eX, _⟩ := finiteDiscreteSchemeRing_constant.{u} B X eR heR
  obtain ⟨eT⟩ := Scheme.constantZMod_scalarTensor X ℓ n (ULift.{u + 1} B) a
    (Scheme.purTwistRootsModule X ℓ n)
  refine ⟨a, ⟨?_⟩⟩
  exact (eX.symm ⊗ᵢ
    Iso.refl (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) ≪≫ eT

/-- O_E,X(1), the inverse limit with the pulled-back continuous integer coefficients.
Source: blueprint Tate twists, integral formula (blueprint: sk-def-sp-tate-twist). -/
def spIntegralTwist (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X) :=
  limit (spIntegralTwistSystem X ℓ E)


/-- E_X(1), extension of the integral twist along the continuous inclusion O_E -> E.
Source: blueprint Tate twists, rational formula (blueprint: sk-def-sp-tate-twist). -/
def spRationalTwist (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X) :=
  (Mod.extendScalars.{u + 1, u + 2}
    (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (padicIntegersToPadicSubfield X ℓ E)).obj
    (spIntegralTwist X ℓ E)

end AlgebraicGeometry.ProEtale
