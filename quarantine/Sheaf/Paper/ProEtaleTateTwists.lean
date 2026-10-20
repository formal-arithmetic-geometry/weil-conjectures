/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Sheaf.Paper.TateTwistLocallyFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.PadicIntegersInvertEll
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Tate twists with pulled-back condensed coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-def-sp-tate-twist/_section.md` (blueprint: sk-def-sp-tate-twist).

All finite levels are positive: the natural-number index n denotes exponent n+1.
The integral levels use B_X tensor_Z mu, restricted along O_X -> B_X. The
finite-level comparison identifies this with B_X tensor_(Z/ell^(n+1)) mu.
Limits are formed in O_X-modules.

## Main definitions

- `spFiniteTwist`: finite scalar extension and its Kummer identifications.
- `spIntegralTwist`: the positive finite-quotient inverse limit.
- `spRationalTwist`: extension of scalars that inverts ell.
- `spQbarTwist`: the specified sheafified field colimit with its canonical action.
- `spSignedTwist` and `spComplexTwist`: signed lines and unbounded derived twists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

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
  sorry

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
  sorry

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
  sorry

/-- The discrete finite coefficient as a continuous-function condensed ring.
It is canonically the constant finite ring sheaf, since continuous maps to a
finite discrete set are locally constant.
Source: blueprint finite-coefficient convention (blueprint: sk-def-sp-tate-twist). -/
def spEllPointRing (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  Profinite.continuousMapRingSheaf (spEllQuotient ℓ E n)

/-- The abelian ring object underlying the finite condensed coefficient.
Source: blueprint finite-coefficient convention (blueprint: sk-def-sp-tate-twist). -/
abbrev spEllPointRingObj (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj (spEllPointRing ℓ E n)

/-- The actual continuous quotient map on condensed coefficients.
Source: blueprint coordinatewise quotient action (blueprint: sk-def-sp-tate-twist). -/
def spEllPointReduction (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    Profinite.padicIntegersRingObj.{u} ℓ E.1 ⟶ spEllPointRingObj ℓ E n :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk (spTateEllIdeal ℓ E n))
        (spEllQuotient_finite_continuous ℓ E n).2)

/-- The condensed finite quotient map preserves the ring structure.
Source: blueprint quotient action (blueprint: sk-def-sp-tate-twist).
Proof: its maps are postcomposition with a ring homomorphism, so preserve one
and multiplication sectionwise; forgetting to abelian sheaves retains these laws. -/
@[instance] theorem spEllPointReduction_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllPointReduction.{u} ℓ E n) := by
  sorry

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
  sorry

/-- The finite coefficient reduction at the point, induced by the identity on O_E.
Source: blueprint quotient transitions (blueprint: sk-def-sp-tate-twist). -/
def spEllPointTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllPointRingObj.{u} ℓ E (n + 1) ⟶ spEllPointRingObj ℓ E n :=
  letI : TopologicalSpace (spEllQuotient ℓ E (n + 1)) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E (n + 1)) := ⟨rfl⟩
  letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
  letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Ideal.Quotient.factor (spTateEllIdeal_succ_le ℓ E n)) continuous_of_discreteTopology)

/-- Finite reduction preserves one and multiplication.
Source: blueprint quotient transitions (blueprint: sk-def-sp-tate-twist).
Proof: it is postcomposition with the quotient ring homomorphism; ring operations
on continuous functions are pointwise. -/
@[instance] theorem spEllPointTransition_isMonHom
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsMonHom (spEllPointTransition.{u} ℓ E n) := by
  sorry

/-- The finite twist, regarded as an O_E,X-module through the quotient map.
Since mu is killed by ell^(n+1), B_X tensor_Z mu is precisely its extension
from (Z/ell^(n+1))_X to B_X.
Source: blueprint finite-level integral twist (blueprint: sk-def-sp-tate-twist). -/
def spIntegralTwistLevel (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  (Mod.comap (spEllReduction X ℓ E n)).obj
    ((Mod.free (condensedRingObj.{u} (spEllPointRingObj ℓ E n) X)).obj
      (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))))

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
  sorry

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
  sorry

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

/-- The integral coefficient inclusion is the unique ring map over E_X -> F_X.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: the inclusion E -> F preserves the extending valuation, so restrict it to
O_E -> O_F and apply continuous-function condensation and p_X^*. The square
commutes before pullback and hence afterwards. The inclusion O_F,X -> F_X is
monic: it is monic on profinite tests and p_X^* is left exact. Cancel it to obtain
uniqueness. This does not choose an arbitrary scalar map. -/
theorem spIntegersMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    ∃! φ : condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X ⟶
        condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X,
      IsMonHom φ ∧
      φ ≫ padicIntegersToPadicSubfield X ℓ F =
        padicIntegersToPadicSubfield X ℓ E ≫
          coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X := by
  sorry

/-- Pullback of the continuous inclusion O_E -> O_F, uniquely fixed by E -> F.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist). -/
def spIntegersMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ E.1) X ⟶
      condensedRingObj.{u} (Profinite.padicIntegersRingObj.{u} ℓ F.1) X :=
  (spIntegersMap_existsUnique X ℓ h).exists.choose

/-- The induced quotient inclusion is characterized by the two integral reductions.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: the integral ring inclusion sends ell^(n+1) to ell^(n+1), so descends to
the finite quotients. Condense and pull back that quotient map. The quotient
reduction is an epimorphism, so its commuting square determines the map uniquely. -/
theorem spEllMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (n : ℕ) :
    ∃! φ : condensedRingObj.{u} (spEllPointRingObj ℓ E n) X ⟶
        condensedRingObj.{u} (spEllPointRingObj ℓ F n) X,
      spEllReduction X ℓ E n ≫ φ =
        spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
  sorry

/-- The finite quotient inclusion along E -> F, fixed by the integral reductions.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist). -/
def spEllMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (n : ℕ) :
    condensedRingObj.{u} (spEllPointRingObj ℓ E n) X ⟶
      condensedRingObj.{u} (spEllPointRingObj ℓ F n) X :=
  (spEllMap_existsUnique X ℓ h n).exists.choose

/-- The integral transition is uniquely specified on every positive quotient twist.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: tensor each finite quotient inclusion with the identity on the root sheaf.
These maps commute with reduction and Kummer transition. The forgetful functor
creates limits, so the compatible finite-level maps give a unique map of limits. -/
theorem spIntegralTwistMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    ∃! f : (spIntegralTwist X ℓ E).X ⟶ (spIntegralTwist X ℓ F).X,
      ∀ n : ℕ, f ≫ (limit.π (spIntegralTwistSystem X ℓ F) (op n)).hom =
        (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom ≫
          (spEllMap X ℓ h n ⊗ₘ
            𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1)))) := by
  sorry

/-- Integral extension transition: the coefficient inclusion on every root level.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist). -/
def spIntegralTwistMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (spIntegralTwist X ℓ E).X ⟶ (spIntegralTwist X ℓ F).X :=
  (spIntegralTwistMap_existsUnique X ℓ h).exists.choose

/-- Localization gives the unique rational transition with the prescribed tensor formula.
Source: blueprint rational field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: tensor the maps E_X -> F_X and O_E,X(1) -> O_F,X(1). The integral map is
semilinear because its projections are tensor maps linear in the scalar factor.
The coefficient square makes the tensor map balanced. Descend through the defining
coequalizer of extension of scalars. Its epimorphic projection gives uniqueness. -/
theorem spRationalTwistMap_existsUnique {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    ∃! f : (spRationalTwist X ℓ E).X ⟶ (spRationalTwist X ℓ F).X,
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) ≫ f =
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
          spIntegralTwistMap X ℓ h) ≫
            Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F) := by
  sorry

/-- The rational field-extension transition, with its specified localization normalization.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist). -/
def spRationalTwistMap {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (spRationalTwist X ℓ E).X ⟶ (spRationalTwist X ℓ F).X :=
  (spRationalTwistMap_existsUnique X ℓ h).exists.choose

/-- The identity inclusion induces the identity transition.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: identity maps have the required finite projections and localization formula.
Apply uniqueness first to the integral limits and then to the rational tensor quotient. -/
theorem spRationalTwistMap_id (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    spRationalTwistMap X ℓ (le_refl E) = 𝟙 _ := by
  sorry

/-- Field-extension transitions compose.
Source: blueprint field-extension transitions (blueprint: sk-def-sp-tate-twist).
Proof: the two composites have the same maps on finite root tensors because the
coefficient inclusions compose. Joint injectivity of limit projections gives the
integral identity. The localization pure-tensor formula then gives the rational
identity, by uniqueness through the tensor coequalizer. -/
theorem spRationalTwistMap_comp {E F H : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) (k : F ≤ H) :
    spRationalTwistMap X ℓ (h.trans k) =
      spRationalTwistMap X ℓ h ≫ spRationalTwistMap X ℓ k := by
  sorry

/-- The specified rational transitions are semilinear for the coefficient inclusions.
Source: blueprint scalar-action paragraph (blueprint: sk-def-sp-tate-twist).
Proof: each finite-level transition tensors a coefficient homomorphism with the
identity on roots, hence is semilinear. The integral limit projections jointly
reflect equality, so the integral map is semilinear. Apply the localization
normalization of spRationalTwistMap on pure tensors and cancel its epimorphic
projection to obtain the displayed action identity. -/
theorem spRationalTwistMap_semilinear {E F : PadicAlgCl.FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    Mod.act (spRationalTwist X ℓ E).X ≫ spRationalTwistMap X ℓ h =
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) X ⊗ₘ
        spRationalTwistMap X ℓ h) ≫ Mod.act (spRationalTwist X ℓ F).X := by
  sorry

/-- The specified diagram of rational twists on the small directed poset of finite fields.
Source: blueprint algebraic-closure colimit (blueprint: sk-def-sp-tate-twist). -/
def spRationalTwistDiagram : PadicAlgCl.FiniteIntermediateField ℓ ⥤
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} where
  obj E := (spRationalTwist X ℓ E).X
  map f := spRationalTwistMap X ℓ (leOfHom f)
  map_id E := spRationalTwistMap_id X ℓ E
  map_comp f g := spRationalTwistMap_comp X ℓ (leOfHom f) (leOfHom g)

/-- The underlying algebraic-closure twist is the sheafified abelian colimit, not a
sectionwise union without sheafification.
Source: blueprint algebraic-closure colimit (blueprint: sk-def-sp-tate-twist). -/
def spQbarTwistAb : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  colimit (C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (spRationalTwistDiagram X ℓ)

/-- The colimit's action is uniquely determined by multiplying at a common finite field.
Source: blueprint scalar-action paragraph (blueprint: sk-def-sp-tate-twist).
Proof: on sectionwise presheaf colimits choose a common finite extension H of E and F.
Multiply the two images there. The tensor normalization of the rational transitions
makes them semilinear, so further extension preserves this product. Any two common
extensions map into their finite compositum, giving independence of representatives.
The module identities hold at a common field. Sheafify the action. The coefficient
colimit is p_X^* Qbar by the sectionwise finite-subextension union and preservation
of colimits by the left adjoint p_X^*. Tensor preserves colimits and sheafification,
so the stagewise formulas uniquely determine the resulting action. -/
theorem spQbarTwistAction_existsUnique :
    ∃! a : ModObj (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X) (spQbarTwistAb X ℓ),
      ∀ (E F H : PadicAlgCl.FiniteIntermediateField ℓ) (hE : E ≤ H) (hF : F ≤ H),
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X ⊗ₘ
          colimit.ι (spRationalTwistDiagram X ℓ) F) ≫ a.smul =
        (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ hE) X ⊗ₘ
          spRationalTwistMap X ℓ hF) ≫
            Mod.act (spRationalTwist X ℓ H).X ≫
              colimit.ι (spRationalTwistDiagram X ℓ) H := by
  sorry

/-- Qbar_X(1), with the uniquely specified action on its sheafified colimit.
Source: blueprint algebraic-closure colimit and action (blueprint: sk-def-sp-tate-twist). -/
def spQbarTwist : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  { X := spQbarTwistAb X ℓ
    mod := (spQbarTwistAction_existsUnique X ℓ).exists.choose }
/-- The canonical Kummer identification for finite coefficients is fixed on pure tensors.
Source: blueprint finite-coefficient independence paragraph
(blueprint: sk-def-sp-tate-twist).
Proof: clause 2 of det-def-sp-tate-twist-locally-free supplies the map with this
formula and says that it is an isomorphism. On a cover with compatible root
generators it is the identity of A. Pure tensors locally generate the sheafified
scalar extension, so the formula determines the morphism uniquely. This includes
r=n; composing the formulas gives the formula for a composite root power. Thus
uniqueness also supplies the identity and composition coherence. -/
theorem spFiniteKummer_existsUnique
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    ∃! k : Scheme.tateFiniteLine X ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
          (ZMod (ℓ ^ (r + 1))))) ⟶ Scheme.tateFiniteLine X ℓ A r a,
      IsIso k ∧
      ∀ (V : X.ProEt) (b : (Scheme.tateFiniteCoefficient X A).obj.obj (op V))
        (x : (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
        k.val.app (op V)
          (Scheme.tateFiniteTensor X ℓ A n
            (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
              (ZMod (ℓ ^ (r + 1))))) V b x) =
          Scheme.tateFiniteTensor X ℓ A r a V b
            ((Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
              (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
              (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x) := by
  sorry

/-- The actual finite-coefficient Kummer identification, uniquely specified on pure tensors.
The unital quotient homomorphism a is unique, so it adds no coefficient choice.
Source: blueprint finite-coefficient independence (blueprint: sk-def-sp-tate-twist). -/
def spFiniteKummer
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    Scheme.tateFiniteLine X ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
          (ZMod (ℓ ^ (r + 1))))) ⟶ Scheme.tateFiniteLine X ℓ A r a :=
  (spFiniteKummer_existsUnique X ℓ A r n hrn a).exists.choose

/-- Equal-exponent Kummer identification is the identity, after the canonical equality
of the two quotient scalar maps. HEq accounts only for that scalar-map presentation.
Source: blueprint identity clause (blueprint: sk-def-sp-tate-twist).
Proof: ZMod.castHom_self makes the two scalar maps equal. The root transition
at equal indices is the identity because its power exponent is one. Thus the
identity has the defining pure-tensor formula; uniqueness identifies the maps. -/
theorem spFiniteKummer_id
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    HEq (spFiniteKummer X ℓ A r r (le_refl r) a)
      (𝟙 (Scheme.tateFiniteLine X ℓ A r a)) := by
  sorry

/-- Kummer identifications compose, with the canonical equality of quotient scalar maps.
Source: blueprint composition clause (blueprint: sk-def-sp-tate-twist).
Proof: ZMod.castHom_comp identifies the source scalar actions. On pure tensors
the composite applies two root powers, whose exponents multiply to the direct
power exponent. The coefficient factor stays fixed. Apply uniqueness in
spFiniteKummer_existsUnique. HEq records the scalar-map transport just described. -/
theorem spFiniteKummer_comp
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n m : ℕ)
    (hrn : r ≤ n) (hnm : n ≤ m) (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    HEq (spFiniteKummer X ℓ A r m (hrn.trans hnm) a)
      (spFiniteKummer X ℓ A n m hnm
          (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
            (ZMod (ℓ ^ (r + 1))))) ≫
        spFiniteKummer X ℓ A r n hrn a) := by
  sorry

/-- All signed powers of an internal coefficient line, in the sectionwise module encoding.
Zero is the coefficient unit; positive degrees use tensor powers and negative
degrees use sheaf Hom into the unit. The equivalence keeps the underlying sheaf.
Source: blueprint signed twists (blueprint: sk-def-sp-tate-twist). -/
def spSignedTwist (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R) (d : ℤ) :=
  WeilConjectures.coefficientTwistLine.{u} X
    (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R)
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor.obj L)
    d

/-- K(d) in the unbounded derived category of arbitrary ringed-site module sheaves.
The signed coefficient line is placed in degree zero; the tensor is exactly the
recorded ringed-site derived tensor, with its K-flat representative characterization.
Source: blueprint final formula (blueprint: sk-def-sp-tate-twist). -/
def spComplexTwist
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} (Scheme.purTwistRing X R))]
    (L : SheafOfModules.{u + 1} (Scheme.purTwistRing X R))
    (K : DerivedCategory (SheafOfModules.{u + 1} (Scheme.purTwistRing X R))) (d : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} (Scheme.purTwistRing X R)) :=
  (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) R).obj
    (K, (DerivedCategory.singleFunctor.{u + 1, u + 1, u + 2}
      (SheafOfModules.{u + 1} (Scheme.purTwistRing X R)) 0).obj
      (WeilConjectures.coefficientTwistLine.{u} X (R := R) L d))

/-- The constructed integral, rational and sheafified-colimit lines are locally free
of rank one over their respective pulled-back condensed coefficient rings.
Source: blueprint local-generator paragraph (blueprint: sk-def-sp-tate-twist).
Proof: use clauses 1 and 2 of det-def-sp-tate-twist-locally-free to choose one
pro-etale cover and compatible root generators. At each positive quotient level,
a maps to a tensor zeta_n is a free rank-one trivialization. They commute with
root powers and coefficient reduction. On the slice site, take their sectionwise
inverse limits. The cofinal ell-power form of the integral coefficient comparison
identifies the coefficient limit with O_E,X; if ell=v*pi^e then the indices e*n
are cofinal. Extend scalars to E_X using det-prop-sfb-qlbar-colimit-x-invert-ell.
The same zeta_n work for every E, so these maps commute with all finite-extension
transitions. Their sheafified colimit is the unit over Qbar_X, since p_X^* preserves
the finite-subextension coefficient colimit. Limits and sheafification restrict to
the slice with the same sections and coverings. Descend rank one along the cover.
Only the two compatible-root and finite Kummer clauses of the cited theorem are
used; no common-stage rational coefficient category is used. -/
theorem spTwists_locallyFree
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (spSignedTwist X _ (spIntegralTwist X ℓ E) 1).IsFiniteLocallyFreeOfRank 1 ∧
    (spSignedTwist X _ (spRationalTwist X ℓ E) 1).IsFiniteLocallyFreeOfRank 1 ∧
    (spSignedTwist X _ (spQbarTwist X ℓ) 1).IsFiniteLocallyFreeOfRank 1 := by
  sorry
/-- A single pro-etale covering carries compatible root generators and trivializes
all the constructed integral, rational and algebraic-closure coefficient lines.
Source: blueprint common-cover and slice-site paragraphs (blueprint: sk-def-sp-tate-twist).
Proof: take the compatible-root cover from clause 1 of the recorded local-freeness
theorem. The displayed root-module isomorphisms have its normalized generator formula.
For each E and each positive quotient, tensor this formula with B_E,n; the same
root sections work for every field. They commute with reductions. Take the inverse
limits on the slice, identify the coefficient limit by the integral comparison,
then extend scalars to E. These trivializations commute with every finite-extension
transition by its finite tensor normalization. Their sheafified colimit is the
Qbar coefficient unit by the coefficient-colimit identity. Thus the same covering
works simultaneously for all finite E and for Qbar, with no quasi-compactness
hypothesis on X. -/
theorem spTwists_commonCover
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ Scheme.ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (Scheme.purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n))).over
            (U i) ≅ (Scheme.purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (Scheme.ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((Scheme.purTwistRing X (Scheme.purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (Scheme.purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
        (hA : (ℓ ^ (r + 1) : A) = 0) (i : I),
        Nonempty ((spFiniteTwist X ℓ A r hA).over (U i) ≅
          (SheafOfModules.unit
            (Scheme.purTwistRing X (Scheme.tateFiniteCoefficient X A))).over (U i))) ∧
      (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (i : I),
        Nonempty ((spSignedTwist X _ (spIntegralTwist X ℓ E) 1).over (U i) ≅
          (spSignedTwist X _ (spIntegralTwist X ℓ E) 0).over (U i)) ∧
        Nonempty ((spSignedTwist X _ (spRationalTwist X ℓ E) 1).over (U i) ≅
          (spSignedTwist X _ (spRationalTwist X ℓ E) 0).over (U i))) ∧
      ∀ i : I, Nonempty ((spSignedTwist X _ (spQbarTwist X ℓ) 1).over (U i) ≅
        (spSignedTwist X _ (spQbarTwist X ℓ) 0).over (U i)) := by
  sorry

end AlgebraicGeometry.ProEtale

