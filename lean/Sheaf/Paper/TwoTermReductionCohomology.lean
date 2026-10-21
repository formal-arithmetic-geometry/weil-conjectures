/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
import Sheaf.Algebra.Homology.KFlatScalarTowerRealization
import Sheaf.Paper.CondensedPointCoefficients
import Sheaf.Paper.CondensedPointDiscreteConstantComparison
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.ConstantRingModuleSheaves
import Sheaf.AlgebraicGeometry.ProEtale.ConstantRealizationDetectsZero
import Sheaf.CategoryTheory.SiteConstantModuleUnit

/-! # The two-term integral coefficient example

Source: main-20261015, sk-def-pe-derived-completion, final paragraph;
Stacks Tags 06YQ and 06YY (blueprint: lem-pe-two-term-reduction-cohomology).

## Main definitions

* `ring`, `map`, `projection`, `step`, `residue`: the existing coefficient constructions.
* `complex`, `localized`, `transition`: the literal complex and the canonical derived mate.
* `Realization`, `Cohomology`, `TensorCalculation`, `Calculation`: the specified calculation.

## Main statements

* `two_term_reduction_cohomology`: the K-flat, cohomology, transition and tensor calculation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open SheafOfModules.SuccessiveDerivedQuotient
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale.TwoTermReduction

/-- The existing section-ring presentation of a pulled-back continuous coefficient ring.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def ring (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  let S := (upperStarFromPoint X).mapCommMon.obj
    (CommMon.mk (Profinite.continuousMapRingObj A))
  letI := S.mon
  letI := S.comm
  sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S.X

/-- On sections a coefficient map is the original internal ring map, with no choices.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def map (X : Scheme.{u}) {A B : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : ring X A ⟶ ring X B :=
  ⟨Functor.whiskerRight
    ((Monoidal.commMonFunctorCategoryEquivalence X.ProEtᵒᵖ Ab.{u + 1}).functor.map
      ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapCommMon.map
        ((upperStarFromPoint X).mapCommMon.map (CommMon.homMk (Mon.ofHom
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (Profinite.continuousMapRingSheafMap f hf))))))) commMonToRing⟩

/-- The literal two-term complex with differential multiplication by the prime.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def complex (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ :=
  HomologicalComplex.double (C := Modules.{u + 1, u, u + 1} R)
    (ℓ • 𝟙 (SheafOfModules.unit
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)


/-- The free rank-one module over the existing ring sheaf.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def unit (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    Modules.{u + 1, u, u + 1} R :=
  SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The identification of the degree-minus-one term of the literal double complex.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def termMinus (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (complex ℓ X R).X (-1) ≅ unit X R :=
  HomologicalComplex.doubleXIso₀ _ _

/-- The identification of the degree-zero term of the literal double complex.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def termZero (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (complex ℓ X R).X 0 ≅ unit X R :=
  HomologicalComplex.doubleXIso₁ _ _ (by decide)

/-- Positive quotient exponent: the natural index n denotes the paper's n+1.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def finiteRing (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) := ring X (ZMod (ℓ ^ (n + 1)))

/-- The actual pulled-back integral-to-finite quotient homomorphism.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def projection (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ) :
    ring X ℤ_[ℓ] ⟶ finiteRing ℓ X n :=
  map X (PadicInt.toZModPow (n + 1)) (PadicInt.continuous_toZModPow (n + 1))

/-- The actual consecutive quotient homomorphism, induced by postcomposition.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def step (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    finiteRing ℓ X (n + 1) ⟶ finiteRing ℓ X n :=
  map X (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
    (ZMod (ℓ ^ (n + 1)))) (continuous_of_discreteTopology)

/-- The canonical residue homomorphism giving the B_n-action on k_X.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def residue (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    finiteRing ℓ X n ⟶ ring X (ZMod ℓ) :=
  map X (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ))
    (continuous_of_discreteTopology)

/-- The residue sheaf with exactly its reduction-modulo-prime scalar action.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def k (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) : Modules.{u + 1, u, u + 1} (finiteRing ℓ X n) :=
  (restriction.{u + 1, u, u + 1} (residue ℓ X n)).obj (unit X (ring X (ZMod ℓ)))

/-- Additive postcomposition before pullback, retaining the prescribed kernel inclusion.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def additiveMap {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+ B) (hf : Continuous f) :
    Profinite.continuousMapRingObj.{u} A ⟶ Profinite.continuousMapRingObj B :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
      { toFun := fun x ↦ ULift.up
          (⟨fun t ↦ f (x.down t), hf.comp x.down.continuous⟩ : C(S.unop, B))
        map_zero' := by
          apply ULift.ext
          apply ContinuousMap.ext
          intro t
          exact f.map_zero
        map_add' := fun x y ↦ by
          apply ULift.ext
          apply ContinuousMap.ext
          intro t
          exact f.map_add (x.down t) (y.down t) }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The canonical homology comparison for exact restriction of scalars.
The proof-valued instances are extracted from the existing ordinary adjunction theorem.
Source: Stacks 03D7 and blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def restrictHomology (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (Modules.{u + 1, u, u + 1} S) ℤ) (q : ℤ) :
    (((restriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ)).obj P).homology q ≅
      (restriction.{u + 1, u, u + 1} a).obj (P.homology q) :=
  letI := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose
  letI := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose_spec.choose
  (P.sc q).mapHomologyIso (restriction.{u + 1, u, u + 1} a)

/-- The usual localization, written through the homotopy quotient to read its counit.
The canonical quotientCompQhIso identifies this with Q(P).
Source: Stacks 05RR and blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def localized (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ) :
    DerivedCategory (Modules.{u + 1, u, u + 1} R) :=
  DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The canonical localization factorization of cohomology on the same complex.
Source: Stacks 05RR and blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def localizedHomology (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor (Modules.{u + 1, u, u + 1} R) q).obj
      (localized X R P) ≅ P.homology q :=
  (DerivedCategory.homologyFunctorFactorsh (Modules.{u + 1, u, u + 1} R) q).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≪≫
    (HomotopyCategory.homologyFunctorFactors (Modules.{u + 1, u, u + 1} R) (.up ℤ) q).app P

/-- The existing section module action, with its coefficient ring made explicit.
Source: Stacks 03D7 and blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def sectionSMul (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : Modules.{u + 1, u, u + 1} R) (U : X.ProEtᵒᵖ)
    (b : R.obj.obj U) (x : M.val.obj U) : M.val.obj U :=
  @SMul.smul _ _ (M.val.obj U).isModule.toSMul b x

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section Calculation
variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
  [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
    HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
  (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a) (N : Normalization.{u + 1, u, u + 1, w} p)

/-- The canonical transition is the adjoint of the normalized scalar-composition map.
The compatibility equation is only the equality of the actual quotient homomorphisms.
Source: Stacks 0D6D and blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def transition (n : ℕ) (h : projection ℓ X (n + 1) ≫ step ℓ X n = projection ℓ X n)
    (K : DerivedCategory (Modules.{u + 1, u, u + 1} (ring X ℤ_[ℓ]))) :
    (p (projection ℓ X (n + 1))).derived.obj K ⟶
      (N.right (step ℓ X n)).obj ((p (projection ℓ X n)).derived.obj K) :=
  (N.adjunction (step ℓ X n)).homEquiv _ _
    ((N.derived (projection ℓ X (n + 1)) (step ℓ X n)).hom.app K ≫
      eqToHom (congrArg (fun a ↦ (p a).derived.obj K) h))

/-- The comparison objects and maps of the two-term calculation. The equations in
`IsRealization` fix the canonical maps through their values and universal counits.
Every object is the existing ring, module, tensor or localization.
Source: blueprint, derived completion, final paragraph; Stacks 06YY
(blueprint: lem-pe-two-term-reduction-cohomology). -/
structure Realization (N : Normalization.{u + 1, u, u + 1, w} p) where
  /-- The canonical quotient maps commute. -/
  compatible : ∀ n, projection ℓ X (n + 1) ≫ step ℓ X n = projection ℓ X n
  /-- Ordinary scalar extension gives the literal finite two-term complex. -/
  ordinary : ∀ n, ((p (projection ℓ X n)).ordinary.mapHomologicalComplex (.up ℤ)).obj
    (complex ℓ X (ring X ℤ_[ℓ])) ≅ complex ℓ X (finiteRing ℓ X n)
  /-- Canonical derived computation isomorphisms on that same representative. -/
  model : ∀ n, (p (projection ℓ X n)).derived.obj
    (localized X _ (complex ℓ X (ring X ℤ_[ℓ]))) ≅
      localized X _ (complex ℓ X (finiteRing ℓ X n))
  /-- The termwise quotient map. -/
  chain : ∀ n, complex ℓ X (finiteRing ℓ X (n + 1)) ⟶
    ((restriction.{u + 1, u, u + 1} (step ℓ X n)).mapHomologicalComplex (.up ℤ)).obj
      (complex ℓ X (finiteRing ℓ X n))

/-- The equations and properties of the specified Realization data.
Source: blueprint, derived completion, final paragraph; Stacks 06YY and 03EK
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def IsRealization (T : Realization ℓ X p N) : Prop :=
  -- kflat: The integral two-term complex is K-flat.
  (CochainComplex.IsKFlatIndependentCoefficients (R := ring X ℤ_[ℓ])
      (complex ℓ X (ring X ℤ_[ℓ]))) ∧
  -- ordinary_sections: The ordinary comparison is r tensor b maps to a_n(r)b in both terms.
  (∀ (n : ℕ) (i : ℤ) (hi : i = -1 ∨ i = 0)
      (U : X.ProEtᵒᵖ) (b : (finiteRing ℓ X n).obj.obj U)
      (r : ((complex ℓ X (ring X ℤ_[ℓ])).X i).val.obj U),
      HEq (((T.ordinary n).hom.f i).val.app U
        (sectionTensor (p (projection ℓ X n)) _ U b r))
        (b • ((projection ℓ X n).hom.app U).hom
          ((if hi' : i = -1 then
            (eqToHom (congrArg (fun j ↦ (complex ℓ X (ring X ℤ_[ℓ])).X j) hi') ≫
              (termMinus ℓ X (ring X ℤ_[ℓ])).hom).val.app U r
          else
            (eqToHom (congrArg (fun j ↦ (complex ℓ X (ring X ℤ_[ℓ])).X j)
                (hi.resolve_left hi')) ≫ (termZero ℓ X (ring X ℤ_[ℓ])).hom).val.app U r)))) ∧
  -- model_eq: Retain the universal counit, not merely an isomorphism of objects.
  (∀ n, (T.model n).hom =
      (p (projection ℓ X n)).counit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (complex ℓ X (ring X ℤ_[ℓ]))) ≫
      DerivedCategory.Qh.map
        (((p (projection ℓ X n)).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app
            (complex ℓ X (ring X ℤ_[ℓ])) ≫
          (HomotopyCategory.quotient _ (.up ℤ)).map (T.ordinary n).hom)) ∧
  -- chain_minus: It is reduction on the term in degree minus one.
  (∀ n U x,
      ((restriction.{u + 1, u, u + 1} (step ℓ X n)).map
        (termMinus ℓ X (finiteRing ℓ X n)).hom).val.app U
          (((T.chain n).f (-1)).val.app U x) =
        ((step ℓ X n).hom.app U).hom
          ((termMinus ℓ X (finiteRing ℓ X (n + 1))).hom.val.app U x)) ∧
  -- chain_zero: It is reduction on the term in degree zero.
  (∀ n U x,
      ((restriction.{u + 1, u, u + 1} (step ℓ X n)).map
        (termZero ℓ X (finiteRing ℓ X n)).hom).val.app U
          (((T.chain n).f 0).val.app U x) =
        ((step ℓ X n).hom.app U).hom
          ((termZero ℓ X (finiteRing ℓ X (n + 1))).hom.val.app U x)) ∧
  -- transition_eq: The actual adjunction-defined transition is represented by this chain map.
  (∀ n,
      transition ℓ X p N n (T.compatible n) (localized X _ (complex ℓ X (ring X ℤ_[ℓ]))) ≫
        (N.right (step ℓ X n)).map (T.model n).hom ≫
        (N.right_factors (step ℓ X n)).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (complex ℓ X (finiteRing ℓ X n))) ≫
        DerivedCategory.Qh.map
          (((restriction.{u + 1, u, u + 1} (step ℓ X n)).mapHomotopyCategoryFactors
            (.up ℤ)).hom.app (complex ℓ X (finiteRing ℓ X n))) =
      (T.model (n + 1)).hom ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map (T.chain n)))

/-- The cohomology, with its coefficient maps and actual transition maps fixed.
Source: blueprint, derived completion, final paragraph; Stacks 06YY
(blueprint: lem-pe-two-term-reduction-cohomology). -/
structure Cohomology (T : Realization ℓ X p N) where
  /-- The specified B_n-linear degree-minus-one identification. -/
  minus : ∀ n, (complex ℓ X (finiteRing ℓ X n)).homology (-1) ≅ k ℓ X n
  /-- The specified B_n-linear degree-zero identification. -/
  zero : ∀ n, (complex ℓ X (finiteRing ℓ X n)).homology 0 ≅ k ℓ X n
  /-- The degree-minus-one identification on the actual derived reduction K_n. -/
  derivedMinus : ∀ n, (DerivedCategory.homologyFunctor
    (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) (-1)).obj
    ((p (projection ℓ X n)).derived.obj
      (localized X _ (complex ℓ X (ring X ℤ_[ℓ])))) ≅ k ℓ X n
  /-- The degree-zero identification on the actual derived reduction K_n. -/
  derivedZero : ∀ n, (DerivedCategory.homologyFunctor
    (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) 0).obj
    ((p (projection ℓ X n)).derived.obj
      (localized X _ (complex ℓ X (ring X ℤ_[ℓ])))) ≅ k ℓ X n
  /-- The additive map before pullback. -/
  kernelCoefficient : ∀ n, ZMod ℓ →+ ZMod (ℓ ^ (n + 1))
  /-- The B_n-linear kernel inclusion. -/
  inclusion : ∀ n, k ℓ X n ⟶ unit X (finiteRing ℓ X n)
  /-- The B_n-linear reduction onto the residue module. -/
  reduction : ∀ n, unit X (finiteRing ℓ X n) ⟶ k ℓ X n
  /-- The identity on the same underlying residue sheaf, with restricted scalars. -/
  residueIdentity : ∀ n, k ℓ X (n + 1) ⟶ (restriction.{u + 1, u, u + 1} (step ℓ X n)).obj (k ℓ X n)

/-- The equations and properties of the specified Cohomology data.
Source: blueprint, derived completion, final paragraph; Stacks 06YY and 03EK
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def IsCohomology (T : Realization ℓ X p N)
    (H : Cohomology ℓ X p N T) : Prop :=
  -- vanishes: All other cohomology objects vanish.
  (∀ (n : ℕ) (q : ℤ), q ≠ -1 → q ≠ 0 →
      IsZero ((complex ℓ X (finiteRing ℓ X n)).homology q)) ∧
  -- derivedMinus_eq:
  -- It is the previously specified identification transported by the canonical model.
  (∀ n, (H.derivedMinus n).hom =
      (DerivedCategory.homologyFunctor
        (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) (-1)).map (T.model n).hom ≫
        (localizedHomology X _ (complex ℓ X (finiteRing ℓ X n)) (-1)).hom ≫ (H.minus n).hom) ∧
  -- derivedZero_eq: It is reduction modulo the prime, via the canonical model.
  (∀ n, (H.derivedZero n).hom =
      (DerivedCategory.homologyFunctor
        (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) 0).map (T.model n).hom ≫
        (localizedHomology X _ (complex ℓ X (finiteRing ℓ X n)) 0).hom ≫ (H.zero n).hom) ∧
  -- derivedVanishes: The other derived cohomology sheaves vanish.
  (∀ (n : ℕ) (q : ℤ), q ≠ -1 → q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) q).obj
        ((p (projection ℓ X n)).derived.obj
          (localized X _ (complex ℓ X (ring X ℤ_[ℓ])))))) ∧
  -- kernelCoefficient_formula: Its value on integer representatives is multiplication by ℓ^n.
  (∀ (n : ℕ) (a : ℤ),
      H.kernelCoefficient n a = (ℓ : ZMod (ℓ ^ (n + 1))) ^ n * (a : ZMod (ℓ ^ (n + 1)))) ∧
  -- inclusion_eq: It is exactly the pullback of the specified additive coefficient map.
  (∀ n,
      HEq ((SheafOfModules.toSheaf _).map (H.inclusion n))
        ((upperStarFromPoint X).map
          (additiveMap (H.kernelCoefficient n) continuous_of_discreteTopology))) ∧
  -- minus_eq: Minus is the inverse of that kernel inclusion on cohomology.
  (∀ n, (complex ℓ X (finiteRing ℓ X n)).homologyπ (-1) ≫
        (H.minus n).hom ≫ H.inclusion n =
      (complex ℓ X (finiteRing ℓ X n)).iCycles (-1) ≫
        (termMinus ℓ X (finiteRing ℓ X n)).hom) ∧
  -- reduction_eq: It is exactly reduction modulo ℓ.
  (∀ n U x, (H.reduction n).val.app U x = ((residue ℓ X n).hom.app U).hom x) ∧
  -- zero_eq: Zero is induced by that reduction on the cokernel.
  (∀ n, (complex ℓ X (finiteRing ℓ X n)).homologyπ 0 ≫ (H.zero n).hom =
      (complex ℓ X (finiteRing ℓ X n)).iCycles 0 ≫
        (termZero ℓ X (finiteRing ℓ X n)).hom ≫ H.reduction n) ∧
  -- residueIdentity_eq: The preceding morphism really is the identity on sections.
  (∀ n,
      HEq ((SheafOfModules.toSheaf _).map (H.residueIdentity n))
        (𝟙 ((SheafOfModules.toSheaf _).obj (unit X (ring X (ZMod ℓ)))))) ∧
  -- minus_transition: The degree-minus-one transition is zero.
  (∀ n, HomologicalComplex.homologyMap (T.chain n) (-1) ≫
      (restrictHomology X (step ℓ X n) (complex ℓ X (finiteRing ℓ X n)) (-1)).hom ≫
        (restriction.{u + 1, u, u + 1} (step ℓ X n)).map (H.minus n).hom = 0) ∧
  -- zero_transition:
  -- The degree-zero transition is the identity under the prescribed identifications.
  (∀ n, HomologicalComplex.homologyMap (T.chain n) 0 ≫
      (restrictHomology X (step ℓ X n) (complex ℓ X (finiteRing ℓ X n)) 0).hom ≫
        (restriction.{u + 1, u, u + 1} (step ℓ X n)).map (H.zero n).hom =
      (H.zero (n + 1)).hom ≫ H.residueIdentity n) ∧
  -- nonzero: The residue module is nonzero.
  (∀ n, ¬ IsZero (k ℓ X n)) ∧
  -- constantResidue: Its underlying abelian sheaf is the specified constant F_ℓ sheaf.
  (Nonempty
      ((SheafOfModules.toSheaf _).obj (unit X (ring X (ZMod ℓ))) ≅
        (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))))

/-- The specified ordinary tensor action and the zero induced transition.
Source: blueprint, derived completion, final paragraph; Stacks 03EK
(blueprint: lem-pe-two-term-reduction-cohomology). -/
structure TensorCalculation (T : Realization ℓ X p N)
    (H : Cohomology ℓ X p N T) where
  /-- The ordinary sheaf tensor action is an isomorphism. -/
  action : ∀ n, SheafOfModules.changeOfRings.{u, u + 1, u + 1} (step ℓ X n)
    ((complex ℓ X (finiteRing ℓ X (n + 1))).homology (-1)) ≅ k ℓ X n
  /-- The balanced map induced by the quotient transition. -/
  induced : ∀ n, SheafOfModules.changeOfRings.{u, u + 1, u + 1} (step ℓ X n)
    ((complex ℓ X (finiteRing ℓ X (n + 1))).homology (-1)) ⟶
      (complex ℓ X (finiteRing ℓ X n)).homology (-1)

/-- The equations and properties of the specified TensorCalculation data.
Source: blueprint, derived completion, final paragraph; Stacks 06YY and 03EK
(blueprint: lem-pe-two-term-reduction-cohomology). -/
def IsTensorCalculation (T : Realization ℓ X p N)
    (H : Cohomology ℓ X p N T) (V : TensorCalculation ℓ X p N T H) : Prop :=
  -- action_eq: It sends x tensor b to the residue action of b on the identified x.
  (∀ n U b x, ((V.action n).hom).val.app U
        (pure (step ℓ X n) _ U b x) =
      sectionSMul X _ (k ℓ X n) U b
        ((H.residueIdentity n).val.app U (((H.minus (n + 1)).hom).val.app U x))) ∧
  -- induced_eq: It is the map induced by that transition, specified on pure sections.
  (∀ n U b x, (V.induced n).val.app U (pure (step ℓ X n) _ U b x) =
      sectionSMul X _ ((complex ℓ X (finiteRing ℓ X n)).homology (-1)) U b
        (@id (((complex ℓ X (finiteRing ℓ X n)).homology (-1)).val.obj U)
          ((HomologicalComplex.homologyMap (T.chain n) (-1) ≫
            (restrictHomology X (step ℓ X n) (complex ℓ X (finiteRing ℓ X n)) (-1)).hom).val.app
              U x))) ∧
  -- induced_zero: Consequently the ordinary-tensor transition is zero.
  (∀ n, V.induced n = 0)

/-- The three parts of the stated two-term reduction calculation.
Source: blueprint, derived completion, final paragraph
(blueprint: lem-pe-two-term-reduction-cohomology). -/
structure Calculation where
  /-- K-flat representative and its canonical quotient transitions. -/
  realization : Realization ℓ X p N
  /-- The specified cohomology identifications and their transitions. -/
  cohomology : Cohomology ℓ X p N realization
  /-- Nonzero ordinary scalar extension and its zero transition. -/
  tensor : TensorCalculation ℓ X p N realization cohomology
  /-- The representative and canonical-transition properties. -/
  realization_spec : IsRealization ℓ X p N realization
  /-- The cohomology, coefficient-map, nonvanishing and transition properties. -/
  cohomology_spec : IsCohomology ℓ X p N realization cohomology
  /-- The action formula and the zero induced map. -/
  tensor_spec : IsTensorCalculation ℓ X p N realization cohomology tensor

end Calculation

/-- The two-term integral coefficient calculation, with all quotient maps retained.
Source: main-20261015 blueprint, sk-def-pe-derived-completion, final paragraph;
Stacks Tags 06YQ and 06YY (blueprint: lem-pe-two-term-reduction-cohomology).

Proof: Tensoring with the free rank-one ring module is the identity by the balanced
relations, and tensoring with zero is zero. Thus the bounded-above complex has flat
terms and is K-flat (lem-weil-pbc-independent-bounded-flat-kflat). Derived change of
rings computes it by the termwise tensor (lem-pur-derived-change-of-rings); simultaneous
scalar-tower realization (lem-pe-kflat-scalar-tower-realization) identifies the actual
adjunction transition with reduction in both terms. The finite discrete comparisons
(lem-pe-condensed-point-discrete-constant-comparisons) identify these coefficients
with constant rings. Ring maps out of ZMod(ℓ^n) are determined by one, so the comparisons
respect reductions; additive maps out of ZMod ℓ are likewise determined by one, so they
respect the specified kernel map (def-weil-pbc-sheafification).

For n≥1, the map a↦ℓ^(n-1)a identifies ZMod ℓ with the kernel of multiplication by ℓ
on ZMod(ℓ^n): divisibility of ℓ^(n-1)a by ℓ^n is equivalent to divisibility of a by ℓ.
Reduction modulo ℓ is onto and its kernel is ℓ ZMod(ℓ^n), giving the cokernel. Both maps
are linear for the residue action. Exact constant module sheafification and the action
extension equivalence (lem-cbc-constant-ring-module-sheaves and
lem-weil-pbc-site-module-presheaf-sheafification-exact) transfer these computations to
sheaves and through localization. All other cohomology vanishes because the other
terms are zero. Consecutive reduction kills ℓ^n a, hence the minus-one transition is
zero; reduction followed by reduction modulo ℓ is unchanged, hence degree zero is the
identity. This includes n=1, when the differential is zero and both coefficient maps
are identities.

The identity object Spec Ω is nonempty. Injectivity of constant sections
(lem-sfb-constant-realization-detects-zero) and 0≠1 in ZMod ℓ show k_X≠0. The action
map x tensor b↦b̄x has inverse x↦x tensor 1. Locally b is constant
(lem-sf-constant-module-unit-locally-bijective), hence has a lift to the preceding
finite quotient. Balancing moves that lift to x, proving the other inverse equation;
sheafification extends it globally. Finally the map induced by the cohomology
transition is zero on pure tensors, hence zero by the tensor universal property. -/
theorem two_term_reduction_cohomology (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a) (N : Normalization.{u + 1, u, u + 1, w} p) :
    Nonempty (Calculation ℓ (Spec (.of Ω)) p N) := by
  sorry

end AlgebraicGeometry.ProEtale.TwoTermReduction
