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
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients

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
open CategoryTheory.Preadditive CategoryTheory.Category
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



open scoped CategoryTheory.Obj


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem upperStarFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (upperStarFromPoint X) := by
  unfold upperStarFromPoint pointUpperStar
  infer_instance

private theorem upperStarLeftAdjoint (X : Scheme.{u}) :
    (upperStarFromPoint X).IsLeftAdjoint :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

private theorem upperStar_additive (X : Scheme.{u}) :
    (upperStarFromPoint X).Additive :=
  leftExactFunctor_le_additiveFunctor _ _ _ (upperStarFiniteLimits X)

attribute [local instance] upperStar_additive

private def coefficientFunctor (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousMapRingObj A) ⥤ Modules.{u + 1, u, u + 1} (ring X A) :=
  (upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj A) ⋙
    sectionModuleFunctor (Scheme.ProEt.topology X)
      ((upperStarFromPoint X).obj (Profinite.continuousMapRingObj A))

private theorem coefficientFunctor_exact (X : Scheme.{u})
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteLimits (coefficientFunctor X A) ∧
      PreservesFiniteColimits (coefficientFunctor X A) := by
  let e := sectionModuleEquivalence (Scheme.ProEt.topology X)
    ((upperStarFromPoint X).obj (Profinite.continuousMapRingObj A))
  have := upperStarFiniteLimits X
  have := upperStarLeftAdjoint X
  have : PreservesFiniteLimits e.functor := inferInstance
  have : PreservesFiniteColimits e.functor := inferInstance
  change PreservesFiniteLimits
      ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj A) ⋙ e.functor) ∧
    PreservesFiniteColimits
      ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj A) ⋙ e.functor)
  exact ⟨inferInstance, inferInstance⟩

private theorem coefficientFunctor_additive (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : (coefficientFunctor X A).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (coefficientFunctor_exact X A)

attribute [local instance] coefficientFunctor_additive

private def coefficientRegularIso (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (coefficientFunctor X A).obj (Mod.regular (Profinite.continuousMapRingObj A)) ≅
      unit X (ring X A) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    rfl
  · intro U V f
    rfl

private def doubleScalarIso {A B : Type*} [Category A] [Preadditive A]
    [HasZeroObject A] [Category B] [Preadditive B] [HasZeroObject B]
    (F : A ⥤ B) [F.Additive] (ℓ : ℕ) (M : A) (L : B) (e : F.obj M ≅ L) :
    (F.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.double (ℓ • 𝟙 M) (i₀ := (-1 : ℤ)) (i₁ := 0) (by decide)) ≅
      HomologicalComplex.double (ℓ • 𝟙 L) (i₀ := (-1 : ℤ)) (i₁ := 0) (by decide) := by
  let P := HomologicalComplex.double (ℓ • 𝟙 M)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)
  let Q := HomologicalComplex.double (ℓ • 𝟙 L)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)
  let ψ : Q ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P :=
    HomologicalComplex.mkHomFromDouble (by decide) (by decide)
      (e.inv ≫ F.map (HomologicalComplex.doubleXIso₀ _ _).inv)
      (e.inv ≫ F.map (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv)
      (by
        change (e.inv ≫ F.map (HomologicalComplex.doubleXIso₀ _ _).inv) ≫
          F.map (P.d (-1) 0) = _
        rw [Category.assoc, ← F.map_comp, HomologicalComplex.double_d _ _ (by decide)]
        simp only [Iso.inv_hom_id_assoc, Functor.map_nsmul,
          comp_nsmul, id_comp, nsmul_comp])
      (by
        intro j hj
        change _ ≫ F.map (P.d 0 j) = 0
        rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide), F.map_zero, comp_zero])
  have (i : ℤ) : IsIso (ψ.f i) := by
    by_cases h₀ : i = -1
    · subst i
      dsimp only [ψ]
      rw [HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    by_cases h₁ : i = 0
    · subst i
      dsimp only [ψ]
      rw [HomologicalComplex.mkHomFromDouble_f₁]
      infer_instance
    have hs : IsZero (Q.X i) := HomologicalComplex.isZero_double_X _ _ _ h₀ h₁
    have ht : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj P).X i) :=
      F.map_isZero (HomologicalComplex.isZero_double_X _ _ _ h₀ h₁)
    exact hs.isIso ht _
  have : IsIso ψ := HomologicalComplex.Hom.isIso_of_components ψ
  exact (asIso ψ).symm

private theorem map_comp (X : Scheme.{u})
    {A B C : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    (f : A →+* B) (hf : Continuous f) (g : B →+* C) (hg : Continuous g) :
    map X f hf ≫ map X g hg = map X (g.comp f) (hg.comp hf) := by
  apply Sheaf.hom_ext
  change (map X f hf).hom ≫ (map X g hg).hom = (map X (g.comp f) (hg.comp hf)).hom
  dsimp only [map]
  rw [← Functor.whiskerRight_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

private theorem projection_step (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ) :
    projection ℓ X (n + 1) ≫ step ℓ X n = projection ℓ X n := by
  rw [projection, step, map_comp]
  congr 1
  exact PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _)

private def scalarUnitPresheaf (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a (unit X R) ≅ (unit X S).val := by
  dsimp only [unit]
  refine PresheafOfModules.isoMk
    (fun U ↦ by
      let := (a.hom.app U).hom.toAlgebra
      exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj U) (S.obj.obj U)
        (S.obj.obj U)).toModuleIso)
    (by
      intro U V f
      let := (a.hom.app U).hom.toAlgebra
      let := (a.hom.app V).hom.toAlgebra
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul b r =>
        change TensorProduct.AlgebraTensorModule.rid (R.obj.obj V) (S.obj.obj V)
          (S.obj.obj V) ((SheafOfModules.changeOfRingsPresheaf a (unit X R)).map f
            (b ⊗ₜ[R.obj.obj U] r)) = _
        erw [Classical.choose_spec
          (SheafOfModules.exists_changeOfRingsMap a (unit X R) f)]
        change (a.hom.app V).hom (R.obj.map f r) * S.obj.map f (show S.obj.obj U from b) =
          S.obj.map f ((a.hom.app U).hom r * (show S.obj.obj U from b))
        rw [map_mul]
        congr 1
        exact ConcreteCategory.congr_hom (a.hom.naturality f) r)

private def scalarUnitIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : Presentation.{u + 1, u, u + 1, w} a) :
    p.ordinary.obj (unit X R) ≅ unit X S :=
  eqToIso (p.obj_eq _) ≪≫
    (PresheafOfModules.sheafification (𝟙 _)).mapIso (scalarUnitPresheaf X a) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit).app (unit X S)


private theorem scalarUnitIso_sections (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : Presentation.{u + 1, u, u + 1, w} a) (U : X.ProEtᵒᵖ)
    (b : S.obj.obj U) (r : (unit X R).val.obj U) :
    (scalarUnitIso X a p).hom.val.app U
      (sectionTensor.{u + 1, u, u + 1, w} p (unit X R) U b r) =
      (a.hom.app U).hom r * b := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
  let e : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a (unit X R) ≅
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj
        (unit X S)) := scalarUnitPresheaf X a
  have hn : adj.homEquiv _ _
      ((PresheafOfModules.sheafification (𝟙 _)).map e.hom ≫
        adj.counit.app (unit X S)) = e.hom := by
    rw [adj.homEquiv_naturality_left]
    rw [← adj.homEquiv_symm_id]
    change e.hom ≫ (adj.homEquiv _ (unit X S)
      ((adj.homEquiv _ (unit X S)).symm (𝟙 _))) = e.hom
    rw [Equiv.apply_symm_apply, Category.comp_id]
  have hmap := congrArg
    (fun f : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a (unit X R) ⟶
      (PresheafOfModules.restrictScalars (𝟙 _)).obj (unit X S).val ↦
      ((PresheafOfModules.toPresheaf.{u + 1, u, u + 1, u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj).map f).app U
      (b ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] r)) hn
  change (((PresheafOfModules.toPresheaf _).map
    (PresheafOfModules.sheafificationHomEquiv (𝟙 _)
      ((PresheafOfModules.sheafification (𝟙 _)).map e.hom ≫
        adj.counit.app (unit X S)))).app U)
      (b ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] r) = _ at hmap
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at hmap
  have ht : (scalarUnitIso X a p).hom =
      eqToHom (p.obj_eq _) ≫
        (PresheafOfModules.sheafification (𝟙 _)).map e.hom ≫
          adj.counit.app (unit X S) := rfl
  rw [ht]
  change (((eqToHom (p.obj_eq _) ≫
      (PresheafOfModules.sheafification (𝟙 _)).map e.hom ≫
        adj.counit.app (unit X S)).val.app U)
    (((eqToHom (p.obj_eq _).symm).val.app U)
      (SheafOfModules.SuccessiveDerivedQuotient.pure a (unit X R) U b r))) = _
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact hmap

private def kernelCoefficient (ℓ n : ℕ) : ZMod ℓ →+ ZMod (ℓ ^ (n + 1)) :=
  ZMod.lift ℓ ⟨(AddMonoidHom.mulLeft ((ℓ : ZMod (ℓ ^ (n + 1))) ^ n)).comp
    (Int.castAddHom (ZMod (ℓ ^ (n + 1)))), by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft,
        Int.coe_castAddHom, Int.cast_natCast]
      rw [← pow_succ, ← Nat.cast_pow]
      exact ZMod.natCast_self _⟩

private theorem kernelCoefficient_int (ℓ n : ℕ) (a : ℤ) :
    kernelCoefficient ℓ n a = (ℓ : ZMod (ℓ ^ (n + 1))) ^ n * a := by
  exact ZMod.lift_coe _ _ _

private theorem kernelCoefficient_injective (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Function.Injective (kernelCoefficient ℓ n) := by
  apply (injective_iff_map_eq_zero (kernelCoefficient ℓ n)).2
  intro a ha
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  rw [kernelCoefficient_int] at ha
  have hz : (ℓ : ℤ) ^ (n + 1) ∣ (ℓ : ℤ) ^ n * z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using ha
  rw [pow_succ, mul_comm ((ℓ : ℤ) ^ n) (ℓ : ℤ),
    mul_comm ((ℓ : ℤ) ^ n) z, mul_dvd_mul_iff_right
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero))] at hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hz

private theorem kernelCoefficient_exact (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Function.Exact (kernelCoefficient ℓ n)
      (AddMonoidHom.mulLeft (ℓ : ZMod (ℓ ^ (n + 1)))) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  constructor
  · intro hz
    have hd : (ℓ : ℤ) ^ (n + 1) ∣ (ℓ : ℤ) * z := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow,
        AddMonoidHom.coe_mulLeft] using hz
    rw [pow_succ', mul_dvd_mul_iff_left
      (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)] at hd
    obtain ⟨t, rfl⟩ := hd
    exact ⟨(t : ZMod ℓ), by simp only [kernelCoefficient_int, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast]⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective y
    simp only [kernelCoefficient_int, AddMonoidHom.coe_mulLeft]
    rw [← mul_assoc, ← pow_succ', ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

private theorem residueCoefficient_exact (ℓ : ℕ) (n : ℕ) :
    Function.Exact (AddMonoidHom.mulLeft (ℓ : ZMod (ℓ ^ (n + 1))))
      (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ)) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  constructor
  · intro hz
    have hd : (ℓ : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by
      simpa only [map_intCast] using hz)
    obtain ⟨t, rfl⟩ := hd
    exact ⟨(t : ZMod (ℓ ^ (n + 1))), by
      simp only [AddMonoidHom.coe_mulLeft, Int.cast_mul, Int.cast_natCast]⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    simp only [AddMonoidHom.coe_mulLeft, map_mul, map_natCast,
      ZMod.natCast_self, zero_mul]

private theorem kernelCoefficient_linear (ℓ : ℕ) (n : ℕ)
    (b : ZMod (ℓ ^ (n + 1))) (x : ZMod ℓ) :
    kernelCoefficient ℓ n
      (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ) b * x) =
        b * kernelCoefficient ℓ n x := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
  obtain ⟨t, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, ← Int.cast_mul, kernelCoefficient_int, kernelCoefficient_int,
    Int.cast_mul]
  ring

private def condensedResidue (ℓ : ℕ) (n : ℕ) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousMapRingObj (ZMod (ℓ ^ (n + 1)))) :=
  (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ))
        continuous_of_discreteTopology))).obj
    (Mod.regular (Profinite.continuousMapRingObj (ZMod ℓ)))

private def mappedRegularIso (X : Scheme.{u})
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj A)).obj
      (Mod.regular (Profinite.continuousMapRingObj A)) ≅
      Mod.regular ((upperStarFromPoint X).obj (Profinite.continuousMapRingObj A)) :=
  Mod.isoMk (Iso.refl _) (by simp [Mod.act])

private def coefficientResidueIso (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    (coefficientFunctor X (ZMod (ℓ ^ (n + 1)))).obj (condensedResidue ℓ n) ≅ k ℓ X n := by
  let R := Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ (n + 1)))
  let S := Profinite.continuousMapRingObj.{u} (ZMod ℓ)
  let φ : R ⟶ S := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ))
        continuous_of_discreteTopology)
  let F := upperStarFromPoint X
  let e := (F.mapModComapIso φ).app (Mod.regular S) ≪≫
    (Mod.comap (F.map φ)).mapIso (mappedRegularIso X (ZMod ℓ))
  let G := sectionModuleFunctor (Scheme.ProEt.topology X) (F.obj R)
  exact G.mapIso e ≪≫
    (CondensedRing.sectionModuleComapIso X (F.map φ)).app (Mod.regular (F.obj S)) ≪≫
    (SheafOfModules.restrictScalars _).mapIso
      (CondensedRing.sectionModuleRegularIso X (F.obj S))

private def condensedInclusion (ℓ : ℕ) (n : ℕ) :
    condensedResidue.{u} ℓ n ⟶
      Mod.regular (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ (n + 1)))) := by
  letI : MonObj (Profinite.continuousMapRingObj.{u} (ZMod ℓ)).obj :=
    (Profinite.continuousMapRingSheaf (ZMod ℓ)).obj.monObjCompForget₂
  letI : MonObj (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ (n + 1)))).obj :=
    (Profinite.continuousMapRingSheaf (ZMod (ℓ ^ (n + 1)))).obj.monObjCompForget₂
  let a := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ))
        continuous_of_discreteTopology)
  let f := additiveMap.{u} (kernelCoefficient ℓ n) continuous_of_discreteTopology
  refine Mod.homMk f ?_
  change (a ▷ _ ≫ MonObj.mul) ≫ f = _ ◁ f ≫ MonObj.mul
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc]
  have h₀ := Sheaf.μ_comp_map_mul (Profinite.continuousMapRingObj.{u} (ZMod ℓ))
  have h₁ := Sheaf.μ_comp_map_mul
    (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ (n + 1))))
  simp only [reassoc_of% h₀, h₁]
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro b x
  apply ULift.ext
  ext t
  exact kernelCoefficient_linear ℓ n (b.down t) (x.down t)

private def condensedReduction (ℓ : ℕ) (n : ℕ) :
    Mod.regular (Profinite.continuousMapRingObj.{u} (ZMod (ℓ ^ (n + 1)))) ⟶
      condensedResidue.{u} ℓ n := by
  let f := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ))
        continuous_of_discreteTopology)
  refine Mod.homMk f ?_
  change MonObj.mul ≫ f = _ ◁ f ≫ f ▷ _ ≫ MonObj.mul
  rw [IsMonHom.mul_hom]
  rw [tensorHom_def']
  simp only [Category.assoc]

private theorem condensedExact_of_sections (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (S : ShortComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousMapRingObj A)))
    (h : ∀ U : Profinite.{u}ᵒᵖ,
      Function.Exact (S.f.hom.hom.app U) (S.g.hom.hom.app U)) : S.Exact := by
  let V := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Profinite.continuousMapRingObj A)
  apply V.reflects_exact_of_faithful S
  let P := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  have hp : ((S.map V).map P).Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro U
    exact (ShortComplex.ab_exact_iff_function_exact _).2 (h U)
  exact ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso (S.map V)
      (sheafificationNatIso (coherentTopology Profinite.{u}) Ab.{u + 1})).symm
    (hp.map (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))

private theorem condensed_smul_apply (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (m : ℕ)
    (U : Profinite.{u}ᵒᵖ)
    (x : ULift.{u + 1} C(U.unop, A)) (t : U.unop) :
    (((m • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u} A))).hom.hom.app U)
      x).down t = (m : A) * x.down t := by
  change (((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
    (m • 𝟙 (Profinite.continuousMapRingObj.{u} A))).app U x).down t = _
  have hm := (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map_nsmul
    (f := 𝟙 (Profinite.continuousMapRingObj.{u} A)) (n := m)
  rw [(sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map_id] at hm
  rw [hm, NatTrans.app_nsmul]
  change m • x.down t = (m : A) * x.down t
  exact nsmul_eq_mul _ _

private theorem condensedKernel_zero (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    condensedInclusion.{u} ℓ n ≫
      (ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
        (ZMod (ℓ ^ (n + 1)))))) = 0 := by
  apply Mod.hom_ext
  ext U x
  apply ULift.ext
  ext t
  change (((ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
    (ZMod (ℓ ^ (n + 1)))))).hom.hom.app U)
      ((condensedInclusion ℓ n).hom.hom.app U x)).down t = 0
  rw [condensed_smul_apply]
  change (ℓ : ZMod (ℓ ^ (n + 1))) * kernelCoefficient ℓ n (x.down t) = 0
  exact (kernelCoefficient_exact ℓ n _).2 ⟨x.down t, rfl⟩

private theorem condensedKernel_exact (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (ShortComplex.mk (condensedInclusion.{u} ℓ n)
      (ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
        (ZMod (ℓ ^ (n + 1)))))) (condensedKernel_zero ℓ n)).Exact := by
  apply condensedExact_of_sections (ZMod (ℓ ^ (n + 1)))
  intro U x
  constructor
  · intro hx
    let g : ZMod (ℓ ^ (n + 1)) → ZMod ℓ := fun z ↦
      if hz : (ℓ : ZMod (ℓ ^ (n + 1))) * z = 0 then
        Classical.choose ((kernelCoefficient_exact ℓ n z).1 hz) else 0
    let y : C(U.unop, ZMod ℓ) :=
      (⟨g, continuous_of_discreteTopology⟩ :
        C(ZMod (ℓ ^ (n + 1)), ZMod ℓ)).comp x.down
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    ext t
    have ht : (ℓ : ZMod (ℓ ^ (n + 1))) * x.down t = 0 := by
      have h := congrArg (fun z : ULift.{u + 1} C(U.unop, ZMod (ℓ ^ (n + 1))) ↦
        z.down t) hx
      rw [condensed_smul_apply] at h
      exact h
    change kernelCoefficient ℓ n (g (x.down t)) = x.down t
    dsimp only [g]
    rw [dif_pos ht]
    exact Classical.choose_spec ((kernelCoefficient_exact ℓ n (x.down t)).1 ht)
  · rintro ⟨y, rfl⟩
    apply ULift.ext
    ext t
    rw [condensed_smul_apply]
    change (ℓ : ZMod (ℓ ^ (n + 1))) * kernelCoefficient ℓ n (y.down t) = 0
    exact (kernelCoefficient_exact ℓ n _).2 ⟨y.down t, rfl⟩

private theorem condensedReduction_zero (ℓ : ℕ) (n : ℕ) :
    (ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
      (ZMod (ℓ ^ (n + 1)))))) ≫ condensedReduction.{u} ℓ n = 0 := by
  apply Mod.hom_ext
  ext U x
  apply ULift.ext
  ext t
  change ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ)
    ((((ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
      (ZMod (ℓ ^ (n + 1)))))).hom.hom.app U) x).down t) = 0
  rw [condensed_smul_apply]
  simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

private theorem condensedReduction_exact (ℓ : ℕ) (n : ℕ) :
    (ShortComplex.mk
      (ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
        (ZMod (ℓ ^ (n + 1)))))) (condensedReduction.{u} ℓ n)
      (condensedReduction_zero ℓ n)).Exact := by
  apply condensedExact_of_sections (ZMod (ℓ ^ (n + 1)))
  intro U x
  constructor
  · intro hx
    let g : ZMod (ℓ ^ (n + 1)) → ZMod (ℓ ^ (n + 1)) := fun z ↦
      if hz : ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ) z = 0 then
        Classical.choose ((residueCoefficient_exact ℓ n z).1 hz) else 0
    let y : C(U.unop, ZMod (ℓ ^ (n + 1))) :=
      (⟨g, continuous_of_discreteTopology⟩ :
        C(ZMod (ℓ ^ (n + 1)), ZMod (ℓ ^ (n + 1)))).comp x.down
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    ext t
    have ht : ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ)
        (x.down t) = 0 := by
      exact congrArg (fun z : ULift.{u + 1} C(U.unop, ZMod ℓ) ↦ z.down t) hx
    rw [condensed_smul_apply]
    change (ℓ : ZMod (ℓ ^ (n + 1))) * g (x.down t) = x.down t
    dsimp only [g]
    rw [dif_pos ht]
    exact Classical.choose_spec ((residueCoefficient_exact ℓ n (x.down t)).1 ht)
  · rintro ⟨y, rfl⟩
    apply ULift.ext
    ext t
    change ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ)
      ((((ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
        (ZMod (ℓ ^ (n + 1)))))).hom.hom.app U) y).down t) = 0
    rw [condensed_smul_apply]
    simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

private theorem condensedInclusion_mono (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Mono (condensedInclusion.{u} ℓ n) := by
  let V := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Profinite.continuousMapRingObj (ZMod (ℓ ^ (n + 1))))
  apply V.mono_of_mono_map
  apply (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mono_of_mono_map
  rw [NatTrans.mono_iff_mono_app]
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).2
  intro x y h
  apply ULift.ext
  ext t
  apply kernelCoefficient_injective ℓ n
  exact congrArg (fun z : ULift.{u + 1} C(U.unop, ZMod (ℓ ^ (n + 1))) ↦ z.down t) h

private theorem condensedReduction_epi (ℓ : ℕ) (n : ℕ) :
    Epi (condensedReduction.{u} ℓ n) := by
  let V := Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Profinite.continuousMapRingObj (ZMod (ℓ ^ (n + 1))))
  apply V.epi_of_epi_map
  apply (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).epi_of_epi_map
  rw [NatTrans.epi_iff_epi_app]
  intro U
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro x
  let q := ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero n)) (ZMod ℓ)
  let y : C(U.unop, ZMod (ℓ ^ (n + 1))) :=
    (⟨Function.surjInv (ZMod.ringHom_surjective q), continuous_of_discreteTopology⟩ :
      C(ZMod ℓ, ZMod (ℓ ^ (n + 1)))).comp x.down
  refine ⟨ULift.up y, ?_⟩
  apply ULift.ext
  ext t
  exact Function.surjInv_eq (ZMod.ringHom_surjective q) (x.down t)

private def sheafInclusion (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    k ℓ X n ⟶ unit X (finiteRing ℓ X n) :=
  (coefficientResidueIso ℓ X n).inv ≫
    (coefficientFunctor X (ZMod (ℓ ^ (n + 1)))).map (condensedInclusion ℓ n) ≫
      (coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))).hom

private def sheafReduction (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    unit X (finiteRing ℓ X n) ⟶ k ℓ X n :=
  (coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))).inv ≫
    (coefficientFunctor X (ZMod (ℓ ^ (n + 1)))).map (condensedReduction ℓ n) ≫
      (coefficientResidueIso ℓ X n).hom

private theorem sheafInclusion_underlying (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    HEq ((SheafOfModules.toSheaf _).map (sheafInclusion ℓ X n))
      ((upperStarFromPoint X).map
        (additiveMap (kernelCoefficient ℓ n) continuous_of_discreteTopology)) := by
  rfl

private theorem sheafReduction_sections (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ)
    (U : X.ProEtᵒᵖ) (x : (unit X (finiteRing ℓ X n)).val.obj U) :
    (sheafReduction ℓ X n).val.app U x = ((residue ℓ X n).hom.app U).hom x := by
  rfl

-- Transport exactness through the named isomorphisms without unfolding their data.
attribute [local irreducible] coefficientFunctor coefficientRegularIso coefficientResidueIso

private theorem sheafKernel_zero (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    sheafInclusion ℓ X n ≫ (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) = 0 := by
  let F := coefficientFunctor X (ZMod (ℓ ^ (n + 1)))
  let e := coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))
  have h : (ℓ • F.map (condensedInclusion.{u} ℓ n)) = 0 := by
    simpa only [Functor.map_comp, Functor.map_nsmul, Functor.map_id, Functor.map_zero,
      comp_nsmul, Category.comp_id] using congrArg F.map (condensedKernel_zero ℓ n)
  dsimp only [sheafInclusion, finiteRing]
  simpa only [comp_nsmul, nsmul_comp, Category.comp_id, comp_zero, zero_comp] using
    congrArg (fun f ↦ (coefficientResidueIso ℓ X n).inv ≫ f ≫ e.hom) h

private theorem sheafReduction_zero (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) ≫ sheafReduction ℓ X n = 0 := by
  let F := coefficientFunctor X (ZMod (ℓ ^ (n + 1)))
  let e := coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))
  have h : (ℓ • F.map (condensedReduction.{u} ℓ n)) = 0 := by
    simpa only [Functor.map_comp, Functor.map_nsmul, Functor.map_id, Functor.map_zero,
      nsmul_comp, Category.id_comp] using congrArg F.map (condensedReduction_zero ℓ n)
  dsimp only [sheafReduction, finiteRing]
  simpa only [comp_nsmul, nsmul_comp, Category.id_comp, comp_zero, zero_comp] using
    congrArg (fun f ↦ e.inv ≫ f ≫ (coefficientResidueIso ℓ X n).hom) h

private theorem mapScalar_iso {A B : Type*} [Category A] [Preadditive A]
    [Category B] [Preadditive B] (F : A ⥤ B) [F.Additive]
    (M : A) (L : B) (e : F.obj M ≅ L) (m : ℕ) :
    e.hom ≫ (m • 𝟙 L) = F.map (m • 𝟙 M) ≫ e.hom := by
  rw [F.map_nsmul, F.map_id, comp_nsmul, nsmul_comp,
    Category.comp_id, Category.id_comp]

private theorem sheafKernel_exact (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    (ShortComplex.mk (sheafInclusion ℓ X n) (ℓ • 𝟙 (unit X (finiteRing ℓ X n)))
      (sheafKernel_zero ℓ X n)).Exact := by
  let F := coefficientFunctor X (ZMod (ℓ ^ (n + 1)))
  have hF := coefficientFunctor_exact X (ZMod (ℓ ^ (n + 1)))
  have : PreservesFiniteLimits F := hF.1
  have : PreservesFiniteColimits F := hF.2
  let S := ShortComplex.mk (condensedInclusion.{u} ℓ n)
    (ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
      (ZMod (ℓ ^ (n + 1)))))) (condensedKernel_zero ℓ n)
  let e : S.map F ≅ ShortComplex.mk (sheafInclusion ℓ X n)
      (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) (sheafKernel_zero ℓ X n) :=
    ShortComplex.isoMk (coefficientResidueIso ℓ X n)
      (coefficientRegularIso X (ZMod (ℓ ^ (n + 1))))
      (coefficientRegularIso X (ZMod (ℓ ^ (n + 1))))
      (by simp [S, F, sheafInclusion])
      (mapScalar_iso F _ _ (coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))) ℓ)
  exact ShortComplex.exact_of_iso e ((condensedKernel_exact ℓ n).map F)

private theorem sheafReduction_exact (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    (ShortComplex.mk (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) (sheafReduction ℓ X n)
      (sheafReduction_zero ℓ X n)).Exact := by
  let F := coefficientFunctor X (ZMod (ℓ ^ (n + 1)))
  have hF := coefficientFunctor_exact X (ZMod (ℓ ^ (n + 1)))
  have : PreservesFiniteLimits F := hF.1
  have : PreservesFiniteColimits F := hF.2
  let S := ShortComplex.mk
    (ℓ • 𝟙 (Mod.regular (Profinite.continuousMapRingObj.{u}
      (ZMod (ℓ ^ (n + 1)))))) (condensedReduction.{u} ℓ n)
      (condensedReduction_zero ℓ n)
  let e : S.map F ≅ ShortComplex.mk (ℓ • 𝟙 (unit X (finiteRing ℓ X n)))
      (sheafReduction ℓ X n) (sheafReduction_zero ℓ X n) :=
    ShortComplex.isoMk (coefficientRegularIso X (ZMod (ℓ ^ (n + 1))))
      (coefficientRegularIso X (ZMod (ℓ ^ (n + 1))))
      (coefficientResidueIso ℓ X n)
      (mapScalar_iso F _ _ (coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))) ℓ)
      (by simp [S, F, sheafReduction])
  exact ShortComplex.exact_of_iso e ((condensedReduction_exact ℓ n).map F)

private theorem sheafInclusion_mono (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) (n : ℕ) : Mono (sheafInclusion ℓ X n) := by
  have hF := coefficientFunctor_exact X (ZMod (ℓ ^ (n + 1)))
  have : PreservesFiniteLimits (coefficientFunctor X (ZMod (ℓ ^ (n + 1)))) := hF.1
  have := condensedInclusion_mono.{u} ℓ n
  dsimp only [sheafInclusion, finiteRing]
  apply mono_comp'
    (IsIso.mono_of_iso (coefficientResidueIso ℓ X n).inv)
  exact mono_comp'
    (Functor.map_mono (coefficientFunctor X (ZMod (ℓ ^ (n + 1))))
      (condensedInclusion ℓ n))
    (IsIso.mono_of_iso (coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))).hom)

private theorem sheafReduction_epi (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    Epi (sheafReduction ℓ X n) := by
  have hF := coefficientFunctor_exact X (ZMod (ℓ ^ (n + 1)))
  have : PreservesFiniteColimits (coefficientFunctor X (ZMod (ℓ ^ (n + 1)))) := hF.2
  have := condensedReduction_epi.{u} ℓ n
  dsimp only [sheafReduction, finiteRing]
  apply epi_comp'
    (IsIso.epi_of_iso (coefficientRegularIso X (ZMod (ℓ ^ (n + 1)))).inv)
  exact epi_comp'
    (Functor.map_epi (coefficientFunctor X (ZMod (ℓ ^ (n + 1))))
      (condensedReduction ℓ n))
    (IsIso.epi_of_iso (coefficientResidueIso ℓ X n).hom)

private theorem minusFork_condition (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ) :
    (sheafInclusion ℓ X n ≫ (termMinus ℓ X (finiteRing ℓ X n)).inv) ≫
      (complex ℓ X (finiteRing ℓ X n)).d (-1) 0 = 0 := by
  have hd : (complex ℓ X (finiteRing ℓ X n)).d (-1) 0 =
      (termMinus ℓ X (finiteRing ℓ X n)).hom ≫
        (ℓ • 𝟙 _) ≫ (termZero ℓ X (finiteRing ℓ X n)).inv :=
    HomologicalComplex.double_d _ _ (by decide)
  rw [hd]
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    sheafKernel_zero, zero_comp]

private def minusFork_limit (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ) :
    IsLimit (KernelFork.ofι
      (sheafInclusion ℓ X n ≫ (termMinus ℓ X (finiteRing ℓ X n)).inv)
      (minusFork_condition ℓ X n)) := by
  let P := complex ℓ X (finiteRing ℓ X n)
  let e₀ := termMinus ℓ X (finiteRing ℓ X n)
  let e₁ := termZero ℓ X (finiteRing ℓ X n)
  let i := sheafInclusion ℓ X n ≫ e₀.inv
  have hd : P.d (-1) 0 = e₀.hom ≫ (ℓ • 𝟙 _) ≫ e₁.inv :=
    HomologicalComplex.double_d _ _ (by decide)
  have hzero : i ≫ (P.sc' (-2) (-1) 0).g = 0 := by
    change i ≫ P.d (-1) 0 = 0
    rw [hd]
    dsimp only [i]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      sheafKernel_zero, zero_comp]
  have := sheafInclusion_mono ℓ X n
  have : Mono i := by dsimp only [i]; infer_instance
  have hz : P.d (-2) (-1) = 0 :=
    HomologicalComplex.double_d_eq_zero₀ (c := .up ℤ)
      (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) (by decide) (-2) (-1) (by decide)
  apply KernelFork.IsLimit.ofι' i hzero
  intro A f hf
  change f ≫ P.d (-1) 0 = 0 at hf
  have hf' : (f ≫ e₀.hom) ≫ (ℓ • 𝟙 _) = 0 := by
    rw [← cancel_mono e₁.inv]
    simpa only [Category.assoc, ← hd, zero_comp] using hf
  refine ⟨(sheafKernel_exact ℓ X n).lift (f ≫ e₀.hom) hf', ?_⟩
  dsimp only [i]
  have hl : (sheafKernel_exact ℓ X n).lift (f ≫ e₀.hom) hf' ≫
      sheafInclusion ℓ X n = f ≫ e₀.hom :=
    (sheafKernel_exact ℓ X n).lift_f _ _
  rw [← Category.assoc, hl]
  simp

private theorem zeroCofork_condition (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    (complex ℓ X (finiteRing ℓ X n)).d (-1) 0 ≫
      ((termZero ℓ X (finiteRing ℓ X n)).hom ≫ sheafReduction ℓ X n) = 0 := by
  have hd : (complex ℓ X (finiteRing ℓ X n)).d (-1) 0 =
      (termMinus ℓ X (finiteRing ℓ X n)).hom ≫
        (ℓ • 𝟙 _) ≫ (termZero ℓ X (finiteRing ℓ X n)).inv :=
    HomologicalComplex.double_d _ _ (by decide)
  rw [hd]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    sheafReduction_zero, comp_zero]

private def zeroCofork_colimit (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      ((termZero ℓ X (finiteRing ℓ X n)).hom ≫ sheafReduction ℓ X n)
      (zeroCofork_condition ℓ X n)) := by
  let P := complex ℓ X (finiteRing ℓ X n)
  let e₀ := termMinus ℓ X (finiteRing ℓ X n)
  let e₁ := termZero ℓ X (finiteRing ℓ X n)
  let f := e₁.hom ≫ sheafReduction ℓ X n
  have hd : P.d (-1) 0 = e₀.hom ≫ (ℓ • 𝟙 _) ≫ e₁.inv :=
    HomologicalComplex.double_d _ _ (by decide)
  have hzero : (P.sc' (-1) 0 1).f ≫ f = 0 := by
    change P.d (-1) 0 ≫ f = 0
    rw [hd]
    dsimp only [f]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      sheafReduction_zero, comp_zero]
  have := sheafReduction_epi ℓ X n
  have : Epi f := by dsimp only [f]; infer_instance
  have hz : P.d 0 1 = 0 :=
    HomologicalComplex.double_d_eq_zero₀ (c := .up ℤ)
      (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) (by decide) 0 1 (by decide)
  apply CokernelCofork.IsColimit.ofπ' f hzero
  intro A g hg
  change P.d (-1) 0 ≫ g = 0 at hg
  have hg' : (ℓ • 𝟙 _) ≫ (e₁.inv ≫ g) = 0 := by
    rw [← cancel_epi e₀.hom]
    simpa only [← Category.assoc, ← hd, comp_zero] using hg
  refine ⟨(sheafReduction_exact ℓ X n).desc (e₁.inv ≫ g) hg', ?_⟩
  dsimp only [f]
  have hg : sheafReduction ℓ X n ≫
      (sheafReduction_exact ℓ X n).desc (e₁.inv ≫ g) hg' = e₁.inv ≫ g :=
    (sheafReduction_exact ℓ X n).g_desc _ _
  rw [Category.assoc, hg]
  simp


private def minusHomologyData (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ) :
    ((complex ℓ X (finiteRing ℓ X n)).sc' (-2) (-1) 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsLimitKernelFork _
    (HomologicalComplex.double_d_eq_zero₀ (c := .up ℤ)
      (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) (by decide) (-2) (-1) (by decide))
    (KernelFork.ofι
      (sheafInclusion ℓ X n ≫ (termMinus ℓ X (finiteRing ℓ X n)).inv)
      (minusFork_condition ℓ X n)) (minusFork_limit ℓ X n)

private def zeroHomologyData (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    ((complex ℓ X (finiteRing ℓ X n)).sc' (-1) 0 1).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork _
    (HomologicalComplex.double_d_eq_zero₀ (c := .up ℤ)
      (ℓ • 𝟙 (unit X (finiteRing ℓ X n))) (by decide) 0 1 (by decide))
    (CokernelCofork.ofπ
      ((termZero ℓ X (finiteRing ℓ X n)).hom ≫ sheafReduction ℓ X n)
      (zeroCofork_condition ℓ X n)) (zeroCofork_colimit ℓ X n)

private def minusIso (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ) :
    (complex ℓ X (finiteRing ℓ X n)).homology (-1) ≅ k ℓ X n :=
  (complex ℓ X (finiteRing ℓ X n)).homologyIsoSc' (-2) (-1) 0
    (by simp) (by simp) ≪≫ (minusHomologyData ℓ X n).homologyIso

private def zeroIso (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    (complex ℓ X (finiteRing ℓ X n)).homology 0 ≅ k ℓ X n :=
  (complex ℓ X (finiteRing ℓ X n)).homologyIsoSc' (-1) 0 1
    (by simp) (by simp) ≪≫ (zeroHomologyData ℓ X n).homologyIso

private theorem minusIso_normalization (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    (complex ℓ X (finiteRing ℓ X n)).homologyπ (-1) ≫
      (minusIso ℓ X n).hom ≫ sheafInclusion ℓ X n =
      (complex ℓ X (finiteRing ℓ X n)).iCycles (-1) ≫
        (termMinus ℓ X (finiteRing ℓ X n)).hom := by
  let P := complex ℓ X (finiteRing ℓ X n)
  let h := minusHomologyData ℓ X n
  have hi := h.cyclesIso_hom_comp_i
  dsimp only [minusIso, Iso.trans_hom]
  simp only [Category.assoc]
  erw [HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    h.homologyπ_comp_homologyIso_hom_assoc]
  change _ ≫ h.cyclesIso.hom ≫ 𝟙 _ ≫ sheafInclusion ℓ X n = _
  rw [Category.id_comp]
  rw [← cancel_mono (termMinus ℓ X (finiteRing ℓ X n)).inv]
  have hi' : h.cyclesIso.hom ≫ sheafInclusion ℓ X n ≫
      (termMinus ℓ X (finiteRing ℓ X n)).inv = (P.sc' (-2) (-1) 0).iCycles := hi
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hi', HomologicalComplex.cyclesIsoSc'_hom_iCycles]

private theorem zeroIso_normalization (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    (complex ℓ X (finiteRing ℓ X n)).homologyπ 0 ≫ (zeroIso ℓ X n).hom =
      (complex ℓ X (finiteRing ℓ X n)).iCycles 0 ≫
        (termZero ℓ X (finiteRing ℓ X n)).hom ≫ sheafReduction ℓ X n := by
  let P := complex ℓ X (finiteRing ℓ X n)
  let h := zeroHomologyData ℓ X n
  have hi := h.cyclesIso_hom_comp_i
  have hi' : h.cyclesIso.hom = (P.sc' (-1) 0 1).iCycles := by
    simpa only [h, zeroHomologyData,
      ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork, Category.comp_id] using hi
  dsimp only [zeroIso, Iso.trans_hom]
  rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom, Category.assoc,
    h.homologyπ_comp_homologyIso_hom]
  change _ ≫ h.cyclesIso.hom ≫
    (termZero ℓ X (finiteRing ℓ X n)).hom ≫ sheafReduction ℓ X n = _
  rw [hi', ← Category.assoc, HomologicalComplex.cyclesIsoSc'_hom_iCycles]

-- Use the normalization lemmas without unfolding chosen homology data.
attribute [local irreducible] minusIso zeroIso sheafInclusion sheafReduction

private theorem mapHomologyIso_π {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (S : ShortComplex A) [S.HasHomology] (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [(S.leftHomologyData.map F).homologyπ_comp_homologyIso_hom_assoc]
  simp only [ShortComplex.LeftHomologyData.homologyIso_leftHomologyData,
    Iso.symm_inv]
  change (S.mapCyclesIso F).hom ≫ F.map S.leftHomologyπ ≫
    F.map S.leftHomologyIso.hom = _
  rw [← F.map_comp]
  rfl

private theorem restriction_finiteLimits (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (restriction.{u + 1, u, u + 1} a) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose

attribute [local instance] restriction_finiteLimits

private theorem restriction_finiteColimits (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits (restriction.{u + 1, u, u + 1} a) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose_spec.choose

attribute [local instance] restriction_finiteColimits

private theorem homologyMap_restrict_π (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ)
    (Q : CochainComplex (Modules.{u + 1, u, u + 1} S) ℤ)
    (f : P ⟶ ((restriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ)).obj Q)
    (q : ℤ) :
    P.homologyπ q ≫ HomologicalComplex.homologyMap f q ≫
      (restrictHomology X a Q q).hom =
      HomologicalComplex.cyclesMap f q ≫
        ((Q.sc q).mapCyclesIso (restriction.{u + 1, u, u + 1} a)).hom ≫
          (restriction.{u + 1, u, u + 1} a).map (Q.homologyπ q) := by
  change P.homologyπ q ≫ HomologicalComplex.homologyMap f q ≫
    ((Q.sc q).mapHomologyIso (restriction.{u + 1, u, u + 1} a)).hom = _
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [Category.assoc]
  exact congrArg (HomologicalComplex.cyclesMap f q ≫ ·)
    (mapHomologyIso_π (Q.sc q) (restriction.{u + 1, u, u + 1} a))

private theorem homologyMap_restrict_cycles (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ)
    (Q : CochainComplex (Modules.{u + 1, u, u + 1} S) ℤ)
    (f : P ⟶ ((restriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ)).obj Q)
    (q : ℤ) :
    HomologicalComplex.cyclesMap f q ≫
      ((Q.sc q).mapCyclesIso (restriction.{u + 1, u, u + 1} a)).hom ≫
        (restriction.{u + 1, u, u + 1} a).map (Q.iCycles q) =
      P.iCycles q ≫ f.f q := by
  calc
    _ = HomologicalComplex.cyclesMap f q ≫
        ((Q.sc q).map (restriction.{u + 1, u, u + 1} a)).iCycles :=
      congrArg (HomologicalComplex.cyclesMap f q ≫ ·)
        ((Q.sc q).mapCyclesIso_hom_iCycles (restriction.{u + 1, u, u + 1} a))
    _ = _ := HomologicalComplex.cyclesMap_i f q

attribute [local irreducible] restrictHomology

private theorem kernelCoefficient_step (ℓ : ℕ) (n : ℕ) (x : ZMod ℓ) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
      (kernelCoefficient ℓ (n + 1) x) = 0 := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simp only [kernelCoefficient_int, map_mul, map_pow, map_natCast, map_intCast]
  rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]

private theorem homology_other (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (q : ℤ) (h₀ : q ≠ -1) (h₁ : q ≠ 0) :
    IsZero ((complex ℓ X R).homology q) :=
  ((complex ℓ X R).sc q).isZero_homology_of_isZero_X₂
    (HomologicalComplex.isZero_double_X (ℓ • 𝟙 (unit X R))
      (c := ComplexShape.up ℤ) (by decide) q h₀ h₁)

private theorem flat_unit (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := R) (unit X R) := by
  apply (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (unit X R)).symm
  apply (exactFunctor _ _).prop_of_iso (rightUnitorNatIso (Modules.{u + 1, u, u + 1} R)).symm
  change PreservesFiniteLimits (𝟭 (Modules.{u + 1, u, u + 1} R)) ∧
    PreservesFiniteColimits (𝟭 (Modules.{u + 1, u, u + 1} R))
  exact ⟨inferInstance, inferInstance⟩

private theorem flat_zero (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : Modules.{u + 1, u, u + 1} R) (hM : IsZero M) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := R) M := by
  apply (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R M).symm
  have hz : IsZero (tensorRight M) := by
    rw [Functor.isZero_iff]
    intro N
    exact (tensorLeft N).map_isZero hM
  exact ⟨⟨fun _ _ _ ↦ (tensorRight M).preservesLimitsOfShape_of_isZero hz _⟩,
    ⟨fun _ _ _ ↦ (tensorRight M).preservesColimitsOfShape_of_isZero hz _⟩⟩

private theorem complex_term_minus (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (complex ℓ X R).X (-1) = unit X R := by
  dsimp only [complex, HomologicalComplex.double]
  exact if_pos rfl

private theorem complex_term_zero (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (complex ℓ X R).X 0 = unit X R := by
  dsimp only [complex, HomologicalComplex.double]
  rw [if_neg (by decide), if_pos rfl]
  rfl

private theorem flat_terms (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (i : ℤ) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := R) ((complex ℓ X R).X i) := by
  by_cases h₀ : i = -1
  · subst i
    rw [complex_term_minus]
    exact flat_unit X R
  by_cases h₁ : i = 0
  · subst i
    rw [complex_term_zero]
    exact flat_unit X R
  exact flat_zero X R _ (HomologicalComplex.isZero_double_X _ _ _ h₀ h₁)

private theorem kflat_complex (ℓ : ℕ) (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) (complex ℓ X R) := by
  have : (complex ℓ X R).IsStrictlyLE 0 :=
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦
      HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega))
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R
    (complex ℓ X R) 0 (flat_terms ℓ X R)



private def ordinaryComplexIso (ℓ : ℕ) (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : Presentation.{u + 1, u, u + 1, w} a) :
    (p.ordinary.mapHomologicalComplex (.up ℤ)).obj (complex ℓ X R) ≅ complex ℓ X S :=
  doubleScalarIso p.ordinary ℓ (unit X R) (unit X S) (scalarUnitIso X a p)

private def derivedComplexIso (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (p a).derived.obj (localized X R (complex ℓ X R)) ≅
      localized X S (complex ℓ X S) := by
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj (complex ℓ X R)
  have : IsIso ((p a).counit.app H) :=
    N.computed a (complex ℓ X R) (kflat_complex ℓ X R) (flat_terms ℓ X R)
  exact asIso ((p a).counit.app H) ≪≫ DerivedCategory.Qh.mapIso
    (((p a).ordinary.mapHomotopyCategoryFactors (.up ℤ)).app (complex ℓ X R) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso (ordinaryComplexIso ℓ X a (p a)))

private def constantToContinuous (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (Profinite.continuousMapRingObj.{u} A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

private theorem constantToContinuous_locallySurjective (A : Type) [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (constantToContinuous.{u} A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    let : Fintype (Set.range f) :=
      ((IsLocallyConstant.iff_continuous f).2 f.continuous).range_finite.fintype
    let I := Fin (Fintype.card (Set.range f))
    let e : I ≃ Set.range f := (Fintype.equivFin (Set.range f)).symm
    have hclosed (i : I) : IsClosed {x : S | f x = (e i).val} :=
      isClosed_singleton.preimage f.continuous
    let (i : I) : CompactSpace {x : S // f x = (e i).val} :=
      isCompact_iff_compactSpace.mp (hclosed i).isCompact
    let U (i : I) : Profinite.{u} := Profinite.of {x : S // f x = (e i).val}
    let incl (i : I) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl := by
      apply Profinite.effectiveEpiFamily_of_jointly_surjective U incl
      intro x
      refine ⟨e.symm ⟨f x, ⟨x, rfl⟩⟩, ⟨x, ?_⟩, rfl⟩
      simp
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨I, inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i).val, ?_⟩
    apply ULift.ext
    ext x
    exact x.property.symm

private theorem constantToContinuous_locallyInjective (A : Type) [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (constantToContinuous.{u} A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext a b (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private def constantResidueIso (ℓ : ℕ) (X : Scheme.{u}) :
    (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} _).obj
      (unit X (ring X (ZMod ℓ))) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) := by
  let J := coherentTopology Profinite.{u}
  have := constantToContinuous_locallyInjective.{u} (ZMod ℓ)
  have := constantToContinuous_locallySurjective.{u} (ZMod ℓ)
  have h : J.W (A := Ab.{u + 1}) (constantToContinuous.{u} (ZMod ℓ)) :=
    J.W_of_isLocallyBijective _
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map (constantToContinuous.{u} (ZMod ℓ))) :=
    (J.W_iff _).1 h
  let e := asIso ((presheafToSheaf J Ab.{u + 1}).map
    (constantToContinuous.{u} (ZMod ℓ))) ≪≫
      (sheafificationNatIso J Ab.{u + 1}).symm.app
        (Profinite.continuousMapRingObj.{u} (ZMod ℓ))
  exact ((upperStarFromPoint X).mapIso e).symm ≪≫
    (constantSchemeIso X).symm.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))

private theorem residue_nonzero (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (n : ℕ) :
    ¬ IsZero (k ℓ (Spec (.of Ω)) n) := by
  let X := Spec (.of Ω)
  let J := Scheme.ProEt.topology X
  let U : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have : Nonempty U.left := by
    change Nonempty (PrimeSpectrum Ω)
    infer_instance
  have hbot : (⊥ : Sieve U) ∉ J U := by
    intro h
    obtain ⟨Q, hQ, hQS⟩ := Scheme.ProEt.mem_topology_iff.mp h
    obtain ⟨ι, V, f, rfl⟩ := Q.exists_eq_ofArrows
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hQ
    obtain ⟨i, y, hy⟩ :=
      ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 hQ.2).1
        (Classical.arbitrary U.left)
    have hf := hQS _ _ (Presieve.ofArrows.mk i)
    simp at hf
  intro hz
  let W := SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u} J
      (finiteRing ℓ X n))
  have hzero := W.map_isZero hz
  change IsZero ((SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} _).obj
      (unit X (ring X (ZMod ℓ)))) at hzero
  have hc := hzero.of_iso (constantResidueIso ℓ X).symm
  have he := ((sheafSections J Ab.{u + 1}).obj (op U)).map_isZero hc
  have hsub : Subsingleton (((constantSheaf J Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))).obj.obj (op U)) :=
    AddCommGrpCat.subsingleton_of_isZero he
  have hinj := J.toSheafify_const_app_injective
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) hbot
  have h01 : (0 : ULift.{u + 1} (ZMod ℓ)) = 1 :=
    hinj (@Subsingleton.elim _ hsub _ _)
  exact zero_ne_one (congrArg ULift.down h01)

private theorem step_residue (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    step ℓ X n ≫ residue ℓ X n = residue ℓ X (n + 1) := by
  rw [step, residue, map_comp]
  congr 1
  exact Subsingleton.elim _ _

private def restrictionCompositeIso (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules.{u + 1, u, u + 1} T) :
    (restriction.{u + 1, u, u + 1} c).obj M ≅
      (restriction.{u + 1, u, u + 1} a).obj
        ((restriction.{u + 1, u, u + 1} b).obj M) := by
  have hU (U : X.ProEtᵒᵖ) :
      (c.hom.app U).hom = (b.hom.app U).hom.comp (a.hom.app U).hom :=
    (congrArg CommRingCat.Hom.hom (congr_app (congrArg (fun f ↦ f.hom) h) U)).symm
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦
    ModuleCat.restrictScalarsComp'App (a.hom.app U).hom
      (b.hom.app U).hom (c.hom.app U).hom (hU U) (M.val.obj U)) ?_
  intro U V f
  rfl

private def residueIdentityIso (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    k ℓ X (n + 1) ≅ (restriction.{u + 1, u, u + 1} (step ℓ X n)).obj (k ℓ X n) :=
  restrictionCompositeIso X (step ℓ X n) (residue ℓ X n) (residue ℓ X (n + 1))
    (step_residue ℓ X n) (unit X (ring X (ZMod ℓ)))

private def residueIdentity (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    k ℓ X (n + 1) ⟶ (restriction.{u + 1, u, u + 1} (step ℓ X n)).obj (k ℓ X n) :=
  (residueIdentityIso ℓ X n).hom

private theorem residueIdentity_underlying (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    HEq ((SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} _).map (residueIdentity ℓ X n))
      (𝟙 ((SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} _).obj
      (unit X (ring X (ZMod ℓ))))) := by
  rfl

private def identityInverse (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf (Scheme.ProEt.topology X)
      (Type (u + 1)))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules.{u + 1, u, u + 1} R)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private theorem sectionTensor_smul_one (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} {a : R ⟶ S}
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : Presentation.{u + 1, u, u + 1, w} a)
    (M : Modules.{u + 1, u, u + 1} R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor p M U s x = s • sectionTensor p M U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (Scheme.ProEt.topology X) S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M)
  change (eqToHom (p.obj_eq M).symm).val.app U
      (η.app U (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)) =
    s • (eqToHom (p.obj_eq M).symm).val.app U
      (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x))
  rw [← ((eqToHom (p.obj_eq M).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x =
    (s * 1) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x
  rw [mul_one]

private theorem sectionSMul_eq_smul (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (M : Modules.{u + 1, u, u + 1} R) (U : X.ProEtᵒᵖ)
    (b : R.obj.obj U) (x : M.val.obj U) : sectionSMul X R M U b x = b • x := by
  rfl

private theorem ordinaryMate_sections (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : Modules.{u + 1, u, u + 1} R) (L : Modules.{u + 1, u, u + 1} S)
    (g : M ⟶ (restriction a).obj L) (U : X.ProEtᵒᵖ)
    (b : S.obj.obj U) (x : M.val.obj U) :
    (((N.ordinaryAdjunction a).homEquiv M L).symm g).val.app U
      (sectionTensor (p a) M U b x) = sectionSMul X S L U b (g.val.app U x) := by
  let f := ((N.ordinaryAdjunction a).homEquiv M L).symm g
  have h : (N.ordinaryAdjunction a).unit.app M ≫ (restriction a).map f = g := by
    change (N.ordinaryAdjunction a).homEquiv _ _ f = g
    exact Equiv.apply_symm_apply _ g
  have hx := congrArg (fun k ↦ k.val.app U x) h
  change f.val.app U (((N.ordinaryAdjunction a).unit.app M).val.app U x) =
    g.val.app U x at hx
  rw [N.ordinary_unit] at hx
  change f.val.app U (sectionTensor (p a) M U b x) =
    @SMul.smul _ _ (L.val.obj U).isModule.toSMul b (g.val.app U x)
  rw [sectionTensor_smul_one, (f.val.app U).hom.map_smul, hx]
  rfl

private theorem ordinary_map_sections (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M L : Modules.{u + 1, u, u + 1} R} (f : M ⟶ L)
    (U : X.ProEtᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U) :
    ((p a).ordinary.map f).val.app U (sectionTensor (p a) M U b x) =
      sectionTensor (p a) L U b (f.val.app U x) := by
  have h := congrArg (fun g ↦ g.val.app U x)
    ((N.ordinaryAdjunction a).unit.naturality f)
  change (((N.ordinaryAdjunction a).unit.app L).val.app U) (f.val.app U x) =
    ((p a).ordinary.map f).val.app U
      (((N.ordinaryAdjunction a).unit.app M).val.app U x) at h
  rw [N.ordinary_unit, N.ordinary_unit] at h
  calc
    _ = b • (((p a).ordinary.map f).val.app U
        (sectionTensor (p a) M U 1 x)) := by
      rw [sectionTensor_smul_one]
      exact (((p a).ordinary.map f).val.app U).hom.map_smul b _
    _ = b • sectionTensor (p a) L U 1 (f.val.app U x) := congrArg (b • ·) h.symm
    _ = _ := (sectionTensor_smul_one X (p a) L U b (f.val.app U x)).symm

private theorem ordinaryComplexIso_minus (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (p : Presentation.{u + 1, u, u + 1, w} a) :
    (ordinaryComplexIso ℓ X a p).hom.f (-1) ≫ (termMinus ℓ X S).hom =
      p.ordinary.map (termMinus ℓ X R).hom ≫ (scalarUnitIso X a p).hom := by
  let e := ordinaryComplexIso ℓ X a p
  have hi : e.inv.f (-1) =
      (termMinus ℓ X S).hom ≫ (scalarUnitIso X a p).inv ≫
        p.ordinary.map (termMinus ℓ X R).inv := by
    dsimp only [e, ordinaryComplexIso, doubleScalarIso, Iso.symm_inv, asIso_hom]
    exact HomologicalComplex.mkHomFromDouble_f₀ ..
  have hc : e.inv.f (-1) ≫ e.hom.f (-1) = 𝟙 _ :=
    congrArg (fun f ↦ f.f (-1)) e.inv_hom_id
  have : Epi (e.inv.f (-1)) := inferInstance
  apply (cancel_epi (e.inv.f (-1))).mp
  erw [← Category.assoc, hc, Category.id_comp, hi]
  simp only [Category.assoc, ← p.ordinary.map_comp_assoc, Iso.inv_hom_id]
  erw [p.ordinary.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem ordinaryComplexIso_zero (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (p : Presentation.{u + 1, u, u + 1, w} a) :
    (ordinaryComplexIso ℓ X a p).hom.f 0 ≫ (termZero ℓ X S).hom =
      p.ordinary.map (termZero ℓ X R).hom ≫ (scalarUnitIso X a p).hom := by
  let e := ordinaryComplexIso ℓ X a p
  have hi : e.inv.f 0 =
      (termZero ℓ X S).hom ≫ (scalarUnitIso X a p).inv ≫
        p.ordinary.map (termZero ℓ X R).inv := by
    dsimp only [e, ordinaryComplexIso, doubleScalarIso, Iso.symm_inv, asIso_hom]
    exact HomologicalComplex.mkHomFromDouble_f₁ ..
  have hc : e.inv.f 0 ≫ e.hom.f 0 = 𝟙 _ :=
    congrArg (fun f ↦ f.f 0) e.inv_hom_id
  have : Epi (e.inv.f 0) := inferInstance
  apply (cancel_epi (e.inv.f 0)).mp
  erw [← Category.assoc, hc, Category.id_comp, hi]
  simp only [Category.assoc, ← p.ordinary.map_comp_assoc, Iso.inv_hom_id]
  erw [p.ordinary.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem ordinaryComplexIso_minus_sections (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEtᵒᵖ) (b : S.obj.obj U)
    (r : ((complex ℓ X R).X (-1)).val.obj U) :
    (termMinus ℓ X S).hom.val.app U
      (((ordinaryComplexIso ℓ X a (p a)).hom.f (-1)).val.app U
        (sectionTensor (p a) _ U b r)) =
      (a.hom.app U).hom ((termMinus ℓ X R).hom.val.app U r) * b := by
  have h := congrArg (fun f ↦ f.val.app U (sectionTensor (p a) _ U b r))
    (ordinaryComplexIso_minus ℓ X a (p a))
  change (termMinus ℓ X S).hom.val.app U
    (((ordinaryComplexIso ℓ X a (p a)).hom.f (-1)).val.app U
      (sectionTensor (p a) _ U b r)) =
    (scalarUnitIso X a (p a)).hom.val.app U
      (((p a).ordinary.map (termMinus ℓ X R).hom).val.app U
        (sectionTensor (p a) _ U b r)) at h
  rw [ordinary_map_sections X p N, scalarUnitIso_sections] at h
  exact h

private theorem ordinaryComplexIso_zero_sections (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEtᵒᵖ) (b : S.obj.obj U) (r : ((complex ℓ X R).X 0).val.obj U) :
    (termZero ℓ X S).hom.val.app U
      (((ordinaryComplexIso ℓ X a (p a)).hom.f 0).val.app U
        (sectionTensor (p a) _ U b r)) =
      (a.hom.app U).hom ((termZero ℓ X R).hom.val.app U r) * b := by
  have h := congrArg (fun f ↦ f.val.app U (sectionTensor (p a) _ U b r))
    (ordinaryComplexIso_zero ℓ X a (p a))
  change (termZero ℓ X S).hom.val.app U
    (((ordinaryComplexIso ℓ X a (p a)).hom.f 0).val.app U
      (sectionTensor (p a) _ U b r)) =
    (scalarUnitIso X a (p a)).hom.val.app U
      (((p a).ordinary.map (termZero ℓ X R).hom).val.app U
        (sectionTensor (p a) _ U b r)) at h
  rw [ordinary_map_sections X p N, scalarUnitIso_sections] at h
  exact h

private theorem eqToHom_apply_heq (X : Scheme.{u})
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    {M L : Modules.{u + 1, u, u + 1} R} (h : M = L)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst L
  rfl

private theorem ordinaryComplexIso_sections (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (i : ℤ) (hi : i = -1 ∨ i = 0) (U : X.ProEtᵒᵖ) (b : S.obj.obj U)
    (r : ((complex ℓ X R).X i).val.obj U) :
    HEq (((ordinaryComplexIso ℓ X a (p a)).hom.f i).val.app U
      (sectionTensor (p a) _ U b r))
      (b • (a.hom.app U).hom
        ((if hi' : i = -1 then
          (eqToHom (congrArg (fun j ↦ (complex ℓ X R).X j) hi') ≫
            (termMinus ℓ X R).hom).val.app U r
        else
          (eqToHom (congrArg (fun j ↦ (complex ℓ X R).X j) (hi.resolve_left hi')) ≫
            (termZero ℓ X R).hom).val.app U r))) := by
  rcases hi with rfl | rfl
  · have h := ordinaryComplexIso_minus_sections ℓ X p N a U b r
    have ht := eqToHom_apply_heq X (complex_term_minus ℓ X S) U
      (((ordinaryComplexIso ℓ X a (p a)).hom.f (-1)).val.app U
        (sectionTensor (p a) _ U b r))
    have hh := ht.symm.trans (heq_of_eq h)
    simpa [smul_eq_mul, mul_comm] using hh
  · have h := ordinaryComplexIso_zero_sections ℓ X p N a U b r
    have ht := eqToHom_apply_heq X (complex_term_zero ℓ X S) U
      (((ordinaryComplexIso ℓ X a (p a)).hom.f 0).val.app U
        (sectionTensor (p a) _ U b r))
    have hh := ht.symm.trans (heq_of_eq h)
    simpa [smul_eq_mul, mul_comm] using hh

-- Use the section formulas without unfolding the chosen inverse chain map.
attribute [local irreducible] scalarUnitIso ordinaryComplexIso

private theorem coefficientMap_locallySurjective (X : Scheme.{u})
    {A B : Type} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [DiscreteTopology B]
    [IsTopologicalRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (map X f continuous_of_discreteTopology)).hom := by
  let g := additiveMap.{u} f.toAddMonoidHom continuous_of_discreteTopology
  have : Epi g := by
    apply (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).epi_of_epi_map
    rw [NatTrans.epi_iff_epi_app]
    intro U
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    let y : C(U.unop, A) :=
      (⟨Function.surjInv hf, continuous_of_discreteTopology⟩ : C(B, A)).comp x.down
    refine ⟨ULift.up y, ?_⟩
    apply ULift.ext
    ext t
    exact Function.surjInv_eq hf (x.down t)
  have := upperStarLeftAdjoint X
  have : Epi ((upperStarFromPoint X).map g) := inferInstance
  have h := (Sheaf.isLocallySurjective_iff_epi' (J := Scheme.ProEt.topology X) Ab.{u + 1}
    ((upperStarFromPoint X).map g)).2
    inferInstance
  have h' := (Presheaf.isLocallySurjective_iff_whisker_forget
    (Scheme.ProEt.topology X) (((upperStarFromPoint X).map g).hom)).1 h
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact h'

private def restrictionFullyFaithful (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    [Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a).hom] :
    (restriction.{u + 1, u, u + 1} a).FullyFaithful := by
  let f := ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a).hom
  refine ⟨(fun {M N} g ↦
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective f N.isSheaf).symm
      g.val⟩), ?_, ?_⟩
  · intro M N g
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      f N.isSheaf).apply_symm_apply g.val
  · intro M N g
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      f N.isSheaf).symm_apply_apply g.val

private def tensorActionIso (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p) (n : ℕ) :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} (step ℓ X n)
      ((complex ℓ X (finiteRing ℓ X (n + 1))).homology (-1)) ≅ k ℓ X n := by
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (step ℓ X n)).hom :=
    coefficientMap_locallySurjective X
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1))))
      (ZMod.ringHom_surjective _)
  have := (restrictionFullyFaithful X (step ℓ X n)).full
  have := (restrictionFullyFaithful X (step ℓ X n)).faithful
  exact (eqToIso ((p (step ℓ X n)).obj_eq _)).symm ≪≫
    (p (step ℓ X n)).ordinary.mapIso
      (minusIso ℓ X (n + 1) ≪≫ residueIdentityIso ℓ X n) ≪≫
      asIso ((N.ordinaryAdjunction (step ℓ X n)).counit.app (k ℓ X n))

private theorem tensorActionIso_sections (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p) (n : ℕ) (U : X.ProEtᵒᵖ)
    (b : (finiteRing ℓ X n).obj.obj U)
    (x : ((complex ℓ X (finiteRing ℓ X (n + 1))).homology (-1)).val.obj U) :
    (tensorActionIso ℓ X p N n).hom.val.app U
      (pure (step ℓ X n) _ U b x) =
      sectionSMul X _ (k ℓ X n) U b
        ((residueIdentity ℓ X n).val.app U ((minusIso ℓ X (n + 1)).hom.val.app U x)) := by
  let a := step ℓ X n
  let g := (minusIso ℓ X (n + 1)).hom ≫ (residueIdentity ℓ X n)
  have h : (p a).ordinary.map g ≫ (N.ordinaryAdjunction a).counit.app (k ℓ X n) =
      ((N.ordinaryAdjunction a).homEquiv _ _).symm g := by
    exact ((N.ordinaryAdjunction a).homEquiv_counit _ _ g).symm
  have hx := ordinaryMate_sections X p N a _ (k ℓ X n) g U b x
  rw [← h] at hx
  change ((eqToHom ((p a).obj_eq _).symm ≫ (p a).ordinary.map g ≫
    (N.ordinaryAdjunction a).counit.app (k ℓ X n)).val.app U)
      (pure a _ U b x) = _
  simpa only [Functor.id_obj, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, sectionTensor, sectionSMul_eq_smul, g] using hx

private theorem ordinaryTensor_ext (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (p : Presentation.{u + 1, u, u + 1, w} a)
    (M : Modules.{u + 1, u, u + 1} R) (L : Modules.{u + 1, u, u + 1} S)
    (f g : p.ordinary.obj M ⟶ L)
    (h : ∀ (U : X.ProEtᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (sectionTensor p M U b x) =
        g.val.app U (sectionTensor p M U b x)) : f = g := by
  let j := eqToHom (p.obj_eq M).symm
  apply (cancel_epi j).mp
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _ L.isSheaf
  ext U z
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (a.hom.app U).hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul b x => exact h U b x

private def ordinaryChain (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S T : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ) :
    ((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((restriction.{u + 1, u, u + 1} b).mapHomologicalComplex (.up ℤ)).obj
        (((p a').ordinary.mapHomologicalComplex (.up ℤ)).obj P) :=
  ((Functor.mapHomologicalComplexIdIso (Modules.{u + 1, u, u + 1} S)
    (.up ℤ)).inv.app _) ≫
  (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction b).unit (.up ℤ)).app _ ≫
    ((restriction b).mapHomologicalComplex (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (N.ordinary a b ≪≫ eqToIso (congrArg (fun f ↦ (p f).ordinary) h))
        (.up ℤ)).hom.app P)

private theorem ordinaryChain_sections (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S T : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ)
    (i : ℤ) (U : X.ProEtᵒᵖ) (s : S.obj.obj U) (x : (P.X i).val.obj U) :
    ((ordinaryChain X p N a b a' h P).f i).val.app U
      (sectionTensor (p a) (P.X i) U s x) =
      sectionTensor (p a') (P.X i) U ((b.hom.app U).hom s) x := by
  subst a'
  change ((N.ordinary a b).hom.app (P.X i)).val.app U
    (((N.ordinaryAdjunction b).unit.app ((p a).ordinary.obj (P.X i))).val.app U
      (sectionTensor (p a) (P.X i) U s x)) = _
  rw [N.ordinary_unit, N.ordinary_hom, mul_one]

private theorem mate_representative (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S T : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := R) (P.X i)) :
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    let E := (p a).ordinary.mapHomotopyCategory (.up ℤ)
    let δ := (Functor.mapHomotopyCategoryCompIso (N.ordinary a b) (.up ℤ)).hom.app H
    (N.adjunction b).homEquiv _ _ ((N.derived a b).hom.app (DerivedCategory.Qh.obj H)) ≫
      (N.right b).map ((p (a ≫ b)).counit.app H) ≫
      (N.right_factors b).hom.app (((p (a ≫ b)).ordinary.mapHomotopyCategory
        (.up ℤ)).obj H) =
      (p a).counit.app H ≫ DerivedCategory.Qh.map
        ((((N.ordinaryAdjunction b).mapHomotopyCategory (.up ℤ)).unit.app (E.obj H)) ≫
          ((restriction b).mapHomotopyCategory (.up ℤ)).map δ) := by
  dsimp only
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
  let E := (p a).ordinary.mapHomotopyCategory (.up ℤ)
  let δ := (Functor.mapHomotopyCategoryCompIso (N.ordinary a b) (.up ℤ)).hom.app H
  have hE := SheafOfModules.isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse X R) a (p a).ordinary (p a).obj_eq (p a).map_eq P hP hf
  have hu := N.adjunction_normalization b
    (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) hE.1 hE.2
  have hp := congrArg (N.right b).map (N.representative a b P hP hf)
  have hn := (N.adjunction b).unit.naturality ((p a).counit.app H)
  have hr := (N.right_factors b).hom.naturality δ
  simp only [Functor.map_comp] at hp
  simp only [Adjunction.homEquiv_unit, Category.assoc]
  rw [reassoc_of% hp]
  erw [← reassoc_of% hn]
  erw [hr]
  erw [reassoc_of% hu]
  rw [Functor.map_comp]
  rfl

private theorem map_three_comp {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    F.map f ≫ F.map g ≫ F.map h ≫ 𝟙 _ = F.map (f ≫ g ≫ h) := by
  simp only [Functor.map_comp, Category.comp_id]

private theorem mate_chain_representative (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S T : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (P : CochainComplex (Modules.{u + 1, u, u + 1} R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology X) (R := R) (P.X i)) :
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj P
    (N.adjunction b).homEquiv _ _ ((N.derived a b).hom.app (DerivedCategory.Qh.obj H) ≫
      eqToHom (congrArg (fun f ↦ (p f).derived.obj (DerivedCategory.Qh.obj H)) h)) ≫
      (N.right b).map ((p a').counit.app H) ≫
      (N.right_factors b).hom.app
        (((p a').ordinary.mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        (((restriction b).mapHomotopyCategory (.up ℤ)).map
          (((p a').ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P)) ≫
      DerivedCategory.Qh.map
        (((restriction b).mapHomotopyCategoryFactors (.up ℤ)).hom.app
          (((p a').ordinary.mapHomologicalComplex (.up ℤ)).obj P)) =
      (p a).counit.app H ≫ DerivedCategory.Qh.map
        (((p a).ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        (ordinaryChain X p N a b a' h P)) := by
  subst a'
  dsimp only
  simp only [eqToHom_refl, Category.comp_id]
  erw [reassoc_of% mate_representative X p N a b P hP hf]
  simp only [Category.assoc, ← DerivedCategory.Qh.map_comp]
  apply congrArg (fun k ↦ (p a).counit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ DerivedCategory.Qh.map k)
  dsimp only [ordinaryChain]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient (Modules.{u + 1, u, u + 1} S) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Modules.{u + 1, u, u + 1} S) (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (Modules.{u + 1, u, u + 1} S) (.up ℤ)).map _ ≫ 𝟙 _ =
    (HomotopyCategory.quotient (Modules.{u + 1, u, u + 1} S) (.up ℤ)).map _
  exact map_three_comp
    (HomotopyCategory.quotient (Modules.{u + 1, u, u + 1} S) (.up ℤ)) _ _ _

private def unitRestriction (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    unit X R ⟶ (restriction.{u + 1, u, u + 1} a).obj (unit X S) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (unit X R).val.obj U)
        (Y := ((restriction.{u + 1, u, u + 1} a).obj (unit X S)).val.obj U)
        { toFun := (a.hom.app U).hom
          map_add' := map_add _
          map_smul' := fun r m ↦ (a.hom.app U).hom.map_mul r m }
      naturality := fun {U V} f ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (a.hom.naturality f) x }

private def reductionChain (ℓ : ℕ) (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    complex ℓ X R ⟶
      ((restriction.{u + 1, u, u + 1} a).mapHomologicalComplex (.up ℤ)).obj
        (complex ℓ X S) := by
  let F := restriction.{u + 1, u, u + 1} a
  refine HomologicalComplex.mkHomFromDouble (by decide) (by decide)
    (unitRestriction X a ≫ F.map (termMinus ℓ X S).inv)
    (unitRestriction X a ≫ F.map (termZero ℓ X S).inv) ?_ ?_
  · change (unitRestriction X a ≫ F.map (termMinus ℓ X S).inv) ≫
      F.map ((complex ℓ X S).d (-1) 0) = _
    rw [Category.assoc, ← F.map_comp]
    have hd : (complex ℓ X S).d (-1) 0 =
        (termMinus ℓ X S).hom ≫ (ℓ • 𝟙 (unit X S)) ≫ (termZero ℓ X S).inv :=
      HomologicalComplex.double_d _ _ (by decide)
    rw [hd]
    simp only [Iso.inv_hom_id_assoc, Functor.map_nsmul,
      comp_nsmul, id_comp, nsmul_comp]
  · intro j hj
    have hj' : j ≠ 0 := by change 0 + 1 = j at hj; omega
    change (unitRestriction X a ≫ F.map (termZero ℓ X S).inv) ≫
      F.map ((complex ℓ X S).d 0 j) = 0
    have hd : (complex ℓ X S).d 0 j = 0 :=
      HomologicalComplex.double_d_eq_zero₁ _ _ _ _ hj'
    rw [hd, F.map_zero, comp_zero]

private theorem reductionChain_minus_normalization (ℓ : ℕ) (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (reductionChain ℓ X a).f (-1) ≫
      (restriction.{u + 1, u, u + 1} a).map (termMinus ℓ X S).hom =
      (termMinus ℓ X R).hom ≫ unitRestriction X a := by
  simp [reductionChain, termMinus, ← Functor.map_comp]

private theorem reductionChain_minus (ℓ : ℕ) (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEtᵒᵖ) (x : ((complex ℓ X R).X (-1)).val.obj U) :
    ((restriction.{u + 1, u, u + 1} a).map (termMinus ℓ X S).hom).val.app U
      (((reductionChain ℓ X a).f (-1)).val.app U x) =
      (a.hom.app U).hom ((termMinus ℓ X R).hom.val.app U x) := by
  have h : (reductionChain ℓ X a).f (-1) ≫
      (restriction.{u + 1, u, u + 1} a).map (termMinus ℓ X S).hom =
      (termMinus ℓ X R).hom ≫ unitRestriction X a :=
    reductionChain_minus_normalization ℓ X a
  have hx := congrArg (fun f ↦ f.val.app U x) h
  change ((restriction.{u + 1, u, u + 1} a).map
    (termMinus ℓ X S).hom).val.app U
      (((reductionChain ℓ X a).f (-1)).val.app U x) =
    (a.hom.app U).hom ((termMinus ℓ X R).hom.val.app U x) at hx
  exact hx

private theorem reductionChain_zero_normalization (ℓ : ℕ) (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (reductionChain ℓ X a).f 0 ≫
      (restriction.{u + 1, u, u + 1} a).map (termZero ℓ X S).hom =
      (termZero ℓ X R).hom ≫ unitRestriction X a := by
  simp [reductionChain, termZero, ← Functor.map_comp]

private theorem reductionChain_zero (ℓ : ℕ) (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (U : X.ProEtᵒᵖ) (x : ((complex ℓ X R).X 0).val.obj U) :
    ((restriction.{u + 1, u, u + 1} a).map (termZero ℓ X S).hom).val.app U
      (((reductionChain ℓ X a).f 0).val.app U x) =
      (a.hom.app U).hom ((termZero ℓ X R).hom.val.app U x) := by
  have h : (reductionChain ℓ X a).f 0 ≫
      (restriction.{u + 1, u, u + 1} a).map (termZero ℓ X S).hom =
      (termZero ℓ X R).hom ≫ unitRestriction X a :=
    reductionChain_zero_normalization ℓ X a
  have hx := congrArg (fun f ↦ f.val.app U x) h
  change ((restriction.{u + 1, u, u + 1} a).map
    (termZero ℓ X S).hom).val.app U
      (((reductionChain ℓ X a).f 0).val.app U x) =
    (a.hom.app U).hom ((termZero ℓ X R).hom.val.app U x) at hx
  exact hx

attribute [local irreducible] reductionChain

private theorem ordinaryChain_comparison (ℓ : ℕ) (X : Scheme.{u})
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
    (N : Normalization.{u + 1, u, u + 1, w} p)
    {R S T : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a') :
    ordinaryChain X p N a b a' h (complex ℓ X R) ≫
      ((restriction.{u + 1, u, u + 1} b).mapHomologicalComplex (.up ℤ)).map
        (ordinaryComplexIso ℓ X a' (p a')).hom =
      (ordinaryComplexIso ℓ X a (p a)).hom ≫ reductionChain ℓ X b := by
  ext i : 1
  by_cases hi : i = -1
  · subst i
    apply (cancel_mono ((restriction b).map (termMinus ℓ X T).hom)).mp
    apply ordinaryTensor_ext X a (p a)
    intro U s x
    change (termMinus ℓ X T).hom.val.app U
      (((ordinaryComplexIso ℓ X a' (p a')).hom.f (-1)).val.app U
        (((ordinaryChain X p N a b a' h (complex ℓ X R)).f (-1)).val.app U
          (sectionTensor (p a) _ U s x))) = _
    rw [ordinaryChain_sections, ordinaryComplexIso_minus_sections ℓ X p N]
    change _ = ((restriction b).map (termMinus ℓ X T).hom).val.app U
      (((reductionChain ℓ X b).f (-1)).val.app U
        (((ordinaryComplexIso ℓ X a (p a)).hom.f (-1)).val.app U
          (sectionTensor (p a) _ U s x)))
    rw [reductionChain_minus, ordinaryComplexIso_minus_sections ℓ X p N, map_mul]
    have ht := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) h) U)
        ((termMinus ℓ X R).hom.val.app U x)
    exact congrArg (· * (b.hom.app U).hom s) ht.symm
  by_cases hi : i = 0
  · subst i
    apply (cancel_mono ((restriction b).map (termZero ℓ X T).hom)).mp
    apply ordinaryTensor_ext X a (p a)
    intro U s x
    change (termZero ℓ X T).hom.val.app U
      (((ordinaryComplexIso ℓ X a' (p a')).hom.f 0).val.app U
        (((ordinaryChain X p N a b a' h (complex ℓ X R)).f 0).val.app U
          (sectionTensor (p a) _ U s x))) = _
    rw [ordinaryChain_sections, ordinaryComplexIso_zero_sections ℓ X p N]
    change _ = ((restriction b).map (termZero ℓ X T).hom).val.app U
      (((reductionChain ℓ X b).f 0).val.app U
        (((ordinaryComplexIso ℓ X a (p a)).hom.f 0).val.app U
          (sectionTensor (p a) _ U s x)))
    rw [reductionChain_zero, ordinaryComplexIso_zero_sections ℓ X p N, map_mul]
    have ht := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) h) U)
        ((termZero ℓ X R).hom.val.app U x)
    exact congrArg (· * (b.hom.app U).hom s) ht.symm
  exact ((p a).ordinary.map_isZero
    (HomologicalComplex.isZero_double_X _ _ _ (by omega) hi)).eq_of_src _ _

private theorem inclusion_step_zero (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    sheafInclusion ℓ X (n + 1) ≫ unitRestriction X (step ℓ X n) = 0 := by
  apply (SheafOfModules.toSheaf _).map_injective
  have hi : (SheafOfModules.toSheaf _).map (sheafInclusion ℓ X (n + 1)) =
      (upperStarFromPoint X).map
        (additiveMap (kernelCoefficient ℓ (n + 1)) continuous_of_discreteTopology) :=
    eq_of_heq (sheafInclusion_underlying ℓ X (n + 1))
  rw [Functor.map_comp, Functor.map_zero, hi]
  change (upperStarFromPoint X).map
    (additiveMap (kernelCoefficient ℓ (n + 1)) continuous_of_discreteTopology) ≫
    (upperStarFromPoint X).map
      (additiveMap
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
          (ZMod (ℓ ^ (n + 1)))).toAddMonoidHom continuous_of_discreteTopology) = 0
  rw [← Functor.map_comp]
  suffices additiveMap.{u} (kernelCoefficient ℓ (n + 1)) continuous_of_discreteTopology ≫
      additiveMap
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
          (ZMod (ℓ ^ (n + 1)))).toAddMonoidHom continuous_of_discreteTopology = 0 by
    rw [this, Functor.map_zero]
  apply Sheaf.hom_ext
  ext U x
  apply ULift.ext
  ext t
  exact kernelCoefficient_step ℓ n (x.down t)

private theorem reduction_step (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    unitRestriction X (step ℓ X n) ≫
      (restriction.{u + 1, u, u + 1} (step ℓ X n)).map (sheafReduction ℓ X n) =
      sheafReduction ℓ X (n + 1) ≫ residueIdentity ℓ X n := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (sheafReduction ℓ X n).val.app U
      ((unitRestriction X (step ℓ X n)).val.app U x) =
    (residueIdentity ℓ X n).val.app U ((sheafReduction ℓ X (n + 1)).val.app U x)
  rw [sheafReduction_sections, sheafReduction_sections]
  change (residue ℓ X n).hom.app U ((step ℓ X n).hom.app U x) =
    (residue ℓ X (n + 1)).hom.app U x
  exact ConcreteCategory.congr_hom (congr_app
    (congrArg (fun f ↦ f.hom) (step_residue ℓ X n)) U) x

-- The remaining arguments use coefficient rings through the established map APIs.
attribute [local irreducible] ring finiteRing

private theorem homology_minus_transition (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap (reductionChain ℓ X (step ℓ X n)) (-1) ≫
      (restrictHomology X (step ℓ X n) (complex ℓ X (finiteRing ℓ X n)) (-1)).hom ≫
        (restriction.{u + 1, u, u + 1} (step ℓ X n)).map (minusIso ℓ X n).hom = 0 := by
  let F := restriction.{u + 1, u, u + 1} (step ℓ X n)
  let P := complex ℓ X (finiteRing ℓ X (n + 1))
  let Q := complex ℓ X (finiteRing ℓ X n)
  let f := reductionChain ℓ X (step ℓ X n)
  have := sheafInclusion_mono ℓ X n
  apply (cancel_mono (F.map (sheafInclusion ℓ X n))).mp
  apply (cancel_epi (P.homologyπ (-1))).mp
  simp only [Category.assoc, comp_zero, zero_comp]
  erw [reassoc_of% homologyMap_restrict_π X (step ℓ X n) P Q f (-1)]
  have hn := congrArg F.map (minusIso_normalization ℓ X n)
  simp only [Functor.map_comp] at hn
  rw [hn]
  erw [reassoc_of% homologyMap_restrict_cycles X (step ℓ X n) P Q f (-1)]
  have hc : f.f (-1) ≫ F.map (termMinus ℓ X (finiteRing ℓ X n)).hom =
      (termMinus ℓ X (finiteRing ℓ X (n + 1))).hom ≫
        unitRestriction X (step ℓ X n) :=
    reductionChain_minus_normalization ℓ X (step ℓ X n)
  rw [hc, ← reassoc_of% minusIso_normalization ℓ X (n + 1)]
  simp only [inclusion_step_zero, comp_zero]

private theorem homology_zero_transition (ℓ : ℕ) (X : Scheme.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap (reductionChain ℓ X (step ℓ X n)) 0 ≫
      (restrictHomology X (step ℓ X n) (complex ℓ X (finiteRing ℓ X n)) 0).hom ≫
        (restriction.{u + 1, u, u + 1} (step ℓ X n)).map (zeroIso ℓ X n).hom =
      (zeroIso ℓ X (n + 1)).hom ≫ residueIdentity ℓ X n := by
  let F := restriction.{u + 1, u, u + 1} (step ℓ X n)
  let P := complex ℓ X (finiteRing ℓ X (n + 1))
  let Q := complex ℓ X (finiteRing ℓ X n)
  let f := reductionChain ℓ X (step ℓ X n)
  apply (cancel_epi (P.homologyπ 0)).mp
  erw [reassoc_of% homologyMap_restrict_π X (step ℓ X n) P Q f 0]
  have hn := congrArg F.map (zeroIso_normalization ℓ X n)
  simp only [Functor.map_comp] at hn
  rw [hn]
  erw [reassoc_of% homologyMap_restrict_cycles X (step ℓ X n) P Q f 0]
  have hc : f.f 0 ≫ F.map (termZero ℓ X (finiteRing ℓ X n)).hom =
      (termZero ℓ X (finiteRing ℓ X (n + 1))).hom ≫
        unitRestriction X (step ℓ X n) :=
    reductionChain_zero_normalization ℓ X (step ℓ X n)
  rw [reassoc_of% hc]
  rw [reduction_step, ← reassoc_of% zeroIso_normalization]

private theorem zero_sections (X : Scheme.{u})
    {R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    {M L : Modules.{u + 1, u, u + 1} R} (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (0 : M ⟶ L).val.app U x = 0 := by
  have h := (SheafOfModules.forget _).map_zero M L
  change (0 : M ⟶ L).val = 0 at h
  rw [h]
  rfl

section Assembly

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
  [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
    HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
  (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
  (N : Normalization.{u + 1, u, u + 1, w} p)

private def realizationData : Realization ℓ X p N where
  compatible := projection_step ℓ X
  ordinary n := ordinaryComplexIso ℓ X (projection ℓ X n) (p _)
  model n := derivedComplexIso ℓ X p N (projection ℓ X n)
  chain n := reductionChain ℓ X (step ℓ X n)

private def cohomologyData : Cohomology ℓ X p N (realizationData ℓ X p N) where
  minus := minusIso ℓ X
  zero := zeroIso ℓ X
  derivedMinus n :=
    (DerivedCategory.homologyFunctor
      (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) (-1)).mapIso
        ((realizationData ℓ X p N).model n) ≪≫
      localizedHomology X _ (complex ℓ X (finiteRing ℓ X n)) (-1) ≪≫ minusIso ℓ X n
  derivedZero n :=
    (DerivedCategory.homologyFunctor
      (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) 0).mapIso
        ((realizationData ℓ X p N).model n) ≪≫
      localizedHomology X _ (complex ℓ X (finiteRing ℓ X n)) 0 ≪≫ zeroIso ℓ X n
  kernelCoefficient := kernelCoefficient ℓ
  inclusion := sheafInclusion ℓ X
  reduction := sheafReduction ℓ X
  residueIdentity := residueIdentity ℓ X

private def tensorData : TensorCalculation ℓ X p N (realizationData ℓ X p N)
    (cohomologyData ℓ X p N) where
  action := tensorActionIso ℓ X p N
  induced _ := 0

private theorem realizationData_spec :
    IsRealization ℓ X p N (realizationData ℓ X p N) := by
  refine ⟨kflat_complex ℓ X _, ?_, ?_,
    (fun n ↦ reductionChain_minus ℓ X (step ℓ X n)),
    (fun n ↦ reductionChain_zero ℓ X (step ℓ X n)), ?_⟩
  · exact fun n i hi U b r ↦
      ordinaryComplexIso_sections ℓ X p N (projection ℓ X n) i hi U b r
  · intro n
    rfl
  · intro n
    let a := projection ℓ X (n + 1)
    let b := step ℓ X n
    let a' := projection ℓ X n
    let P := complex ℓ X (ring X ℤ_[ℓ])
    let Q' := HomotopyCategory.quotient
      (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) (.up ℤ)
    let e' := ordinaryComplexIso ℓ X a' (p a')
    have hc := ordinaryChain_comparison ℓ X p N a b a' (projection_step ℓ X n)
    have hm := mate_chain_representative X p N a b a' (projection_step ℓ X n)
      P (kflat_complex ℓ X _) (flat_terms ℓ X _)
    dsimp only [realizationData, derivedComplexIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, asIso_hom, transition, localized, Functor.comp_obj]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% (N.right_factors b).hom.naturality (Q'.map e'.hom)]
    erw [reassoc_of% (N.right_factors b).hom.naturality
      (((p a').ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P)]
    have ht := congrArg DerivedCategory.Qh.map
      (((restriction b).mapHomotopyCategoryFactors (.up ℤ)).hom.naturality e'.hom)
    simp only [Functor.comp_map, Functor.map_comp] at ht
    erw [ht]
    erw [reassoc_of% hm]
    simp only [← Functor.map_comp]
    rw [hc]

private theorem cohomologyData_spec (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (hX : X = Spec (.of Ω)) :
    IsCohomology ℓ X p N (realizationData ℓ X p N) (cohomologyData ℓ X p N) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n q h₀ h₁ ↦ homology_other ℓ X _ q h₀ h₁
  · intro n
    rfl
  · intro n
    rfl
  · intro n q h₀ h₁
    exact (homology_other ℓ X _ q h₀ h₁).of_iso
      ((DerivedCategory.homologyFunctor
        (Modules.{u + 1, u, u + 1} (finiteRing ℓ X n)) q).mapIso
          ((realizationData ℓ X p N).model n) ≪≫
        localizedHomology X _ (complex ℓ X (finiteRing ℓ X n)) q)
  · exact kernelCoefficient_int ℓ
  · exact sheafInclusion_underlying ℓ X
  · exact minusIso_normalization ℓ X
  · exact sheafReduction_sections ℓ X
  · exact zeroIso_normalization ℓ X
  · exact residueIdentity_underlying ℓ X
  · exact homology_minus_transition ℓ X
  · exact homology_zero_transition ℓ X
  · subst X
    exact residue_nonzero ℓ Ω
  · exact ⟨constantResidueIso ℓ X⟩

private theorem tensorData_spec :
    IsTensorCalculation ℓ X p N (realizationData ℓ X p N)
      (cohomologyData ℓ X p N) (tensorData ℓ X p N) := by
  refine ⟨tensorActionIso_sections ℓ X p N, ?_, fun _ ↦ rfl⟩
  intro n U b x
  have hz := homology_minus_transition ℓ X n
  let F := restriction.{u + 1, u, u + 1} (step ℓ X n)
  have hzero : HomologicalComplex.homologyMap
      (reductionChain ℓ X (step ℓ X n)) (-1) ≫
        (restrictHomology X (step ℓ X n) (complex ℓ X (finiteRing ℓ X n)) (-1)).hom = 0 := by
    apply (cancel_mono (F.map (minusIso ℓ X n).hom)).mp
    simpa only [zero_comp, Category.assoc] using hz
  change (0 : SheafOfModules.changeOfRings.{u, u + 1, u + 1} (step ℓ X n)
    ((complex ℓ X (finiteRing ℓ X (n + 1))).homology (-1)) ⟶
      (complex ℓ X (finiteRing ℓ X n)).homology (-1)).val.app U
        (pure (step ℓ X n) _ U b x) = _
  dsimp only [realizationData]
  erw [hzero]
  simp only [id_eq, zero_sections, sectionSMul_eq_smul, smul_zero]

end Assembly

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
  exact ⟨{
    realization := realizationData ℓ (Spec (.of Ω)) p N
    cohomology := cohomologyData ℓ (Spec (.of Ω)) p N
    tensor := tensorData ℓ (Spec (.of Ω)) p N
    realization_spec := realizationData_spec ℓ (Spec (.of Ω)) p N
    cohomology_spec := cohomologyData_spec ℓ (Spec (.of Ω)) p N Ω rfl
    tensor_spec := tensorData_spec ℓ (Spec (.of Ω)) p N
  }⟩

end AlgebraicGeometry.ProEtale.TwoTermReduction
