/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Adic coefficient datum and reduction tower

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/def-weil-pbc-complete-coefficient-datum.md, order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum).

The construction uses one K-flat model with flat terms. Quotient reductions are actual
changed complexes. The ordinary balancing and transition maps are specified uniquely on
local tensor generators; their images under localization are the canonical derived maps.

## Main definitions

- `CompleteCoefficientDatum`: the ring, ideal, torsion, and perfectness conditions.
- `AdicKFlatModel`: one flat-term K-flat representative of an arbitrary derived object.
- `adicReduction`, `adicReductionUnderlying`: the quotient reduction and its scalar restriction.
- `adicTransition`: the localized map induced by the quotient homomorphism.
- `adicNormalization`: the localized scalar-extension balancing isomorphism.

## Main statements

- `adicKFlatModel_exists`: availability of models for every unbounded derived object.
- `adicTransition_id`, `adicTransition_comp`: the transition identities.
- `adicNormalization_cocycle`, `adicNormalization_unit`: normalization coherence.
- `adicReductionUnderlying_tensor`: comparison with the recorded derived tensor product.
-/

@[expose] public section

universe t

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The constant commutative ring sheaf, before forgetting commutativity.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicConstantRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))

/-- The underlying constant ring sheaf used by the recorded pro-etale derived category.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicModuleRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (adicConstantRing X A)

/-- The functorial constant sheaf map associated to a coefficient homomorphism.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicConstantMap (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    adicConstantRing X A ⟶ adicConstantRing X B :=
  (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).map
    (CommRingCat.ofHom (RingHom.ulift φ))

/-- The same coefficient map, regarded as a map of ring sheaves.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicModuleMap (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    adicModuleRing X A ⟶ adicModuleRing X B :=
  (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (adicConstantMap X φ)

/-- Localization into the exact derived category recorded for the small pro-etale site.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicLocalization (X : Scheme.{t}) (A : Type t) [CommRing A] :
    CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ ⥤
      proEtaleDerivedCategory X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Perfectness of the actual quotient module over the original coefficient ring,
placed in degree zero. Source: blueprint order 1255
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicQuotientPerfect (Λ : Type t) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{t} Λ)
  DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{t} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I ^ n)))

/-- Precisely the coefficient hypotheses, without an assumption of I-adic completeness,
finiteness of the quotient sets, or flatness of any quotient.
Source: blueprint order 1255 (blueprint: def-weil-pbc-complete-coefficient-datum). -/
structure CompleteCoefficientDatum (Λ : Type t) [CommRing Λ] where
  ideal : Ideal Λ
  noetherian : IsNoetherianRing Λ
  finitelyGenerated : ideal.FG
  quotientTorsion : ∀ x : Λ ⧸ ideal, ∃ m : ℕ, 0 < m ∧ m • x = 0
  quotientPerfect : ∀ n : ℕ, 1 ≤ n → adicQuotientPerfect Λ ideal n

/-- One K-flat flat-term representative of the arbitrary derived object K. The realization
is part of the choice of model, rather than a restriction on K.
Source: blueprint order 1255, construction step 1; Stacks Tag 06YS
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
structure AdicKFlatModel (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (K : proEtaleDerivedCategory X Λ) where
  complex : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ
  isKFlat : CochainComplex.IsKFlat (R := adicConstantRing X Λ) complex
  flatTerms : ∀ p : ℤ, CategoryTheory.exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (adicConstantRing X Λ)) (complex.X p))
  realization :
    (adicLocalization X Λ).obj complex ≅ K

/-- Every derived object has a model of the stipulated kind; no boundedness or flatness
of the quotient coefficients is assumed. Source: blueprint order 1255, construction step 1;
Stacks Tag 06YS.
Proof: represent K by a cochain complex, take its K-flat resolution with flat terms
(lem-pc-kflat-resolution), and compose the localization of the augmentation with the
representative isomorphism. The augmentation is a quasi-isomorphism, so its localization
is invertible. The small-site universe convention does not change this construction.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicKFlatModel_exists (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (K : proEtaleDerivedCategory X Λ) : Nonempty (AdicKFlatModel X Λ K) := by
  sorry

/-- The quotient map for two powers of the ideal, sending the class of x to the class of x.
Source: blueprint order 1255, construction step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicQuotientMap {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (b a : ℕ) (hab : a ≤ b) : Λ ⧸ I ^ b →+* Λ ⧸ I ^ a :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)

/-- Termwise scalar extension, with the target coefficient action retained.
Source: blueprint order 1255, steps 1 and 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicChange (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :=
  SheafOfModules.changeOfRingsComplex.{t + 1, t} (adicConstantMap X φ) P

/-- Termwise restriction of scalars, retaining the same abelian sheaves and differentials.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable abbrev adicRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :=
  ((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- The local pure tensor s tensor m, mapped into the sheafified scalar extension.
Source: blueprint order 1255, steps 2 and 3; Stacks Tag 03EK
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTensorSection (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (M : SheafOfModules.{t + 1} (adicModuleRing X A)) (U : X.ProEtᵒᵖ)
    (s : (adicConstantRing X B).obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRings.{t, t + 1, t + 1} (adicConstantMap X φ) M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (adicConstantMap X φ) M)).app U
        (s ⊗ₜ[(adicConstantRing X A).obj.obj U,
          ((adicConstantMap X φ).hom.app U).hom] m)

/-- The ordinary balancing map is uniquely specified on local tensor generators and is
invertible. Source: blueprint order 1255, step 3; Stacks Tags 03EK and 0D6D.
Proof: send s tensor (r tensor m) to (s * ψ(r)) tensor m. The balancing relations
make this well-defined; restriction maps commute with the formula. Sheafification gives
the sheaf morphism. Its inverse sends s tensor m to s tensor (1 tensor m).
The differential acts only on m, so these are chain maps. The two composites are
identities by the balancing relations. Local tensor generators prove uniqueness.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalance_exists (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    ∃! f : adicChange X ψ (adicChange X φ P) ⟶ adicChange X χ P,
      IsIso f ∧ ∀ (p : ℤ) (U : X.ProEtᵒᵖ)
        (s : (adicConstantRing X C).obj.obj U)
        (r : (adicConstantRing X B).obj.obj U) (m : (P.X p).val.obj U),
        (f.f p).val.app U
          (adicTensorSection X ψ _ U s (adicTensorSection X φ _ U r m)) =
          adicTensorSection X χ _ U (s * (adicConstantMap X ψ).hom.app U r) m := by
  sorry

/-- The uniquely characterized ordinary balancing chain map.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicBalanceHom (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X ψ (adicChange X φ P) ⟶ adicChange X χ P :=
  Classical.choose (adicBalance_exists X φ ψ χ h P)

/-- The chosen balancing map is invertible. Source: blueprint order 1255, step 3.
Proof: use the isomorphism clause of adicBalance_exists; its inverse is the formula
s tensor m maps to s tensor (1 tensor m).
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalanceHom_isIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    IsIso (adicBalanceHom X φ ψ χ h P) := by
  sorry

/-- Scalar-extension associativity, on the explicit complexes before localization.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicBalanceIso (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X ψ (adicChange X φ P) ≅ adicChange X χ P :=
  letI := adicBalanceHom_isIso X φ ψ χ h P
  asIso (adicBalanceHom X φ ψ χ h P)

/-- Compatibility of the quotient maps with the coefficient map from Λ.
Source: blueprint order 1255, step 2.
Proof: both composites send the class of x to its class modulo I^a; quotient induction
reduces the equality to the formula for Ideal.Quotient.factor.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_comp_mk {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (b a : ℕ) (hab : a ≤ b) :
    (adicQuotientMap I b a hab).comp (Ideal.Quotient.mk (I ^ b)) =
      Ideal.Quotient.mk (I ^ a) := by
  sorry

/-- The quotient-coefficient reduction, computed by the fixed K-flat model.
Source: blueprint order 1255, step 1; Stacks Tag 06YY
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReduction (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n : ℕ)) :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (n : ℕ))).obj (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n
    : ℕ))) M.complex)

/-- The same reduction after termwise restriction of scalars to Λ.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReductionUnderlying (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) : proEtaleDerivedCategory X Λ :=
  (adicLocalization X Λ).obj
    (adicRestrict X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex))

/-- Each changed model remains K-flat, with flat terms over its quotient coefficients.
Source: blueprint order 1255, construction step 3; Stacks Tag 0G7E.
Proof: apply lem-pur-kflat-change-of-rings to the constant quotient sheaf homomorphism,
using the K-flat and flat-term fields of the chosen model. Thus a second scalar extension
of this very complex computes the derived scalar extension, by
lem-pur-derived-change-of-rings, without a flatness assumption on the quotient over Λ.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicReductionModel_isKFlat (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    CochainComplex.IsKFlat (R := adicConstantRing X (Λ ⧸ d.ideal ^ (n : ℕ)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex) ∧
      ∀ p : ℤ, CategoryTheory.exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (adicConstantRing X (Λ ⧸ d.ideal ^ (n : ℕ))))
          ((adicChange X (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex).X p)) := by
  sorry

/-- The source of normalization, computed over the intermediate quotient coefficient ring.
Source: blueprint order 1255, step 3; Stacks Tag 0G7E
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicReductionTwice (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (b a : ℕ+) (hab : a ≤ b) :
    proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (a : ℕ)) :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).obj
    (adicChange X (adicQuotientMap d.ideal b a hab)
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (b : ℕ))) M.complex))

/-- The normalization is precisely the localization of the ordinary balancing isomorphism.
Source: blueprint order 1255, step 3
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicNormalization (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (b a : ℕ+) (hab : a ≤ b) :
    adicReductionTwice X d M b a hab ≅ adicReduction X d M a :=
  (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).mapIso
    (adicBalanceIso X (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
      (adicQuotientMap d.ideal b a hab) (Ideal.Quotient.mk (d.ideal ^ (a : ℕ)))
      (adicQuotientMap_comp_mk d.ideal b a hab) M.complex)

/-- The transition chain map is uniquely specified by applying the quotient homomorphism
on the coefficient tensor factor. Source: blueprint order 1255, step 2; Stacks Tag 03EK.
Proof: the formula is balanced over Λ and commutes with restrictions. Extend it by the
universal property of module sheafification. It is Λ-linear after restriction of scalars
and commutes with the differential, which acts on the model factor. Tensor generators
locally generate the sheafifications in every degree, proving uniqueness.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransitionComplex_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) :
    ∃! f :
      adicRestrict X (Ideal.Quotient.mk (I ^ (b : ℕ)))
        (adicChange X (Ideal.Quotient.mk (I ^ (b : ℕ))) P) ⟶
      adicRestrict X (Ideal.Quotient.mk (I ^ (a : ℕ)))
        (adicChange X (Ideal.Quotient.mk (I ^ (a : ℕ))) P),
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ)
        (r : (adicConstantRing X (Λ ⧸ I ^ (b : ℕ))).obj.obj U)
        (m : (P.X p).val.obj U),
        (f.f p).val.app U (adicTensorSection X (Ideal.Quotient.mk (I ^ (b : ℕ)))
          _ U r m) =
        adicTensorSection X (Ideal.Quotient.mk (I ^ (a : ℕ))) _ U
          ((adicConstantMap X (adicQuotientMap I b a hab)).hom.app U r) m := by
  sorry

/-- Apply the quotient map on the scalar factor, with the original Λ-action retained.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTransitionComplex (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (b a : ℕ+) (hab : a ≤ b) :
    adicRestrict X (Ideal.Quotient.mk (I ^ (b : ℕ)))
      (adicChange X (Ideal.Quotient.mk (I ^ (b : ℕ))) P) ⟶
    adicRestrict X (Ideal.Quotient.mk (I ^ (a : ℕ)))
      (adicChange X (Ideal.Quotient.mk (I ^ (a : ℕ))) P) :=
  Classical.choose (adicTransitionComplex_exists X I P b a hab)

/-- The derived transition q_{b,a}, in the original coefficient category.
Source: blueprint order 1255, step 2
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicTransition (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (b a : ℕ+) (hab : a ≤ b) :
    adicReductionUnderlying X d M b ⟶ adicReductionUnderlying X d M a :=
  (adicLocalization X Λ).map (adicTransitionComplex X d.ideal M.complex b a hab)

/-- Equal-index transitions are identity maps. Source: blueprint order 1255, step 2.
Proof: the quotient homomorphism is identity, so the transition and identity have the
same tensor-generator formula. Uniqueness gives equality of chain maps and localization
preserves the identity.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransition_id (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (a : ℕ+) :
    adicTransition X d M a a (le_refl a) = 𝟙 (adicReductionUnderlying X d M a) := by
  sorry

/-- Transition maps compose in the stated order. Source: blueprint order 1255, step 2.
Proof: quotient homomorphisms compose. On every local tensor generator both chain-map
paths send r tensor m to q_{c,a}(r) tensor m. Uniqueness gives equality of chain maps;
the localization functor preserves composition.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransition_comp (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (c b a : ℕ+) (hab : a ≤ b) (hbc : b ≤ c) :
    adicTransition X d M c a (le_trans hab hbc) =
      adicTransition X d M c b hbc ≫ adicTransition X d M b a hab := by
  sorry

/-- Termwise extension of a chain map commutes with differentials.
Source: blueprint order 1255, steps 3 and 4; Stacks Tag 03EK.
Proof: extension of scalars preserves composition; apply it to the commutativity equation
for the original chain map, then sheafify. The resulting equality is exactly the displayed
chain-map condition.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicChangeHom_comm (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ}
    (f : P ⟶ Q) (i j : ℤ) :
    SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
        (adicConstantMap X φ) (P.X i) (f.f i) ≫ (adicChange X φ Q).d i j =
      (adicChange X φ P).d i j ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
          (adicConstantMap X φ) (P.X j) (f.f j) := by
  sorry

/-- Extension of a chain map on each term, using the recorded sheaf change-of-rings map.
Source: blueprint order 1255, steps 3 and 4
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicChangeHom (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ}
    (f : P ⟶ Q) : adicChange X φ P ⟶ adicChange X φ Q where
  f i := SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1}
    (adicConstantMap X φ) (P.X i) (f.f i)
  comm' i j _ := adicChangeHom_comm X φ f i j

/-- Ordinary balancing is natural in the complex being extended.
Source: blueprint order 1255, step 3; Stacks Tag 0D6D.
Proof: both composites send s tensor (r tensor m) to
(s * ψ(r)) tensor f(m). Linearity, restriction compatibility, and local tensor generation
give equality of the sheaf maps in every degree, hence equality of chain maps. Inverting
quasi-isomorphisms between K-flat models preserves this equality, proving compatibility
with the canonical resolution comparisons of lem-pur-derived-change-of-rings.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicBalanceHom_naturality (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ} (f : P ⟶ Q) :
    adicChangeHom X ψ (adicChangeHom X φ f) ≫ adicBalanceHom X φ ψ χ h Q =
      adicBalanceHom X φ ψ χ h P ≫ adicChangeHom X χ f := by
  sorry

/-- The transitions commute with comparison maps of the chosen complexes.
Source: blueprint order 1255, step 2.
Proof: both paths send r tensor m to q_{b,a}(r) tensor f(m), by the two defining
tensor formulas. Local tensor generation gives equality in every degree. After
localization, the equality persists under inversion of quasi-isomorphisms between K-flat
models; hence the canonical resolution comparisons preserve the transition tower.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicTransitionComplex_naturality (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (I : Ideal Λ)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ}
    (f : P ⟶ Q) (b a : ℕ+) (hab : a ≤ b) :
    ((SheafOfModules.restrictScalars.{t + 1}
        (adicModuleMap X (Ideal.Quotient.mk (I ^ (b : ℕ))))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (I ^ (b : ℕ))) f) ≫
      adicTransitionComplex X I Q b a hab =
    adicTransitionComplex X I P b a hab ≫
      ((SheafOfModules.restrictScalars.{t + 1}
        (adicModuleMap X (Ideal.Quotient.mk (I ^ (a : ℕ))))).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (I ^ (a : ℕ))) f) := by
  sorry

/-- The direct and composite quotient homomorphisms coincide.
Source: blueprint order 1255, steps 2 and 4.
Proof: quotient induction reduces both maps to the identical map on representatives.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_comp {Λ : Type t} [CommRing Λ] (I : Ideal Λ)
    (c b a : ℕ+) (hab : a ≤ b) (hbc : b ≤ c) :
    (adicQuotientMap I b a hab).comp (adicQuotientMap I c b hbc) =
      adicQuotientMap I c a (le_trans hab hbc) := by
  sorry

/-- The normalization cocycle, including the canonical associativity identification of
its source. The left path extends θ_{c,b} to P_a and then applies θ_{b,a}; the right
path first balances the last two extensions and then applies θ_{c,a}.
Source: blueprint order 1255, step 4; Stacks Tag 0D6D.
Proof: on local generators s tensor (r tensor (t tensor m)), both paths give
(s * q_{b,a}(r) * q_{c,a}(t)) tensor m. This uses composition and multiplicativity of the
quotient homomorphisms. Local tensor generation and sheafification give equality of chain
maps. Localization gives the displayed equality. K-flatness of successive extensions is
lem-pur-kflat-change-of-rings, so these models compute the successive derived extensions.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicNormalization_cocycle (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (c b a : ℕ+) (hab : a ≤ b) (hbc : b ≤ c) :
    (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map
      (adicChangeHom X (adicQuotientMap d.ideal b a hab)
        (adicBalanceHom X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ)))
          (adicQuotientMap d.ideal c b hbc) (Ideal.Quotient.mk (d.ideal ^ (b : ℕ)))
          (adicQuotientMap_comp_mk d.ideal c b hbc) M.complex)) ≫
      (adicNormalization X d M b a hab).hom =
    (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map
      (adicBalanceHom X (adicQuotientMap d.ideal c b hbc)
        (adicQuotientMap d.ideal b a hab) (adicQuotientMap d.ideal c a (le_trans hab hbc))
        (adicQuotientMap_comp d.ideal c b a hab hbc)
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (c : ℕ))) M.complex)) ≫
      (adicNormalization X d M c a (le_trans hab hbc)).hom := by
  sorry

/-- Extension along the identity coefficient map has its uniquely specified unit map.
Source: blueprint order 1255, step 4; Stacks Tag 03EK.
Proof: send s tensor m to s times m. Balancing makes the map well-defined, and the
inverse sends m to 1 tensor m. Restrictions and differentials commute with the formula.
Local tensor generators prove uniqueness; balancing proves the two inverse identities.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicUnit_exists (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    ∃! f : adicChange X φ P ⟶ P, IsIso f ∧
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ) (s : (adicConstantRing X A).obj.obj U)
        (m : (P.X p).val.obj U),
        (f.f p).val.app U (adicTensorSection X φ _ U s m) = s • m := by
  sorry

/-- The ordinary unit map, with its canonical tensor-generator formula.
Source: blueprint order 1255, step 4
(blueprint: def-weil-pbc-complete-coefficient-datum). -/
noncomputable def adicUnitHom (X : Scheme.{t}) {A : Type t} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ) :
    adicChange X φ P ⟶ P :=
  Classical.choose (adicUnit_exists X φ hφ P)

/-- The equal-index quotient homomorphism is identity.
Source: blueprint order 1255, steps 2 and 4.
Proof: its defining quotient factor sends each class to itself, so quotient induction
proves equality to the identity homomorphism.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicQuotientMap_id {Λ : Type t} [CommRing Λ] (I : Ideal Λ) (a : ℕ+) :
    adicQuotientMap I a a (le_refl a) = RingHom.id (Λ ⧸ I ^ (a : ℕ)) := by
  sorry

/-- Equal-index normalization is the unit identification, rather than an arbitrary
isomorphism between its source and target. Source: blueprint order 1255, step 4.
Proof: on s tensor (r tensor m), balancing gives (s*r) tensor m. This is precisely
the action of the unit map on the changed complex. The unique tensor-generator
characterizations identify the chain maps, and then their localizations.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicNormalization_unit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (a : ℕ+) :
    (adicNormalization X d M a a (le_refl a)).hom =
      (adicLocalization X (Λ ⧸ d.ideal ^ (a : ℕ))).map
        (adicUnitHom X (adicQuotientMap d.ideal a a (le_refl a))
          (adicQuotientMap_id d.ideal a)
          (adicChange X (Ideal.Quotient.mk (d.ideal ^ (a : ℕ))) M.complex)) := by
  sorry

/-- Restricting the quotient reduction is the recorded derived tensor product with the
constant quotient ring. Source: blueprint order 1255, statement and step 1.
Proof: the fixed K-flat model computes both sides (lem-pur-derived-change-of-rings).
Termwise scalar extension restricted to Λ is tensor with the quotient ring sheaf.
Tensoring with its degree-zero complex has just one nonzero summand in each total degree;
the ordinary scalar-extension tensor formula identifies this summand and its differential.
These identifications commute with restrictions and pass to localization.
(blueprint: def-weil-pbc-complete-coefficient-datum) -/
theorem adicReductionUnderlying_tensor (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ+) :
    Nonempty (adicReductionUnderlying X d M n ≅
      derivedTensorRing X Λ (Λ ⧸ d.ideal ^ (n : ℕ))
        (Ideal.Quotient.mk (d.ideal ^ (n : ℕ))) M.complex M.complex
        (𝟙 M.complex) (inferInstance : QuasiIso (𝟙 M.complex)) M.isKFlat) := by
  sorry

end AlgebraicGeometry.Scheme
