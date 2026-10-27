/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.DerivedTensorShiftDescent
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Monoidal.Category
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Ordered tensor composition on shifted regular units

Source: current blueprint, six-functors-basics, direct-images proof, paragraph (3),
agent-formulated internal bar normalization; signed conventions: Stacks Tag 0FNH.
(blueprint: lem-sfb-shifted-unit-tensor-composition).

The helper definitions spell out the maps in this node, using the canonical native
K-flat tensor and its signed shift comparisons. No representatives of the input
arrows are chosen. The coefficient sign is quantified before the site and the ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe d h c v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.ShiftedRegularUnit

section Maps
variable {D : Type d} [Category.{h} D] [Preadditive D] [MonoidalCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [(curriedTensor D).CommShift₂Int] (I : D) (e : 𝟙_ D ≅ I)

/-- The left unitor after identifying the regular unit with the tensor unit.
Source: internal bar normalization, paragraph (3)
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def leftUnit (Z : D) : I ⊗ Z ≅ Z :=
  tensorIso e.symm (Iso.refl Z) ≪≫ λ_ Z

/-- The right unitor with the same regular-unit identification.
Source: internal bar normalization, paragraph (3)
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def rightUnit (Z : D) : Z ⊗ I ≅ Z :=
  tensorIso (Iso.refl Z) e.symm ≪≫ ρ_ Z

/-- Extraction of the second shift followed by the shifted right unitor.
Source: internal bar normalization, paragraph (3), Stacks 0FNH
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def kappa (Z : D) (q : ℤ) : Z ⊗ I⟦-q⟧ ≅ Z⟦-q⟧ :=
  (((curriedTensor D).obj Z).commShiftIso (-q)).app I ≪≫
    (shiftFunctor D (-q)).mapIso (rightUnit I e Z)

/-- Ordinary addition of the two shifts, with no tensor-extraction sign.
Source: internal bar normalization, paragraph (3)
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def can (p q : ℤ) : I⟦-(p + q)⟧ ≅ (I⟦-p⟧)⟦-q⟧ :=
  (shiftFunctorAdd' D (-p) (-q) (-(p + q)) (by omega)).app I

/-- Inverse of first extraction, then second extraction, then shifted multiplication.
Source: internal bar normalization, paragraph (3), Stacks 0FNH
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def split (p q : ℤ) : I⟦-(p + q)⟧ ≅ I⟦-p⟧ ⊗ I⟦-q⟧ :=
  ((((curriedTensor D).flip.obj (I⟦-q⟧)).commShiftIso (-p)).app I ≪≫
    (shiftFunctor D (-p)).mapIso
      ((((curriedTensor D).obj I).commShiftIso (-q)).app I) ≪≫
    ((shiftFunctorAdd' D (-q) (-p) (-(p + q)) (by omega)).app (I ⊗ I)).symm ≪≫
    (shiftFunctor D (-(p + q))).mapIso (leftUnit I e I)).symm

/-- The naturality, unitor, ordered-composition and sign clauses for the displayed maps.
This is a predicate spelling out this node, not an additional categorical structure.
Source: internal bar normalization, paragraph (3)
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def Identities (t : ℤ × ℤ → ℤˣ) : Prop :=
  (∀ (Z Z' : D) (a : Z ⟶ Z') (q : ℤ),
    (a ▷ I⟦-q⟧) ≫ (kappa I e Z' q).hom =
      (kappa I e Z q).hom ≫ a⟦-q⟧') ∧
  (∀ q : ℤ, (kappa I e I q).hom = (leftUnit I e (I⟦-q⟧)).hom) ∧
  (∀ (p q : ℤ) (f : I⟦-p⟧ ⟶ I) (g : I⟦-q⟧ ⟶ I),
    ((f ⊗ₘ g) ≫ (leftUnit I e I).hom =
      (f ▷ I⟦-q⟧) ≫ (leftUnit I e (I⟦-q⟧)).hom ≫ g) ∧
    ((f ▷ I⟦-q⟧) ≫ (leftUnit I e (I⟦-q⟧)).hom ≫ g =
      (f ▷ I⟦-q⟧) ≫ (kappa I e I q).hom ≫ g) ∧
    ((f ▷ I⟦-q⟧) ≫ (kappa I e I q).hom ≫ g =
      (kappa I e (I⟦-p⟧) q).hom ≫ f⟦-q⟧' ≫ g)) ∧
  (∀ p q : ℤ,
    (split I e p q).hom ≫ (kappa I e (I⟦-p⟧) q).hom =
      (t (p, q) : ℤ) • (can I p q).hom) ∧
  (∀ (p q : ℤ) (f : I⟦-p⟧ ⟶ I) (g : I⟦-q⟧ ⟶ I),
    (split I e p q).hom ≫ (f ⊗ₘ g) ≫ (leftUnit I e I).hom =
      (t (p, q) : ℤ) • ((can I p q).hom ≫ f⟦-q⟧' ≫ g))

end Maps

/-- Specialize the displayed maps to the canonical tensor on ordinary module sheaves.
All local instance values below are existing constructions, not chosen tensor data.
The regular object is literally the localization of the coefficient complex in degree zero.
Source: internal bar normalization, paragraph (3), and Stacks 0FNH, 06YS, 0FPT
(blueprint: lem-sfb-shifted-unit-tensor-composition). -/
def RingedIdentities {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (R : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]
    (t : ℤ × ℤ → ℤˣ) : Prop :=
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesSymmetric R
  letI := SheafOfModules.cochainModulesPreadditive R
  letI := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  letI := SheafOfModules.hasFunctorialFlatResolution_kfi R
  letI : HasColimitsOfSize.{0, 0} (RingedTensorModules.{c, v, u} J R) :=
    hasColimitsOfSizeShrink.{0, 0, max c v u, max c v u} _
  letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
  letI := DerivedCategory.commShift₂CurriedTensor (C := RingedTensorModules.{c, v, u} J R)
  Identities (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
    (RingedDerivedNative.unitIso.{c, v, u, w} J R) t

/-- Ordered tensor composition and its uniform integer sign on shifted regular units.
Source: current blueprint, direct-images proof, paragraph (3), agent-formulated internal
bar normalization; Stacks Tag 0FNH fixes the extraction conventions.
(blueprint: lem-sfb-shifted-unit-tensor-composition).

Proof plan, following the six steps of the node:
1. The regular module is flat by the sheaf tensor unit isomorphism. Its shifts are
   bounded flat-term K-flat complexes by `lem-pc-kflat-closure`; shift extraction
   preserves this condition. Use `lem-weil-pbc-derived-tensor-shift-descent` to compute
   the structural comparisons on these representatives, with the canonical monoidal
   constraints of `lem-sf-ringed-derived-closed-symmetric-monoidal`.
2. Second-shift extraction and the right unitor are natural on every derived arrow,
   so their composite kappa is natural on every derived arrow too.
3. With first factor I in degree zero, the second-extraction sign is one. Both kappa
   at I and the left unitor are coefficient multiplication on the single summand.
4. Factor f tensor g into f tensor identity followed by identity tensor g. Left-unitor
   naturality, step 3, and kappa naturality give the three consecutive equalities.
5. In split, first extraction is unsigned and the remaining first factor has degree
   zero, so second extraction is unsigned. In kappa at S_p the sign is (-1)^((-q)p).
   Thus kappa after split equals (-1)^(pq) times ordinary shift addition.
6. Choose t(p,q)=(pq).negOnePow in the integer units, independently of the site and R.
   Its zero-coordinate values are one. Precompose step 4 by split and apply step 5.
   For the zero ring all maps are zero but the same integer sign is still defined;
   no chain-map representative of f or g is used anywhere. -/
theorem shifted_unit_tensor_composition :
    ∃ t : ℤ × ℤ → ℤˣ,
      (∀ p : ℤ, t (p, 0) = 1) ∧ (∀ q : ℤ, t (0, q) = 1) ∧
      ∀ {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
        [HasSheafify J AddCommGrpCat.{max c v u}]
        [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
        (R : Sheaf J CommRingCat.{max c v u})
        [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)],
        RingedIdentities.{c, v, u, w} J R t := by
  sorry

end CategoryTheory.ShiftedRegularUnit
