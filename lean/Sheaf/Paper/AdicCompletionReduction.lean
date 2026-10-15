/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.CompletionMap
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Paper.StrictPerfectCoefficientPackage
import Sheaf.Paper.IntrinsicKoszulCompletion
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.Paper.KoszulQuotientLimit

/-!
# Reduction of adic completion

Source: Weil conjectures blueprint, proper base change, order 1260,
`lemma-weil-pbc-adic-completion-reduction.md`
(blueprint: lemma-weil-pbc-adic-completion-reduction).

The completion object and its evaluation are those of the landed strict product-cone
construction. Its reduction is computed on an arbitrary K-flat model of that object.
The comparison is defined by the derived scalar adjunction, using its unit, so the
isomorphism assertion concerns the specified evaluation map. Positive level a is n+1.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction of scalars is exact, also when the small site's object and morphism
universes differ. Source: order 1260, proof step 6; Stacks Tag 03D3.
Proof: restriction leaves the underlying abelian sheaf unchanged. Kernels and cokernels
are computed on those sheaves, with the restricted action, so it preserves both.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) := by
  sorry

/-- Exact derived restriction along the constant coefficient map.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicDerivedRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategory

/-- The canonical factorization of derived restriction through termwise restriction.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicDerivedRestrictFactors (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :
    (adicDerivedRestrict X φ).obj ((adicLocalization X B).obj P) ≅
      (adicLocalization X A).obj (adicRestrict X φ P) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X A))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X B))
  letI := (adicRestrictScalars_exact X φ).1
  letI := (adicRestrictScalars_exact X φ).2
  (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapDerivedCategoryFactors.app P

/-- The unit L → Res(L tensor P_(n+1)), with its canonical tensor-generator formula.
Source: order 1260, adjunction in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionDerivedUnit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ) :
    L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj
      (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩) :=
  N.realization.inv ≫ (adicLocalization X Λ).map (adicReductionAugmentation X d N n) ≫
    (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
      (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) N.complex)).inv

/-- The unit characterizes the derived scalar adjunction bijection.
Source: order 1260, proof step 6; Stacks Tags 03D3, 09T5 and 06YY.
Proof: ordinary scalar extension is left adjoint to restriction
(lem-weil-pbc-ringed-topoi-module-adjunction). Restriction is exact by
adicRestrictScalars_exact. Derive the adjunction using lem-pc-derived-adjoint-functors;
lem-pur-derived-change-of-rings computes its left adjoint on N. The ordinary unit sends
m to 1 tensor m, so the canonical derived unit is exactly adicReductionDerivedUnit.
The Hom bijection therefore has the stated formula, for every quotient-coefficient H.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicReductionAdjunction_bijective (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    Function.Bijective (fun f : adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H ↦
      adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f) := by
  sorry

/-- The canonical Hom equivalence, rather than an arbitrary choice of adjunction.
Source: order 1260, proof step 6 (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionHomEquiv (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H) :=
  Equiv.ofBijective _ (adicReductionAdjunction_bijective X d N n H)

/-- Evaluation from the specified strict product-cone limit at level n+1.
Source: order 1260, statement (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionEvaluation (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (n : ℕ) :
    adicCompletionObject X d M ⟶ adicReductionSequence X d M n :=
  (adicLocalization X Λ).map
    (adicCompletionProjection X d M ≫ Pi.π (adicReductionComplex X d M) n)

/-- The adjoint of evaluation, with the quotient coefficient action retained.
Source: order 1260, displayed map (blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionReduction (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) :
    adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ :=
  (adicReductionHomEquiv X d N n _).symm
    (adicCompletionEvaluation X d M n ≫
      (adicDerivedRestrictFactors X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
        (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)).inv)

/-- Every finite reduction of completion is the original reduction, via evaluation's
adjoint. No derived completeness of K is assumed.
Source: order 1260, displayed assertion; Stacks Tags 099M and 091Z.
Proof:
1. Choose the fixed K-flat flat-term model M. Replace its strict quotient tower by the
Koszul tower using lemma-weil-pbc-koszul-quotient-limit; the comparison is induced by
its quotient augmentations (def-weil-pbc-intrinsic-koszul-completion).
2. Since P_a is perfect, choose a bounded finite-projective resolution. Constant sheaves
and exact sheafification preserve its quasi-isomorphism. The package
 def-weil-pbc-strict-perfect-coefficient-package realizes its terms as retracts of finite
free constant module sheaves. Tensor by each term commutes with products, first on finite
free terms coordinatewise and then by the same idempotent on retracts. Boundedness makes
each total diagonal finite. Exact countable products
(lem-weil-proetale-countable-products-exact) compute derived products by
lem-weil-derived-limit-products-core. Tensor thus commutes with the two products and cone.
3. Reassociate total tensors. Discard levels m<a: on the finite removed prefix the shift
is nilpotent, so 1-s has its finite geometric-series inverse and its cone is contractible.
For a=1 no level is removed. K-flatness justifies replacing the perfect resolution by P_a.
4. For m≥a, all f_j^m vanish in P_a and the Koszul differential is zero. In negative
Koszul degree each a-fold transition has a factor f_j^a and vanishes. In degree zero
the transition is identity. The reduced tower splits into the constant degree-zero
complex and finitely many shifted pro-zero towers, with no cross differentials.
5. The latter towers have zero derived limit by
lem-weil-pbc-ringed-strict-tower-homotopy-limit. On the constant tower 1-s is split
surjective by finite partial sums and has diagonal kernel. Its fibre evaluates to the
constant object identically. This gives the claimed isomorphism after scalar restriction.
6. The Koszul augmentations identify the resulting map with evaluation's adjoint: on
generators it is c tensor q tensor z ↦ c tensor qbar*z in degree zero, zero in negative
degrees. The derived adjunction is lem-weil-pbc-ringed-topoi-module-adjunction followed
by lem-pc-derived-adjoint-functors, with left adjoint computed by
lem-pur-derived-change-of-rings. Exact restriction reflects vanishing of cone cohomology,
so this map is an isomorphism in the quotient-coefficient category itself. All formulas
commute with representative maps; the naturality statement below records this explicitly.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicCompletionReduction_isIso (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (n : ℕ) : IsIso (adicCompletionReduction X d M N n) := by
  sorry

/-- Reduction on a derived morphism, characterized by the naturality of the scalar unit.
Source: order 1260, functoriality in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K') (n : ℕ) (f : K ⟶ K') :
    adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M' ⟨n + 1, Nat.succ_pos n⟩ :=
  (adicReductionHomEquiv X d M n _).symm (f ≫ adicReductionDerivedUnit X d M' n)

/-- The strict reduction of a chain map between the chosen models.
Source: order 1260, functoriality in proof step 6
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicReductionComplexMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionComplex X d M n ⟶ adicReductionComplex X d M' n :=
  ((SheafOfModules.restrictScalars.{t + 1}
    (adicModuleMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1))))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (adicChangeHom X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) f)

/-- Quotient transitions are natural in the original complex.
Source: order 1260, proof step 6.
Proof: both paths send r tensor m to q(r) tensor f(m). The local tensor generators
characterize the sheaf maps and therefore their chain maps uniquely.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicReductionComplexMap_step (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionComplexMap X d M M' f (n + 1) ≫
        adicReductionComplexStep X d M' n =
      adicReductionComplexStep X d M n ≫ adicReductionComplexMap X d M M' f n := by
  sorry

/-- Completion of a model map, using the same product map in both cone coordinates.
Source: order 1260, proof step 6; the strict cone construction at order 1258
(blueprint: lemma-weil-pbc-adic-completion-reduction). -/
noncomputable def adicCompletionModelMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) :
    adicCompletionObject X d M ⟶ adicCompletionObject X d M' :=
  (adicLocalization X Λ).map
    (adicCompletionTowerMap X d M M' (adicReductionComplexMap X d M M' f)
      (adicReductionComplexMap_step X d M M' f))

/-- The comparison is natural on all K-flat representatives. Since those representatives
localize to the derived category, this is functoriality in K, including the inverse maps
of quasi-isomorphisms; no particular resolution or boundedness is required.
Source: order 1260, functoriality clause and proof step 6.
Proof: scalar extension's unit is natural, with formula m ↦ 1 tensor m. Evaluation from
the cone is natural for the product map in both coordinates, by
adicCompletionTowerMap_exists. Thus the two sides have the same adjoint under
adicReductionHomEquiv, namely evaluation followed by the scalar-restricted reduction
of f. Injectivity of that equivalence gives equality. K-flat resolutions and
lem-pur-derived-change-of-rings identify model changes canonically, so the equality
passes through roofs and inverts quasi-isomorphisms.
(blueprint: lemma-weil-pbc-adic-completion-reduction) -/
theorem adicCompletionReduction_naturality (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (N : AdicKFlatModel X Λ (adicCompletionObject X d M))
    (N' : AdicKFlatModel X Λ (adicCompletionObject X d M'))
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionMap X d N N' n (adicCompletionModelMap X d M M' f) ≫
        adicCompletionReduction X d M' N' n =
      adicCompletionReduction X d M N n ≫
        adicReductionMap X d M M' n
          (M.realization.inv ≫ (adicLocalization X Λ).map f ≫ M'.realization.hom) := by
  sorry

end AlgebraicGeometry.Scheme
