/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstructionData

import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerFiniteReduction
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerDerivedComplete
import WeilConjectures.AlgebraicGeometry.SmoothPurityCofinalIntegralBounds
import all WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated

/-!
# Reconstruction of a normalized smooth-purity coefficient tower

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-sp-tower/_section.md`; Stacks Project, Tags 0940 and 099P
(blueprint: sk-lem-sp-tower).

The natural index n denotes positive exponent n+1. A Roos triangle specifies the
actual derived inverse limit and its projections. The comparison at each finite level
is the tensor-restriction adjoint of that projection, in the finite-coefficient category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

variable (D : SpCoefficientTowersAbelian l E T)

private theorem spReconstructionTor_of_iso (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro Q P hQ f hf hP N i hi
  obtain ⟨eQ⟩ := hQ
  exact h.2 Q P ⟨eQ ≪≫ e.symm⟩ f hf hP N i hi

/-- A normalized constructible finite-Tor tower is reconstructed by its derived inverse
limit. The limit belongs to the recorded integral bounded constructible category, and
its canonical ell-power reductions are isomorphisms in the finite-coefficient categories.
The Roos presentation binds the limit and its projections, rather than adding a
condition on the tower. Source: blueprint main-20261015, sk-lem-sp-tower, order 1823;
Stacks Tags 0940 and 099P (blueprint: sk-lem-sp-tower).

Proof, following the twelve DAG steps:
1. Put O = O_E, R = O_(E,T), B_n = (O/ell^n)_T. The coefficient-tower definition
identifies R with the limit of B_n. The DVR theorem gives ell = unit times pi^e,
e >= 1, and cofinal ell- and pi-power ideals. Constant-completion flatness identifies
R/ell^m with B_m and makes multiplication by ell^m injective. Thus [R -> R], with
map ell^m in degrees [-1,0], is a finite free K-flat resolution of B_m. The analogous
pi-power resolution also exists. Each O/pi^s is finite by its residue-field filtration.
2. Take common cohomological and Tor bounds for the given tower, enlarging them to
one interval [a,b]. Resolve its levels successively by flat-term K-flat complexes,
representing the actual transitions by roofs and then chain maps. Their composites
retain every transition. Sequential evaluation fullness lifts the compatible finite
level identifications to an isomorphism of strict completed-ring derived towers.
It is existence, not uniqueness, of that lift which is needed; all projections agree.
3. Pro-etale repleteness implies exact countable products of modules: successively
replace one target coordinate by its source in a countable product of epimorphisms
and apply repleteness to the resulting surjective tower. Kernels commute with products.
Consequently products and the Roos model are computed termwise. Removing a finite
prefix preserves the model: its 1-shift matrix is triangular with identity diagonal,
and finite elimination splits off its contractible cone, preserving tail projections.
4. For n >= m the augmentation [B_n -> B_n] -> B_m, with map ell^m, has fiber
B_m[1]. Multiplication by ell^(n-m) identifies its degree -1 kernel with B_m.
The transition from n' to n on this fiber is multiplication by ell^(n'-n), including
n = m, where the kernel identification is the identity.
5. Tensor the fiber triangles with the K-flat level representatives Q_n. The middle
tower is Q_n tensor_R [R -> R]; the right tower is Q_n tensor_(B_n) B_m. The left
tower is the shifted right tower with transitions multiplied by ell^(n'-n).
Normalization identifies the actual reduction maps of the right tower with Q_m;
the strict cocycle makes this a map to the constant Q_m tower, not unrelated isomorphisms.
6. Every m consecutive transitions on the left tower are zero. Its shift is nilpotent,
so a finite geometric sum inverts 1-shift and its derived limit vanishes. Exactness
identifies the middle and right limits. The constant Q_m tower has limit Q_m because
finite partial sums split its product difference map and its kernel is the diagonal.
7. Tensor with the two-term finite free resolution commutes with the termwise products
and cones of the Roos model, with the usual differential signs. K-flat resolution of
the limit shows that this computes its derived tensor with B_m. All comparisons
preserve the m-th projection, so the resulting isomorphism is projection-induced.
8. Ordinary tensor-restriction adjunction sends f to c tensor x maps to c f(x).
Restriction is exact and detects acyclic cones. The derived adjunction therefore
identifies the preceding isomorphism with spTowerReconstructionMap in D(B_m), where
it is consequently an isomorphism. The maps [R -> R] for k <= m are (ell^(m-k),1);
together with the original transition cocycle they retain quotient compatibility.
9. For completeness use [R -> R] with map pi^j. Each Q_n is termwise killed by pi^(en).
For j >= en its tensor is Q_n plus Q_n[1], with identity transitions on the first
summand and pi on the second. The second tower is nilpotent and has zero derived
limit, while the first is constant. The canonical completion map for each row is
therefore an isomorphism. The cutoff is allowed to depend on n.
10. The two derived limits commute by expanding their two Roos cones: the four
components have the same doubly indexed products. Swap the two Roos degrees with
sign (-1)^(pq); the differentials agree since the two shifts commute. There are only
four summands per total degree. Finite-free tensor commutes with these products,
so the resulting limit comparison is the completion unit itself. Constant-completion
equivalence identifies Koszul and quotient completion, respecting that unit.
11. Products commute with cohomology and the levels have support in [a,b]. The long
exact sequence of the Roos triangle gives support of the limit in [a,b+1]. No
quasi-compactness of T, or an unjustified sharper bound, is asserted.
12. For j >= 1 choose N with eN >= j. The quotient O/pi^j is a quotient of O/ell^N.
K-flat scalar associativity identifies the uniformizer reduction of the limit with
C_N tensor_(B_N) (O/pi^j)_T. Finite-coefficient scalar extension preserves
constructibility and the common Tor interval [a,b], with no flatness or finite
projective-dimension assumption on that quotient. Testing Tor amplitude with the
quotient ring itself gives the same cohomological interval for all j. Together with
derived completeness these are precisely sfIntegralConstructible. No invertibility
of ell on T is used, and ell is never identified with the uniformizer. -/
theorem spTower_reconstruction (C : spDerivedCoefficientTowers l E T D)
    (hC : spConstructibleTorTowers l E T D C)
    (hnorm : IsSpNormalizedTower l E T D C)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ) :
    WeilConjectures.sfIntegralConstructible l E T M ∧
      ∀ n : ℕ, IsIso (spTowerReconstructionMap l E T D C M p n) := by
  classical
  have hred (n : ℕ) : IsIso (spTowerReconstructionMap l E T D C M p n) :=
    spTower_projection_finite_reduction l E T D C hnorm M p δ hlim n
  obtain ⟨a, b, c, d, _hab, hcd, hbounds⟩ := hC.2
  have hell (n : ℕ) :
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((DerivedCategory.homologyFunctor _ i).obj
          ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M))) ∧
      Scheme.HasProEtaleTorAmplitude T
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
        ((D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj M) c d := by
    let := hred n
    let e := asIso (spTowerReconstructionMap l E T D C M p n)
    refine ⟨fun i ↦ ?_, ?_⟩
    · exact Scheme.constructibleProEtale_of_iso T _
        ((DerivedCategory.homologyFunctor _ i).mapIso e.symm) ((hC.1 n).2.1 i)
    · exact spReconstructionTor_of_iso T _ e.symm (hbounds n).2
  have hpi := sp_cofinal_integral_reduction_bounds l E T D M c d hcd hell
  refine ⟨⟨spTower_limit_derived_complete l E T D C M p δ hlim,
    c, d, hcd, ?_⟩, hred⟩
  intro n
  have hs : Scheme.proEtaleCohomologicalSupport
      ((WeilConjectures.scalarReductionDerivedExtension.{u, u} l E T n).obj M) ⊆
        Set.Icc c d := by
    intro i hi
    constructor
    · by_contra h
      exact hi ((hpi n).2 i (Or.inl (lt_of_not_ge h)))
    · by_contra h
      exact hi ((hpi n).2 i (Or.inr (lt_of_not_ge h)))
  exact ⟨⟨(Set.finite_Icc c d).subset hs, (hpi n).1⟩, hs⟩

end AlgebraicGeometry.ProEtale
