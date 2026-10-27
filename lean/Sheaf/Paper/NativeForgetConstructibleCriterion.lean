module

public import Sheaf.Paper.NativeEncodingDerivedOperations
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence
import Sheaf.Paper.NativeModuleConstructibilityComparison
import Sheaf.Paper.FiniteConstantStratifiedZariskiLocality

/-! # Forgetful constructibility criterion for native Weil complexes

Source: Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.8; native
Adic/Constructible.lean and WeilSheaf/Category.lean. The finite Tor bound is the
coefficient-field case of the blueprint's localizing-closure comparison.
(blueprint: lem-sf-native-forget-constructible-criterion).

The scalar dimension is expressed by an isomorphism to the existing finite free
scalar module of rank r. This includes r = 0 and permits independent ranks on each
covering member. All derived categories are the ordinary unbounded localizations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeEncoding

/-- Native constructibility is detected by the specified encoding, the native local
stratifications globalize, scalar models are finite free with the specified rank,
and forgetting Frobenius detects cohomological support, bounded constructibility,
and finite Tor amplitude, with the bound [a-1,b].

Source: Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.8; native
Adic/Constructible.lean:84-149 and WeilSheaf/Category.lean; the coefficient-field
Tor bound of det-def-localizing-closure-ctf-equals-bc(2).
(blueprint: lem-sf-native-forget-constructible-criterion).

Proof:
1. Apply lem-pod-separated-finite-type-base-change to the structure map and the
algebraic closure. Apply lem-weil-pbc-qcqs-over-affine over Spec of that field.
Thus the geometric fibre is separated, finite type, qcqs and Noetherian.
2. For a scalar basis e_j of P, send s tensor sum c_j e_j to (c_j s)_j; the inverse
sends (s_j)_j to sum s_j tensor e_j. Balancing gives inverse module maps on sections,
compatible with restrictions. For rank zero use the empty sum. The sectionwise
encoding of lem-sf-native-encoding-derived-operations takes native B^r to R^r.
3. Apply lem-sf-weil-verdier-module-constructibility-comparison on the same strata
and covers. The encoding commutes with restrictions, so the finite free and scalar
models identify both local predicates. Apply lem-sfb-constructible-zariski-locality
on the qcqs geometric fibre and transport the resulting global finite stratification
back to native modules. Conversely a global native stratification is locally one.
4. By lem-sf-native-weil-constructible-abelian, forgetting Frobenius is exact and
conservative. By lem-sf-native-encoding-derived-operations, encoding is an exact
equivalence. Compose the inverse comparisons of
lem-pur-exact-derived-cohomology-coherence to obtain the displayed natural
isomorphism on the entire ordinary derived category, with no boundedness premise.
5. Exact functors preserve zero. Conversely the encoding reflects zero, and
conservativity of forgetting makes 0 to H^n(C) invertible whenever its image is zero.
The natural comparison therefore detects vanishing in each degree. Checking all
integers outside an interval proves preservation and reflection of its support.
6. Unfold def-sf-native-weil-derived-framework: its object predicate is boundedness
and native constructibility of each forgotten cohomology object. Steps 3-5 identify
these with boundedness and coefficient constructibility in every degree, which is
constantModelBoundedConstructible from det-def-sfb-constructible-tor-amplitude.
7. Apply det-def-localizing-closure-ctf-equals-bc(2) over the specified condensed
algebraically closed coefficient field. Bounded constructible cohomology in [a,b]
has Tor amplitude in [a-1,b]. Conversely Dctf includes bounded constructibility
by det-def-sfb-constructible-tor-amplitude(4). This proves both predicate
equivalences and the bound, also for the empty scheme and zero complex. -/
theorem native_forget_constructible_criterion
    (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    (∀ M : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      (IsAdicConstructibleSheaf M ↔
        IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          ((encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj M)) ∧
      (IsAdicConstructibleSheaf M ↔ IsAdicStratifiedLisseSheaf M)) ∧
    (∀ (U : Scheme.{u})
      (P : Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj l))) (r : ℕ),
      Nonempty (P ≅ Mod.finiteFree (scalarRingObj (Profinite.padicAlgClRingObj l)) r) →
        Nonempty ((finiteConstantScalarExtension (Profinite.padicAlgClRingObj l) U).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) U) r) ∧
        Nonempty ((encoding l U).obj (Mod.finiteFree (adicConstantSheaf l U) r) ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) U) r)) ∧
    (∀ n : ℤ,
      Nonempty (realization k₀ l X ⋙ DerivedCategory.homologyFunctor _ n ≅
        DerivedCategory.homologyFunctor _ n ⋙
          Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙
            encoding l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ∧
    (∀ (C : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (n : ℤ),
      IsZero ((DerivedCategory.homologyFunctor _ n).obj C) ↔
        IsZero ((DerivedCategory.homologyFunctor _ n).obj ((realization k₀ l X).obj C))) ∧
    (∀ (C : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (a b : ℤ),
      (∀ n : ℤ, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor _ n).obj C)) ↔
        (∀ n : ℤ, n < a ∨ b < n →
          IsZero ((DerivedCategory.homologyFunctor _ n).obj ((realization k₀ l X).obj C)))) ∧
    (∀ C : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      (WeilComplex.objectProperty k₀ l X C ↔
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ((realization k₀ l X).obj C)) ∧
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ((realization k₀ l X).obj C) ↔
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ((realization k₀ l X).obj C) ∧
          DerivedCategory.finiteTorAmplitude _ ((realization k₀ l X).obj C)))) ∧
    (∀ (C : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (a b : ℤ), a ≤ b →
      (∀ n : ℤ, n < a ∨ b < n →
        IsZero ((DerivedCategory.homologyFunctor _ n).obj ((realization k₀ l X).obj C))) →
      (∀ n : ℤ, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ((DerivedCategory.homologyFunctor _ n).obj ((realization k₀ l X).obj C))) →
      DerivedCategory.torAmplitudeIn _ (a - 1) b ((realization k₀ l X).obj C)) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeEncoding
