module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Sheaf.RingTheory.AdicRingCompletionMap
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.RegularMapReducedTarget
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Completeness
import Sheaf.FieldTheory.SeparableMonicApproximation
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import Sheaf.RingTheory.ExcellentRing
import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.HeightOneRealAbsoluteValue

/-!
# Formal comparison over a height-one valuation ring

Source: Temkin, Stable modification of relative curves, Theorem 3.5.5, Step 3,
pp. 22--23 (blueprint: lem-trf-valuation-rank-one-formal-comparison).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace ValuationRing

/-- The conclusions of formal comparison, with normed realizations of the actual localized
completions. Ring equivalences transport the norms without changing the canonical algebraic
constructions. Every map is fixed by its scalar, residue, pure-tensor, or dense-extension
characterization. The `let`s below only name objects inside this definition.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: lem-trf-valuation-rank-one-formal-comparison). -/
def HasRankOneFormalComparison
    (K : Type u) (V : Type v) (A : Type w)
    [Field K] [CommRing V] [CommRing A] [Algebra V K] [Algebra V A]
    (π : V) (F : Type v) [NormedField F] [IsUltrametricDist F]
    (B : Type w) [NormedCommRing B] : Prop :=
  let Vh := AdicCompletion (Ideal.span {π}) V
  let Ah := AdicCompletion (Ideal.span {algebraMap V A π}) A
  let πh := algebraMap V Vh π
  let πA := algebraMap V A π
  let Kh := Localization.Away πh
  let C := Localization.Away (algebraMap A Ah πA)
  let jV := AdicCompletion.principalRingMap (algebraMap V A) π
  ∃ (eF : Kh ≃+* F) (W : Subring F) (eV : Vh ≃+* W) (eC : C ≃+* B)
    (scalar : F →+* B) (iK : K →+* F) (t : A ⊗[V] K →+* B),
    CompleteSpace F ∧ IsAlgClosed F ∧
    (∀ x : F, x ∈ W ↔ ‖x‖ ≤ 1) ∧
    (∀ x : Vh, (eV x : F) = eF (algebraMap Vh Kh x)) ∧
    0 < ‖(eV πh : F)‖ ∧ ‖(eV πh : F)‖ < 1 ∧
    (∀ x : V, iK (algebraMap V K x) = (eV (algebraMap V Vh x) : F)) ∧
    (∀ x : Vh, scalar (eF (algebraMap Vh Kh x)) =
      eC (algebraMap Ah C (jV x))) ∧
    RingHom.Flat jV ∧
    RestrictedSeries.IsTopologicallyFinitelyPresented W Ah
      (jV.comp eV.symm.toRingHom) (eV πh) ∧
    IsReduced B ∧ RestrictedSeries.IsAffinoidQuotient F B scalar ∧
    RestrictedSeries.HasBoundedTopologicallyGeneratedImage W Ah B
      (jV.comp eV.symm.toRingHom) (eC.toRingHom.comp (algebraMap Ah C)) ∧
    (∀ (a : A) (k : K), t (a ⊗ₜ[V] k) =
      eC (algebraMap Ah C (algebraMap A Ah a)) * scalar (iK k)) ∧
    (∀ (E : Type (max u v w)) [CommRing E] [Algebra V E]
      [Module.Flat V E] [Algebra.FinitePresentation V E] (s : V), s ≠ 0 →
      ∀ x : E,
        (algebraMap E (AdicCompletion (Ideal.span {algebraMap V E π}) E) x ∈
          Ideal.span {algebraMap V (AdicCompletion (Ideal.span {algebraMap V E π}) E) s}) ↔
        x ∈ Ideal.span {algebraMap V E s}) ∧
    ∀ (E : Subalgebra A (A ⊗[V] K)) [Module.Finite A E]
      [Module.FinitePresentation A E] [Module.Flat V E] [Algebra.FinitePresentation V E],
      let πE := algebraMap A E πA
      let Eh := AdicCompletion (Ideal.span {πE}) E
      let jA := AdicCompletion.principalRingMap (algebraMap A E) πA
      ∃ (tensorIso : (Ah ⊗[A] E) ≃+* Eh) (g : Eh →+* B)
        (localizedIso : Localization.Away (algebraMap E Eh πE) ≃+* B),
        (∀ (a : Ah) (e : E), tensorIso (a ⊗ₜ[A] e) =
          jA a * algebraMap E Eh e) ∧
        Function.Injective g ∧
        @Continuous _ _ (Ideal.span {algebraMap E Eh πE}).adicTopology
          inferInstance g ∧
        (∀ e : E, g (algebraMap E Eh e) = t e.val) ∧
        (∀ a : Ah, g (jA a) = eC (algebraMap Ah C a)) ∧
        ∀ e : Eh, localizedIso (algebraMap Eh
          (Localization.Away (algebraMap E Eh πE)) e) = g e

/-- Formal comparison over a nontrivial height-one valuation ring. In particular, completion
of the original algebra need not be injective, and the zero affinoid algebra is included.
Source: Temkin, Theorem 3.5.5, Step 3, pp. 22--23
(blueprint: lem-trf-valuation-rank-one-formal-comparison).

Proof (the node's eleven steps):
1. The height-one real-absolute-value lemma gives a nontrivial real norm. Powers of `π`
   are cofinal among small balls. Compatible residues identify the completed ring with the
   unit ball in the metric completion of `K`; bounded Cauchy sequences show its fraction
   localization is that completion. Inverses converge by the usual difference-of-inverses
   estimate, so it is a complete field.
2. Approximate monic polynomials by separable monic polynomials over `K`, using
   lem-trf-separable-monic-approximation. Their roots lie in `K` by separable linear
   factorization. Uniform root bounds and the product formula give successive roots at
   distances less than `2⁻ʲ`; their limit is a root of the original polynomial.
3. Cancellation on successive residues makes completion `π`-torsion-free. Every nonzero
   scalar divides a power of `π`, so completed modules are torsion-free, hence flat over
   the completed valuation ring (lem-trf-valuation-torsionfree-flat).
4. For a short exact sequence with torsion-free quotient, intersection with `πⁿM` is
   `πⁿL`. Residue kernels have surjective transitions; tower-limit exactness gives an
   exact sequence of completions.
5. Apply step 4 twice to a finite polynomial presentation and its relations. The
   polynomial completion is the restricted-series ring; the quotient has exactly the
   finitely generated displayed relations and the adic quotient topology.
6. Invert `π`. Bounded coefficients give the Tate presentation, its Banach quotient norm,
   and the bounded image of the unit-ball series. Polynomials are dense in that image.
7. Geometric reducedness makes the algebraic base change reduced. Fields and finite-type
   localizations are excellent. The algebraic/affinoid closed-point-completion comparison
   identifies completed local rings; regular completion maps preserve reducedness.
8. Krull intersection injects each Noetherian affinoid local ring into its completion.
   Local detection of nilpotents makes the affinoid reduced, also for the zero ring.
9. Given nonzero `s`, choose `N` with `πᴺ ∈ sV`. Reducing a completed divisibility equation
   modulo `πᴺ` proves scalar saturation, without injectivity of the completion map.
10. Complete a finite module presentation of `E` using step 4 twice. Its matrix cokernel
    is also `Ah ⊗[A] E`, giving the canonical pure-tensor comparison isomorphism.
11. Clear the denominators of finitely many generators of `E ⊆ A_K` by `q = πᵏ`.
    The two maps have composites multiplication by `q`; completion preserves this.
    Torsion-freeness gives the continuous injection into the localized completion, and
    inverting `π` gives the asserted isomorphism. These maps agree with the original
    inclusions and the scalar maps. No separation assumption is used. -/
theorem valuation_rank_one_formal_comparison
    (K : Type u) (V : Type v) (A : Type w)
    [Field K] [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing A] [Algebra V K] [IsFractionRing V K] [IsSepClosed K]
    [Algebra V A] [Module.Flat V A] [Algebra.FinitePresentation V A]
    (hheight : ∀ p : Ideal V, p.IsPrime → p = ⊥ ∨ p = IsLocalRing.maximalIdeal V)
    (π : V) (hπ : π ≠ 0) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hgeom : @Algebra.IsGeometricallyReduced K (A ⊗[V] K) inferInstance inferInstance
      Algebra.TensorProduct.rightAlgebra) :
    ∃ (F : Type v) (nf : NormedField F) (hu : @IsUltrametricDist F nf.toDist)
      (B : Type w) (nb : NormedCommRing B),
      @HasRankOneFormalComparison K V A inferInstance inferInstance inferInstance
        inferInstance inferInstance π F nf hu B nb := by
  sorry

end ValuationRing
