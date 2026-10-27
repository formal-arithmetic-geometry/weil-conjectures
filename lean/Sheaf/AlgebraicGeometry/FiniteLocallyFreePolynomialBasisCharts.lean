module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward

/-!
# Polynomial base change and specified principal free bases

Source: Stacks Project, exercises.tex, Tag 02DV(3); morphisms.tex, Tag 02KD;
schemes.tex, Tags 01I4, 01HV, 01IA, 01IB, 01I9; algebra.tex, Tag 00CP
(blueprint: lem-a1-finite-locally-free-polynomial-basis-charts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem polynomial_pullback {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) := by
  let := Polynomial.algebra A B
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout A B (Polynomial A) (Polynomial B))

private theorem polynomial_basis {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} (b : Module.Basis ι R S) :
    ∃ E : @Module.Basis ι (Polynomial R) (Polynomial S) _ _
      (@Algebra.toModule _ _ _ _ (Polynomial.mapRingHom (algebraMap R S)).toAlgebra),
      ∀ j, E j = Polynomial.C (b j) := by
  let := Polynomial.algebra R S
  let E := (Algebra.IsPushout.out (R := R) (S := Polynomial R)
    (R' := S) (S' := Polynomial S)).basis b
  exact ⟨E, fun j ↦ IsBaseChange.basis_apply _ _ j⟩

private theorem polynomial_localization {R : Type u} [CommRing R] (a : R)
    (p : Polynomial R) (hp : p = Polynomial.C a) :
    ∃ α : Localization.Away p ≃+* Polynomial (Localization.Away a),
      ∀ P : Polynomial R, α (algebraMap (Polynomial R) _ P) =
        Polynomial.map (algebraMap R (Localization.Away a)) P := by
  let := Polynomial.algebra R (Localization.Away a)
  have : IsLocalization.Away p (Polynomial (Localization.Away a)) := by
    rw [hp]
    simpa only [Submonoid.map_powers] using
      Polynomial.isLocalization (Submonoid.powers a) (Localization.Away a)
  exact ⟨(IsLocalization.algEquiv (Submonoid.powers p) _ _).toRingEquiv,
    (IsLocalization.algEquiv (Submonoid.powers p) _ _).commutes⟩

/-- Polynomial scalar extension preserves the degree and the specified principal bases
of a finite locally free affine algebra. The scalar actions on the two bases are written
explicitly: they are induced by the canonical localized coefficient map and its polynomial
extension. No global polynomial-algebra instance or auxiliary algebra structure is assumed.

Source: Stacks Project, Tags 02DV(3), 02KD, 01I4, 01HV, 01IA, 01IB, 01I9, and 00CP
(blueprint: lem-a1-finite-locally-free-polynomial-basis-charts).

Proof:
1. Polynomial scalar extension (lem-weil-pbc-polynomial-scalar-extension) gives the
   displayed tensor equivalence. Its inverse sends a polynomial with coefficients b_j to
   the sum of b_j tensor X^j. Balancing verifies both inverse identities.
2. The affine fibre-product theorem (lem-weil-pbc-fibre-product-affine-spectra) identifies
   the tensor spectrum with the pullback. The tensor inclusions become C and the
   coefficientwise polynomial map, so the entire displayed square is cartesian.
3. Finiteness, flatness and local finite presentation persist under arbitrary base change
   (lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence). The fibre-rank base-change formula
   (lem-weil-pbc-finite-flat-rank-iso) preserves degree r.
4. Apply C to a relation sum a_i f_i = 1 to show that the C(f_i) generate the unit ideal.
5. Coefficientwise localization factors through localization at C(f_i), by
   lem-weil-pbc-localization-away-universal-property. A finite common denominator proves
   surjectivity. If all localized coefficients vanish, a common power of f_i kills all
   coefficients, proving injectivity by def-weil-ring-localization-away. The maps commute
   with the coefficient map and further localizations because they agree on coefficients
   and X; their values on all polynomials determine them uniquely.
6. Base-change each given basis using lem-weil-pbc-free-module-base-change-free and the
   polynomial tensor equivalence. Its vectors become exactly the constant polynomials
   C(e_{i,j}), including the empty basis.
7. The affine pushforward/tilde comparison (lem-weil-pbc-pushforward-tilde-spec) identifies
   the structure-sheaf pushforward with the tilde of B[X], hence it is quasi-coherent.
   The principal localization open immersion
   (lem-weil-pbc-principal-localization-open-immersion) identifies D(C(f_i)) with
   Spec A[X]_{C(f_i)}. The sections theorem
   (lem-weil-pbc-spec-module-tilde-sections), affine tilde/Gamma adjunction
   (lem-weil-pbc-affine-tilde-gamma-adjunction), and tilde of a free module
   (lem-weil-pbc-spec-tilde-free-module) turn these bases into rank-r trivializations.
8. For r=0 the same empty-basis argument applies. If A is zero, B is zero and all spectra
   are empty; the empty cover is permitted. Zero or nilpotent f_i give zero localizations;
   the fraction argument never cancels f_i. -/
theorem finiteLocallyFree_polynomial_basis_charts
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (r m : ℕ)
    (h : (Spec.map (CommRingCat.ofHom (algebraMap A B))).IsFiniteLocallyFreeOfDegree r)
    (f : Fin m → A) (hf : Ideal.span (Set.range f) = ⊤)
    (e : (i : Fin m) →
      @Module.Basis (Fin r) (Localization.Away (f i))
        (Localization.Away (algebraMap A B (f i))) _ _
        (@Algebra.toModule _ _ _ _
          (IsLocalization.Away.map (Localization.Away (f i))
            (Localization.Away (algebraMap A B (f i))) (algebraMap A B) (f i)).toAlgebra)) :
    (∀ (b : B) (P : Polynomial A),
      (polyEquivTensor A B).symm (b ⊗ₜ[A] P) =
        P.sum (fun n a ↦ Polynomial.monomial n (b * algebraMap A B a))) ∧
    IsPullback
      (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) ∧
    (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B)))).IsFiniteLocallyFreeOfDegree r ∧
    ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B))))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (Polynomial B))).ringCatSheaf)).IsQuasicoherent ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap A B))))).obj
          (SheafOfModules.unit (Spec (CommRingCat.of (Polynomial B))).ringCatSheaf)) r ∧
    Ideal.span (Set.range (fun i : Fin m ↦ Polynomial.C (f i))) = ⊤ ∧
    ∀ i : Fin m,
      ∃ (α : Localization.Away (Polynomial.C (f i)) ≃+*
          Polynomial (Localization.Away (f i)))
        (β : Localization.Away
          ((Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))) ≃+*
          Polynomial (Localization.Away (algebraMap A B (f i)))),
        (∀ P : Polynomial A,
          α (algebraMap (Polynomial A) _ P) =
            Polynomial.map (algebraMap A (Localization.Away (f i))) P) ∧
        (∀ P : Polynomial B,
          β (algebraMap (Polynomial B) _ P) =
            Polynomial.map (algebraMap B (Localization.Away (algebraMap A B (f i)))) P) ∧
        (∀ z : Localization.Away (Polynomial.C (f i)),
          β (IsLocalization.Away.map (Localization.Away (Polynomial.C (f i)))
            (Localization.Away
              ((Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))))
            (Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i)) z) =
          Polynomial.map (IsLocalization.Away.map (Localization.Away (f i))
            (Localization.Away (algebraMap A B (f i))) (algebraMap A B) (f i)) (α z)) ∧
        ∃ E : @Module.Basis (Fin r) (Polynomial (Localization.Away (f i)))
          (Polynomial (Localization.Away (algebraMap A B (f i)))) _ _
          (@Algebra.toModule _ _ _ _
            (Polynomial.mapRingHom
              (IsLocalization.Away.map (Localization.Away (f i))
                (Localization.Away (algebraMap A B (f i)))
                (algebraMap A B) (f i))).toAlgebra),
          ∀ j : Fin r, E j = Polynomial.C (e i j) := by
  have hp := polynomial_pullback (A := A) (B := B)
  have := h
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B)))) :=
    MorphismProperty.of_isPullback hp (inferInstanceAs (IsFinite _))
  have : Flat (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B)))) :=
    MorphismProperty.of_isPullback hp (inferInstanceAs (Flat _))
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B)))) :=
    MorphismProperty.of_isPullback hp (inferInstanceAs (LocallyOfFinitePresentation _))
  have : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B)))).IsFiniteLocallyFree := ⟨⟩
  have hq : (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap A B)))).IsFiniteLocallyFreeOfDegree r := by
    refine ⟨fun x ↦ ?_⟩
    exact (Scheme.Hom.fiberDegree_of_isPullback _ hp x).trans (h.fiberDegree_eq _)
  refine ⟨polyEquivTensor_symm_apply_tmul A B, hp, hq, ?_, ?_, ?_, ?_⟩
  · have := SheafOfModules.isQuasicoherent_unit
      (R := (Spec (CommRingCat.of (Polynomial B))).ringCatSheaf)
    exact Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _ _
  · have := hq
    exact Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit _ r
  · have hh := congrArg (Ideal.map (Polynomial.C : A →+* Polynomial A)) hf
    simpa only [Ideal.map_span, Ideal.map_top, ← Set.range_comp, Function.comp_def] using hh
  · intro i
    obtain ⟨α, hα⟩ := polynomial_localization (f i) (Polynomial.C (f i)) rfl
    obtain ⟨β, hβ⟩ := polynomial_localization (algebraMap A B (f i))
      ((Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i)))
      (Polynomial.map_C (algebraMap A B))
    refine ⟨α, β, hα, hβ, ?_, ?_⟩
    · intro z
      have hh : β.toRingHom.comp
          (IsLocalization.Away.map (Localization.Away (Polynomial.C (f i)))
            (Localization.Away
              ((Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))))
            (Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))) =
          (Polynomial.mapRingHom (IsLocalization.Away.map (Localization.Away (f i))
            (Localization.Away (algebraMap A B (f i))) (algebraMap A B) (f i))).comp
            α.toRingHom := by
        apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C (f i)))
        apply RingHom.ext
        intro P
        change β (IsLocalization.Away.map (Localization.Away (Polynomial.C (f i)))
            (Localization.Away
              ((Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))))
            (Polynomial.mapRingHom (algebraMap A B)) (Polynomial.C (f i))
            (algebraMap (Polynomial A) _ P)) =
          Polynomial.map (IsLocalization.Away.map (Localization.Away (f i))
            (Localization.Away (algebraMap A B (f i))) (algebraMap A B) (f i))
            (α (algebraMap (Polynomial A) _ P))
        rw [IsLocalization.Away.map, IsLocalization.map_eq, hβ, hα]
        simp only [Polynomial.coe_mapRingHom, Polynomial.map_map]
        congr 1
        apply RingHom.ext
        intro a
        simp only [RingHom.comp_apply, IsLocalization.Away.map, IsLocalization.map_eq]
      exact RingHom.congr_fun hh z
    · let := (IsLocalization.Away.map (Localization.Away (f i))
        (Localization.Away (algebraMap A B (f i))) (algebraMap A B) (f i)).toAlgebra
      exact polynomial_basis (e i)

end AlgebraicGeometry
