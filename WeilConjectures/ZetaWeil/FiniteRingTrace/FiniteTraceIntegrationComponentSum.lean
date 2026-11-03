/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteTraceLocalTerm
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd

/-! # Integration splits over the open–closed components

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-p-local/
lem-trf-integration-component-sum.md (blueprint: lem-trf-integration-component-sum).

Everything is stated over the specified constructions of def-trf-local-term
(`Sheaf.Paper.FiniteTraceLocalTerm`), with no restatement:
* the open-and-closed piece `β` of `T` is `clopenPiece T U` for an open `U` of `T` that is
  open and closed (`Fact (IsClopen U)`), and `j_β` is `clopenInclusion T U`;
* the restriction `τ|_β : A_β ≅ Lj_β^*A_T → Lj_β^*ω_{T,A} ≅ Rj_β^!ω_{T,A} ≅ ω_{β,A}` is
  `restrictSection` (open purity in relative dimension `0` via `clopenPurity`, then
  `dualizingComposition` of thm-trf-dualizing-complex-composition);
* `∫_Y` is `sectionIntegral`, the scalar of the integration composite of def-trf-integration;
  at `A = A_{E,n}` it is literally `traceFormulaIntegration` (second theorem below);
* the dualizing complex is `dualizingComplex` of def-trf-dualizing-complex;
* the fixed scheme is `tmFixed c` with the component convention
  `HasFiniteClopenConnectedComponents` and components `clopenConnectedComponentOpen`
  of def-trf-fixed-scheme; the component restriction is `componentTraceClass` and the
  component integral is `componentLocalTerm` of def-trf-local-term.

The finite disjoint-union presentation `T = ∐_{β ∈ B} β` is a finite family `U : B → T.Opens`
of open-and-closed subsets that are pairwise disjoint and cover `T`; `B` may be empty.
As in def-trf-local-term, the coefficient ring is an arbitrary finite commutative ring killed
by a power of `ell`; the blueprint's `A = A_{E,n}` is the special case, stated separately with
`traceFormulaIntegration`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
-- Keep the published theorem's geometric hypotheses and Fintype binder unchanged.
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace

attribute [local instance] vdDiscreteTopology tmDiscrete tmTopologicalRing tmCharPrime

-- Reuse the finite-index induction of GoodCurvesPreimageBoundary, reducing to
-- proper_coproduct_two rather than duplicating the finite-union topological argument.
private theorem proper_sigma_desc
    {I : Type u} [Finite I] {B : Scheme.{u}} (C : I → Scheme.{u})
    (c : ∀ i, C i ⟶ B) (hc : ∀ i, IsProper (c i)) : IsProper (Sigma.desc c) := by
  refine Finite.induction_empty_option (P := fun I ↦ ∀ [Finite I] (C : I → Scheme.{u})
    (c : ∀ i, C i ⟶ B), (∀ i, IsProper (c i)) → IsProper (Sigma.desc c))
    ?_ ?_ ?_ I C c hc
  · intro A D e hA _ C c hc
    have : Finite A := Finite.of_equiv _ e.symm
    have := hA (fun a ↦ C (e a)) (fun a ↦ c (e a)) fun a ↦ hc (e a)
    have he : (Sigma.whiskerEquiv e fun a ↦ Iso.refl (C (e a))).hom ≫ Sigma.desc c =
        Sigma.desc fun a ↦ c (e a) := by
      ext a
      simp
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper
      (Sigma.whiskerEquiv e fun a ↦ Iso.refl (C (e a))).hom, he]
    infer_instance
  · intro _ C c _
    have : IsEmpty ↥(∐ C) := isInitial_iff_isEmpty.mp
      ⟨IsInitial.ofUniqueHom (fun _ ↦ Sigma.desc fun i ↦ i.elim)
        fun _ _ ↦ Sigma.hom_ext _ _ fun i ↦ i.elim⟩
    infer_instance
  · intro A _ hA _ C c hc
    have := hA (fun a ↦ C (some a)) (fun a ↦ c (some a)) fun a ↦ hc (some a)
    have := hc none
    have hb := (proper_coproduct_two (c none) (Sigma.desc fun a ↦ c (some a))).2.2.2
    have : IsProper (coprod.desc (c none) (Sigma.desc fun a ↦ c (some a))) := hb
    have he : Sigma.desc c =
        (sigmaOptionIso C).hom ≫ coprod.desc (c none) (Sigma.desc fun a ↦ c (some a)) := by
      ext (_ | a) <;> simp
    rw [he]
    infer_instance

section Geometry

variable {D : FiniteFieldDatum.{u}} (T : Over (Spec (.of D.k)))
  [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
  {B : Type u} [Fintype B] (U : B → T.left.Opens) [∀ β, Fact (IsClopen (U β : Set T.left))]

/-- A separated finite-type `k`-scheme which is a finite disjoint union of open-and-closed
subschemes, each proper over `s`, is proper over `s`.
Source: "let `T` be a separated finite-type scheme over `s` which is a finite disjoint union
`T = ∐_{β∈B} β` of open-and-closed subschemes `j_β : β ↪ T`, each proper over `s`. Then `T`
is proper over `s`." (blueprint: lem-trf-integration-component-sum).

Proof (node step 1): `a_T` is separated and of finite type by hypothesis. After a base change
`s' → s` the presentation gives `T_{s'} = ∐_β β_{s'}`. For closed `Z ⊆ T_{s'}`, its image is
the finite union `⋃_β a_{β,s'}(Z ∩ β_{s'})`; each `Z ∩ β_{s'}` is closed in `β_{s'}` and its
image is closed since `a_β` is universally closed. Hence `a_T` is universally closed, so
proper (def-weil-proper-morphism). For `B = ∅`, `T = ∅` and the claim is trivial. -/
theorem isProper_of_clopen_cover
    (hdisj : Pairwise fun β γ ↦ Disjoint (U β) (U γ)) (hcover : ⨆ β, U β = ⊤)
    [∀ β, IsProper (clopenPiece T (U β)).hom] : IsProper T.hom := by
  let C : B → Scheme := fun β ↦ (U β).toScheme
  let j : ∀ β, C β ⟶ T.left := fun β ↦ (U β).ι
  have hcol : Nonempty (IsColimit (Cofan.mk T.left j)) := by
    apply nonempty_isColimit_cofanMk_of
    · simpa only [j, Scheme.Opens.opensRange_ι] using hcover
    · simpa only [j, Scheme.Opens.opensRange_ι] using hdisj
  let e : (∐ C) ≅ T.left :=
    @asIso _ _ _ _ (Sigma.desc j)
      ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk T.left j)).mp hcol)
  have hp : IsProper (Sigma.desc fun β ↦ j β ≫ T.hom) :=
    proper_sigma_desc C (fun β ↦ j β ≫ T.hom)
      (fun β ↦ inferInstanceAs (IsProper (clopenPiece T (U β)).hom))
  have he : e.hom ≫ T.hom = Sigma.desc (fun β ↦ j β ≫ T.hom) := by
    ext β
    simp [e]
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom, he]
  exact hp

end Geometry

variable (A : Type) [CommRing A] [Finite A]
  {D : FiniteFieldDatum.{u}} (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)

/-- **Integration splits over the open–closed components.** If `T` is a separated
finite-type `k`-scheme which is the finite disjoint union of the open-and-closed pieces
`β = clopenPiece T (U β)`, each proper over `s`, then (`T` being proper by
`isProper_of_clopen_cover`) for every section `τ : A_T → ω_{T,A}`
`∫_T τ = ∑_{β∈B} ∫_β (τ|_β)`, the restriction being `restrictSection` of def-trf-local-term.
For `B = ∅` both sides are `0`.
Source: "Then `∫_T τ = ∑_{β∈B} ∫_β(τ|_β)` ... for `B = ∅` both sides are `0`"
(blueprint: lem-trf-integration-component-sum).

Proof (node steps 2-7).
2. Write `P_β = Lj_β^*` and `J_β = Rj_{β*} = Rj_{β!}` (proper coincidence; open purity of
   prop-functor-package). The recollement adjunctions
   (prop-weil-open-closed-recollement-adjunctions) give `P_β ⊣ J_β ⊣ P_β`, with ordinary unit
   `s_{β,L} : L → J_β P_β L` and exceptional counit `r_{β,L} : J_β P_β L → L`; the open counit
   is the extension-by-zero counit, and the ordinary counit `P_β J_β → id` is inverse to the
   open unit. Via `dualizingComposition`, `P_β τ` is exactly `τ|_β` (`restrictSection`).
3. Put `Q_L = ⊕_β J_β P_β L`, `R_L = (r_{β,L})_β : Q_L → L`, `S_L = (s_{β,L})_β : L → Q_L`.
   Proper base change gives `P_γ J_β = 0` for `γ ≠ β` (empty fibre product) and
   `P_β J_β ≅ id`; so `P_γ R_L = P_γ r_{γ,L}` is invertible, and by finite clopen covering
   locality (lem-cbc-proetale-stalk-conservative (1)) `R_L` is an isomorphism.
4. The `(γ,β)` entry of `S_L R_L` is `s_{γ,L} r_{β,L}`; its `P_γ ⊣ J_γ` adjunct is zero off the
   diagonal (step 3) and is `P_γ(r_{γ,L})` = the ordinary counit on the diagonal (triangle
   identities). Hence `S_L R_L = 1`, so `S_L = R_L⁻¹`, `R_L S_L = 1`.
5. Naturality of counits at `L = A_T, ω_T` gives
   `τ = R_{ω_T} (⊕_β J_β(τ|_β)) S_{A_T} = ∑_β (j_β)_*(τ|_β)`, the Borel–Moore pushforward
   (def-trf-borel-moore-pushforward).
6. For proper `h : V → W` between proper schemes, `η_{ah} = Ra_*η_h ∘ η_a` and
   `ε_{ah} = ε_a ∘ Ra_!ε_h` (fix-prop-coherence, def-weil-pbc-composite-adjunction,
   thm-trf-dualizing-complex-composition), whence `∫_W h_*γ = ∫_V γ`.
7. By `A`-linearity of integration (lem-trf-integration-linear) and step 6 at each proper
   `j_β` (a clopen immersion is a closed immersion), `∫_T τ = ∑_β ∫_T (j_β)_*(τ|_β) =
   ∑_β ∫_β(τ|_β)`. For `B = ∅`, `T = ∅`, every module sheaf on `T` is zero, the integration
   composite factors through zero and its scalar is `0`, the empty sum. -/
theorem sectionIntegral_eq_sum_restrictSection
    (T : Over (Spec (.of D.k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom]
    {B : Type u} [Fintype B] (U : B → T.left.Opens) [∀ β, Fact (IsClopen (U β : Set T.left))]
    (hdisj : Pairwise fun β γ ↦ Disjoint (U β) (U γ)) (hcover : ⨆ β, U β = ⊤)
    [∀ β, IsProper (clopenPiece T (U β)).hom]
    (τ : 𝟙_ (Ambient A T.left) ⟶ dualizingComplex A D ell hell hA T) :
    haveI : IsProper T.hom := isProper_of_clopen_cover T U hdisj hcover
    sectionIntegral A ell hell hA T τ =
      ∑ β : B, sectionIntegral A ell hell hA (clopenPiece T (U β))
        (restrictSection A ell hell hA T (U β) τ) := by
  sorry

/-- The component sum at the blueprint coefficients `A = A_{E_coeff,n}`, with the integration
`traceFormulaIntegration` of def-trf-integration.
Source: "Fix the coefficient conventions, `A = A_{E,n}` ... `∫_T τ = ∑_{β∈B} ∫_β(τ|_β)`"
(blueprint: lem-trf-integration-component-sum).
Proof: `traceFormulaIntegration` at `A_{E,n}` unfolds to `sectionIntegral` with the primary
witness `coefficientExtensionRing_primary` (as in `localTermOfSection_coefficientExtensionRing`
of def-trf-local-term); apply `sectionIntegral_eq_sum_restrictSection`. -/
theorem traceFormulaIntegration_eq_sum_restrictSection
    (Ec : IntermediateField (Padic ell) (PadicAlgCl ell)) [FiniteDimensional (Padic ell) Ec]
    (n : ℕ) (hn : 1 ≤ n) [Finite (Padic.coefficientExtensionRing ell Ec n)]
    (T : Over (Spec (.of D.k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T.hom]
    {B : Type u} [Fintype B] (U : B → T.left.Opens) [∀ β, Fact (IsClopen (U β : Set T.left))]
    (hdisj : Pairwise fun β γ ↦ Disjoint (U β) (U γ)) (hcover : ⨆ β, U β = ⊤)
    [∀ β, IsProper (clopenPiece T (U β)).hom]
    (τ : 𝟙_ (Ambient (Padic.coefficientExtensionRing ell Ec n) T.left) ⟶
      dualizingComplex (Padic.coefficientExtensionRing ell Ec n) D ell hell
        (coefficientExtensionRing_primary ell Ec n hn) T) :
    haveI : IsProper T.hom := isProper_of_clopen_cover T U hdisj hcover
    traceFormulaIntegration D ell hell Ec n hn T τ =
      ∑ β : B, traceFormulaIntegration D ell hell Ec n hn (clopenPiece T (U β))
        (restrictSection (Padic.coefficientExtensionRing ell Ec n) ell hell
          (coefficientExtensionRing_primary ell Ec n hn) T (U β) τ) := by
  simpa only [traceFormulaIntegration] using
    sectionIntegral_eq_sum_restrictSection (Padic.coefficientExtensionRing ell Ec n)
      ell hell (coefficientExtensionRing_primary ell Ec n hn) T U hdisj hcover τ

section FixedScheme

variable {A ell hell hA} {X : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

end FixedScheme

end WeilConjectures.FiniteRingTrace
