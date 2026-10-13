/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOverField
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward

/-!
# The trace formula for schemes finite over the base

Step 1 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace formula
for a Weil complex on a scheme `X` finite over `s = Spec Ω`, `Ω` algebraically closed. If the
Frobenius has no fixed point, both sides vanish: the Lefschetz–Verdier formula
(`GeometricOperations.trace_globalOperator_eq_sum_localTerm`) on the proper `X` is a sum over the
components of the empty fixed scheme. Otherwise a fixed section `x : s ⟶ X` is a closed immersion
with open complement stable under the Frobenius, the trace formula over the point `x` is
`WeilComplex.traceFormula_of_eq_id`, and induction on the number of points of `X` with the
additivity `WeilComplex.traceFormula_of_isCompl` concludes.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_forall_base_ne`: no fixed points.
- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_one_of_isFinite`: degree one, for a
  Frobenius bijective on points.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale.WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {X : Scheme.{u}}
/-- Over an algebraically closed field `Ω`, every point `y` of a scheme finite over `Spec Ω` is
the image of a section `x` of the structure morphism, and every section whose point is `y` is `x`:
the residue field `κ(y)` is finite over `Ω`, hence `Ω` itself, and a section through `y` factors
through the closed point `Spec κ(y) ⟶ X`. -/
lemma _root_.AlgebraicGeometry.exists_section_base_eq_of_isFinite {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] {X : Scheme.{u}} (aX : X ⟶ Spec (.of Ω)) [IsFinite aX] (y : X) :
    ∃ x : Spec (.of Ω) ⟶ X, x ≫ aX = 𝟙 _ ∧ (∀ p, x.base p = y) ∧
      ∀ x' : Spec (.of Ω) ⟶ X, x' ≫ aX = 𝟙 _ → (∀ p, x'.base p = y) → x' = x := by
  have := (finite_and_discreteTopology_of_isFinite aX).2
  have := isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete {y})
  have : IsIso (X.fromSpecResidueField y ≫ aX) := by
    rw [← Spec.map_preimage (X.fromSpecResidueField y ≫ aX)]
    have hfin : (Spec.preimage (X.fromSpecResidueField y ≫ aX)).hom.Finite := by
      rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
      infer_instance
    have : IsIso (Spec.preimage (X.fromSpecResidueField y ≫ aX)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (IsAlgClosed.ringHom_bijective_of_isIntegral _ hfin.to_isIntegral)
    infer_instance
  refine ⟨inv (X.fromSpecResidueField y ≫ aX) ≫ X.fromSpecResidueField y, by simp,
    fun p ↦ X.fromSpecResidueField_apply y _, fun x' hx' hy ↦ ?_⟩
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  obtain ⟨l, rfl⟩ := IsClosedImmersion.exists_lift_of_range_subset (X.fromSpecResidueField y) x'
    (range_subset_of_base_mem x' p (by rw [Scheme.range_fromSpecResidueField]; exact hy p))
  obtain rfl : l = inv (X.fromSpecResidueField y ≫ aX) := by
    rw [← cancel_mono (X.fromSpecResidueField y ≫ aX), IsIso.inv_hom_id, ← Category.assoc, hx']
  rfl

/-- The iterates of the Frobenius of a Weil complex on a proper scheme are proper. -/
instance isProper_frobeniusIterate {s : Scheme.{u}} {aX : X ⟶ s} [IsProper aX]
    (W : WeilComplex (A := A) aX) (m : ℕ) : IsProper (W.frobeniusIterate m) :=
  IsProper.comp_iff.mp (by rw [W.frobeniusIterate_comp]; infer_instance)

/-- The ordinary-pullback leg of a graph correspondence `(id, g)` is proper when `g` is. -/
instance _root_.AlgebraicGeometry.ProEtale.Correspondence.isProper_ofGraph_snd {s : Scheme.{u}}
    (G : GeometricOperations A s) (aX : X ⟶ s) [IsGeometric aX]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : G.ctf X K) (g : X ⟶ X)
    (hg : g ≫ aX = aX) (w : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K) [IsProper g] :
    IsProper (Correspondence.ofGraph G aX K hK g hg w).snd :=
  ‹IsProper g›

/-- If `Φ_m` has no fixed point on a scheme `X` proper over `s = Spec Ω`, both sides of the trace
formula vanish: the Lefschetz–Verdier formula is a sum over the empty set of components of the
fixed scheme, and there are no fixed sections. -/
theorem traceFormula_of_forall_base_ne {Ω : Type u} [Field Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)} [IsGeometric aX]
    [HasCompactification aX] [IsProper aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj)
    (m : ℕ) [IsProper (W.graph G hW m).snd] (h : ∀ y : X, (W.frobeniusIterate m).base y ≠ y) :
    W.TraceFormula G hW m := by
  intro _ _ _
  have hfix : IsEmpty (W.graph G hW m).fix := ⟨fun z ↦ h ((W.graph G hW m).fixι.base z) (by
    have := congrArg (fun f ↦ f.base z) (W.graph G hW m).fixι_snd
    exact this)⟩
  have : IsEmpty {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x} := by
    obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    refine ⟨fun x ↦ h (x.1.base p) ?_⟩
    rw [← Scheme.Hom.comp_apply, x.2.2]
  have : IsProper (W.graph G hW m).fixStr :=
    inferInstanceAs (IsProper ((W.graph G hW m).fixι ≫ aX))
  rw [GeometricOperations.trace_globalOperator_eq_sum_localTerm G hW (W.graph G hW m)
    (ι := PEmpty) (B := fun _ ↦ (W.graph G hW m).fix) (fun _ ↦ 𝟙 _) (fun i ↦ i.elim)
    (fun i ↦ i.elim) (by rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff]; exact hfix),
    Fintype.sum_empty, Fintype.sum_empty]

/-- The trace formula in degree one for a Weil complex on a scheme `X` finite over `Spec Ω`,
`Ω` algebraically closed, whose Frobenius is bijective on points and which has at most `n`
points, by induction on `n`. -/
theorem traceFormula_one_of_isFinite_of_card_le {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) (n : ℕ) {X : Scheme.{u}}
    {aX : X ⟶ Spec (.of Ω)} [IsFinite aX] [HasCompactification aX] (W : WeilComplex (A := A) aX)
    (hW : G.ctf X W.obj) (hbij : Function.Bijective W.frobenius.base)
    [IsProper (W.graph G hW 1).snd] (hn : Nat.card X ≤ n) :
    W.TraceFormula G hW 1 := by
  induction n generalizing X with
  | zero =>
    have := (finite_and_discreteTopology_of_isFinite aX).1
    intro _ _ _
    refine traceFormula_of_forall_base_ne G W hW 1 fun y _ ↦ ?_
    have : Nonempty X := ⟨y⟩
    exact absurd (Nat.le_zero.mp hn) Nat.card_pos.ne'
  | succ n ih =>
  have hfin := (finite_and_discreteTopology_of_isFinite aX).1
  have := (finite_and_discreteTopology_of_isFinite aX).2
  intro _ _ _
  by_cases hfix : ∀ y : X, (W.frobeniusIterate 1).base y ≠ y
  · exact traceFormula_of_forall_base_ne G W hW 1 hfix
  push Not at hfix
  obtain ⟨y, hy⟩ := hfix
  rw [frobeniusIterate_one] at hy
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  obtain ⟨x, hx, hxy, hxuniq⟩ := exists_section_base_eq_of_isFinite aX y
  have hxΦ : x ≫ W.frobenius = x := hxuniq _ (by rw [Category.assoc, W.frobenius_comp, hx])
    fun p ↦ by rw [Scheme.Hom.comp_apply, hxy, hy]
  have : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id aX x hx
  let U : X.Opens := ⟨{y}ᶜ, isOpen_discrete _⟩
  have hmem (u : U.toScheme) : U.ι.base u ≠ y := u.2
  have hUΦ : Set.range (U.ι ≫ W.frobeniusIterate 1).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι, frobeniusIterate_one, Scheme.Hom.comp_apply]
    exact fun h ↦ hmem u (hbij.1 (h.trans hy.symm))
  let frobU : U.toScheme ⟶ U := IsOpenImmersion.lift U.ι (U.ι ≫ W.frobeniusIterate 1) hUΦ
  have sqU : CommSq frobU U.ι U.ι (W.frobeniusIterate 1) := ⟨IsOpenImmersion.lift_fac _ _ _⟩
  have sqZ : CommSq (𝟙 _) x x (W.frobeniusIterate 1) :=
    ⟨by rw [frobeniusIterate_one, hxΦ, Category.id_comp]⟩
  have hcomm (u : U.toScheme) : U.ι.base (frobU.base u) = W.frobenius.base (U.ι.base u) := by
    rw [← Scheme.Hom.comp_apply, sqU.w, Scheme.Hom.comp_apply, frobeniusIterate_one]
  have hinj : Function.Injective U.ι.base := U.ι.isOpenEmbedding.injective
  have hbijU : Function.Bijective frobU.base := by
    refine ⟨fun a b hab ↦ hinj (hbij.1 ?_), fun u ↦ ?_⟩
    · rw [← hcomm, ← hcomm, hab]
    obtain ⟨v, hv⟩ := hbij.2 (U.ι.base u)
    have hvU : v ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro rfl
      exact hmem u (hv.symm.trans hy)
    obtain ⟨w, rfl⟩ := hvU
    exact ⟨w, hinj (by rw [hcomm, hv])⟩
  have hrange : Set.range x.base = {y} := by
    refine Set.ext fun z ↦ ⟨?_, ?_⟩
    · rintro ⟨q, rfl⟩
      exact hxy q
    · rintro rfl
      exact ⟨p, hxy p⟩
  have hcompl : IsCompl (Set.range U.ι.base) (Set.range x.base) := by
    rw [Scheme.Opens.range_ι, hrange]
    exact isCompl_compl.symm
  have : IsClosedImmersion U.ι := .of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]
    exact isClosed_discrete _)
  have hcard : Nat.card U.toScheme < Nat.card X :=
    Finite.card_subtype_lt (p := (· ∈ (U : Set X))) (x := y) fun h ↦ h rfl
  have : HasRightDual ((rightDerivedLowerShriek A (U.ι ≫ aX)).obj
      (W.upperStarPull U.ι rfl frobU sqU).obj) :=
    (GeometricOperations.nonempty_hasRightDual_rightDerivedLowerShriek G (U.ι ≫ aX)
      (G.ctf_upperStar U.ι (.mk (aX := U.ι ≫ aX) rfl) hW)).some
  have : HasRightDual ((rightDerivedLowerShriek A (𝟙 _)).obj
      (W.upperStarPull x hx (𝟙 _) sqZ).obj) :=
    (GeometricOperations.nonempty_hasRightDual_rightDerivedLowerShriek G (𝟙 _)
      (G.ctf_upperStar x (.mk hx) hW)).some
  refine traceFormula_of_isCompl G (aU := U.ι ≫ aX) (aZ := 𝟙 _) U.ι x rfl hx hcompl W hW frobU
    (𝟙 _) sqU sqZ 1 ?_ ?_
  · intro _ _ _
    exact ih (aX := U.ι ≫ aX) _ _ hbijU (by omega)
  · intro _ _ _
    exact traceFormula_of_eq_id G _ _ 1

/-- The trace formula in degree one for a Weil complex on a scheme `X` finite over `Spec Ω`,
`Ω` algebraically closed, whose Frobenius is bijective on points, by induction on the number of
points of `X`. -/
theorem traceFormula_one_of_isFinite {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)} [IsFinite aX]
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj)
    (hbij : Function.Bijective W.frobenius.base) [IsProper (W.graph G hW 1).snd] :
    W.TraceFormula G hW 1 :=
  traceFormula_one_of_isFinite_of_card_le G _ W hW hbij le_rfl

end AlgebraicGeometry.ProEtale.WeilComplex
