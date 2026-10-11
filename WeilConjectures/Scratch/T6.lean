module

public import WeilConjectures.Scratch.T5

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- At a closed point outside the image of `U`, the geometric stalk of `j₀! F` vanishes: the
pullback of `j̄_! F` to a geometric point missing the range of `j̄` is zero. -/
theorem subsingleton_stalk_extensionByZero (F : WeilSheaf k₀ l U) (x : X.finitePoints)
    (hx : x.1 ∉ Set.range j.base) :
    Subsingleton (((extensionByZero j).obj F).stalk x).carrier := by
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  have hdisj : Set.range (j̄).base ∩ Set.range s.base = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun p ⟨⟨u, hu⟩, ⟨t, ht⟩⟩ ↦ hx ⟨_, ?_⟩
    have h₁ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x
    have h₂ := congrArg (fun g : _ ⟶ _ ↦ g.base u)
      (Scheme.Hom.geometricFiberMap_comp_geometricFiberProj j
        (comp_over j (Spec (CommRingCat.of k₀))))
    have ht' : t = IsLocalRing.closedPoint (AlgebraicClosure k₀) := Subsingleton.elim _ _
    subst ht'
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h₁ h₂
    rw [← h₁, ← ht, ← hu, h₂]
  have hz := ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek l (j̄) s hdisj
    F.obj.carrier
  have hz' : IsZero ((WeilCoefficients.toModuleCat l).obj
      (((extensionByZero j).obj F).stalkObj s)) :=
    (WeilCoefficients.toModuleCat l).map_isZero ((Sheaf.Γ _ _).map_isZero
      ((ProEtale.AdicSheaf.forget _).map_isZero hz))
  exact ModuleCat.subsingleton_of_isZero hz'

/-- The eigenvalues of the local Frobenius of `j₀! F` at a closed point `x` are those of `F` at
the corresponding point of `U`, and there are none if `x` lies outside `U`. -/
theorem exists_hasEigenvalue_of_hasEigenvalue_stalk_extensionByZero (F : WeilSheaf k₀ l U)
    (x : X.finitePoints) {α : PadicAlgCl l}
    (hα : (((extensionByZero j).obj F).stalk x).frobeniusEnd.HasEigenvalue α) :
    ∃ z : U.finitePoints, j.base z.1 = x.1 ∧ (F.stalk z).frobeniusEnd.HasEigenvalue α ∧
      (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 =
        (U ↘ Spec (CommRingCat.of k₀)).residueCard z.1 := by
  by_cases hx : x.1 ∈ Set.range j.base
  · obtain ⟨z, hz⟩ := hx
    have hzU : z ∈ U.finitePoints := by
      have : Finite (X.residueField x.1) := x.2
      rw [← hz] at this
      exact Finite.of_equiv _ (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv.toEquiv
    obtain rfl : x = ⟨j.base (⟨z, hzU⟩ : U.finitePoints).1,
        Scheme.Hom.map_mem_finitePoints j hzU⟩ := Subtype.ext hz.symm
    refine ⟨⟨z, hzU⟩, rfl, ?_, ?_⟩
    · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
        charpoly_frobeniusEnd_stalk_extensionByZero,
        ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
      exact hα
    · rw [Scheme.Hom.residueCard, Scheme.Hom.residueCard,
        degreeOver_base_eq (k₀ := k₀) j ⟨z, hzU⟩]
  · have := subsingleton_stalk_extensionByZero j F x hx
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    exact absurd (Subsingleton.elim v 0) hv.2

variable {ι : PadicAlgCl l →+* ℂ} {w : ℝ} {F : WeilSheaf k₀ l U}

/-- Extension by zero along a quasi-compact open immersion preserves punctual purity: at a
closed point of `U` the geometric stalk of `j₀!F` is that of `F`, with the same local Frobenius
and the same residue field, and at a closed point outside `U` it vanishes. -/
theorem IsPunctuallyPureOfWeight.extensionByZero' (hF : F.IsPunctuallyPureOfWeight ι w) :
    ((WeilSheaf.extensionByZero j).obj F).IsPunctuallyPureOfWeight ι w := by
  intro x α hα
  obtain ⟨z, -, hz, hq⟩ := exists_hasEigenvalue_of_hasEigenvalue_stalk_extensionByZero j F x hα
  rw [hq]
  exact hF z α hz

/-- Extension by zero along a quasi-compact open immersion preserves upper weight bounds: at a
closed point of `U` the geometric stalk of `j₀!F` is that of `F`, with the same local Frobenius
and the same residue field, and at a closed point outside `U` it vanishes. -/
theorem HasWeightsAtMost.extensionByZero' (hF : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.extensionByZero j).obj F).HasWeightsAtMost ι w := by
  intro x α hα
  obtain ⟨z, -, hz, hq⟩ := exists_hasEigenvalue_of_hasEigenvalue_stalk_extensionByZero j F x hα
  rw [hq]
  exact hF z α hz

end WeilSheaf

end AlgebraicGeometry
