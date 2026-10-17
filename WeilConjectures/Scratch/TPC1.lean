module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionTower
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Amplification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleTower
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsConstructible

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A)

set_option hygiene false in
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

def CommutesWithReductions' {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T)) : Prop :=
  ∀ (K : 𝐃(S)) (n : ℕ), Nonempty (Φ.obj
    ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology S) I K).obj (op n)) ≅
      (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I
        (Φ.obj K)).obj (op n))

variable {I} in
lemma commutesWithReductions_of_linear' {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    (hI : I = Ideal.span {ϖ}) {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T)) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Linear A] : CommutesWithReductions' I Φ := by
  intro K n
  have := _root_.DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj hϖ hI Φ K n
  exact this

#check @_root_.DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj
