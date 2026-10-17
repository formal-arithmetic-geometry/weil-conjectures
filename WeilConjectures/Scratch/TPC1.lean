module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ConstructibleReduction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Linear

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {A : Type (u + 1)} [CommRing A] {I : Ideal A}

set_option hygiene false in
local notation "𝐃(" T ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

lemma vGeneric {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    (hI : I = Ideal.span {ϖ})
    (Φ : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Linear A] (K : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (n : ℕ) : Nonempty (Φ.obj
    ((_root_.DerivedCategory.derivedCompletionDiagram J I K).obj (op n)) ≅
      (_root_.DerivedCategory.derivedCompletionDiagram J I (Φ.obj K)).obj (op n)) :=
  _root_.DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj hϖ hI Φ K n

lemma vProEt {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    (hI : I = Ideal.span {ϖ}) {S T : Scheme.{u}} (Φ : 𝐃(S) ⥤ 𝐃(T)) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Φ.Linear A] (K : 𝐃(S)) (n : ℕ) : Nonempty (Φ.obj
    ((_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology S) I K).obj (op n)) ≅
      (_root_.DerivedCategory.derivedCompletionDiagram (Scheme.ProEt.topology T) I
        (Φ.obj K)).obj (op n)) :=
  _root_.DerivedCategory.nonempty_iso_map_derivedCompletionDiagram_obj hϖ hI Φ K n

end AlgebraicGeometry.ProEtale
