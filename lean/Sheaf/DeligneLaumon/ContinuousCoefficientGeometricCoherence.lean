/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData

/-! # Geometric coherence of normalized coefficient charts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.StratifiedContinuousLattices

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0} X.ProEt

/-- Locally closed restriction and finite field change for fixed normalized charts.
Source: Bhatt--Scholze 6.8.2 and 6.8.15; Stacks 03EL.
(blueprint: lem-zl-continuous-coefficient-geometric-coherence). -/
structure CoefficientGeometry (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (c : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], CoefficientFamily l E) where
  restriction : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : PerAdic.Base D.k) (Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f],
    Restriction l E f ((c E).atScheme X.scheme) ((c E).atScheme Y.scheme)
  composition : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X Y Z : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme)
    [IsImmersion f] [IsImmersion g],
    (restriction E X Z (g ≫ f)).integral.hom =
      (proEtaleRingInverseImageComp g f).hom.app
        (pbcAdicCompletion X.scheme (pbcIntegralDatum l E)) ≫
      (adicTowerInverseImage g).map (restriction E X Y f).integral.hom ≫
        (restriction E Y Z g).integral.hom ∧
    (restriction E X Z (g ≫ f)).rational.hom =
      (proEtaleRingInverseImageComp g f).hom.app (rationalCoefficientSheaf l X.scheme E) ≫
      (adicTowerInverseImage g).map (restriction E X Y f).rational.hom ≫
        (restriction E Y Z g).rational.hom
  fieldChange : ∀ (E E' : Type u) [NormedField E] [NormedField E']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    (i : E →ₐ[ℚ_[l]] E') (X : PerAdic.Base D.k),
    FieldChange l E E' i X.scheme ((c E).atScheme X.scheme)
      ((c E').atScheme X.scheme)
  field_restriction : ∀ (E E' : Type u) [NormedField E] [NormedField E']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    (i : E →ₐ[ℚ_[l]] E') (X Y : PerAdic.Base D.k)
    (f : Y.scheme ⟶ X.scheme) [IsImmersion f],
    (adicTowerInverseImage f).map (fieldChange E E' i X).integral ≫
      (restriction E' X Y f).integral.hom =
        (restriction E X Y f).integral.hom ≫ (fieldChange E E' i Y).integral ∧
    (adicTowerInverseImage f).map (fieldChange E E' i X).rational ≫
      (restriction E' X Y f).rational.hom =
        (restriction E X Y f).rational.hom ≫ (fieldChange E E' i Y).rational
  field_composition : ∀ (E E' E'' : Type u)
    [NormedField E] [NormedField E'] [NormedField E'']
    [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] E'] [NormedAlgebra ℚ_[l] E'']
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E''] (i : E →ₐ[ℚ_[l]] E') (j : E' →ₐ[ℚ_[l]] E'')
    (X : PerAdic.Base D.k),
    (fieldChange E E'' (j.comp i) X).integral =
      (fieldChange E E' i X).integral ≫ (fieldChange E' E'' j X).integral ∧
    (fieldChange E E'' (j.comp i) X).rational =
      (fieldChange E E' i X).rational ≫ (fieldChange E' E'' j X).rational

/-- Normalized coefficient charts have coherent locally closed restrictions and field changes.

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; step 3 of
lem-zl-continuous-constructible-stratified-lattices.
(blueprint: lem-zl-continuous-coefficient-geometric-coherence).

Proof: finite type over a field makes every base noetherian and quasi-compact.
The continuous immersion restriction isomorphisms therefore apply. Conjugate their
integral maps by the normalized integral charts and their rational maps by the
normalized rational charts. Naturality of the integral inclusion gives square.
The quotient projection normalization gives integral_normalized; pointwise evaluation
gives rational_normalized. The inverse-image composition isomorphism and continuous
coefficient pullback composition show that both restrictions of a composite are the
displayed composites. For a finite coefficient embedding, its restriction to the
valuation subring is continuous and maps each integer to its stated field image.
Conjugating the induced maps on continuous function sheaves defines integral and
rational field change. For every compatible pair of ideal powers, reduction sends
the class of a to the class of its image; hence quotient_powers holds, with no
unramifiedness assumption. Equality after all quotient projections and equality on
rational section values give field_restriction and field_composition. The same
pointwise calculation gives the scalar square. Empty bases impose no extra choice. -/
theorem continuous_coefficient_geometric_coherence (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime]
    (c : ∀ (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], CoefficientFamily l E) :
    Nonempty (CoefficientGeometry D l c) := by sorry

end WeilConjectures.StratifiedContinuousLattices
