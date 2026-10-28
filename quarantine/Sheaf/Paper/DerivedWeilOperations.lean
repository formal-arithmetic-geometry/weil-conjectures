module

public import WeilConjectures.WeilSheaf.VerdierDual
public import Sheaf.Paper.NativeWeilClosedForgetful
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.DerivedWeilTensorOperations

/-! # Operations on the native derived Weil category

Source: main-20261015, fix-cor-verdier-exchange.proof.md, steps 1--2;
DerivedHom.lean and VerdierDual.lean in the live native realization
(blueprint: def-sf-derived-weil-category-and-operations).

The ordinary tensor and internal Hom are the existing relative module-sheaf
constructions with diagonal and conjugation actions. The total tensor below
orders the left degree first. Derived Hom is exactly ProEtaleWeilSheaf.derivedHom,
including its product-total sign convention. The dualizing object is exactly
WeilComplex.dualizingComplex. The final restriction takes preservation explicitly.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]

/-- The ambient contravariant derived internal Hom into the existing dualizing
complex. HasUpperShriek is explicitly conditional, as is dualizingComplex itself.
Source: VerdierDual.lean, dualizingComplex; DerivedHom.lean, derivedHom
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def ambientVerdierDual :
    (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ ⥤
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
  ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj

/-- Restrict ambient duality exactly when it preserves bounded constructible
objects. Existence of the right adjoint and this preservation are not asserted.
Source: VerdierDual.lean, verdierDual, with its preservation proof supplied explicitly
(blueprint: def-sf-derived-weil-category-and-operations). -/
noncomputable def verdierDualOfPreserves
    (h : ∀ K : WeilComplex k₀ l X,
      objectProperty k₀ l X ((ambientVerdierDual k₀ l X).obj (op K.obj))) :
    (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _ ((ObjectProperty.ι _).op ⋙ ambientVerdierDual k₀ l X)
    (fun K ↦ h K.unop)

end AlgebraicGeometry.WeilComplex
