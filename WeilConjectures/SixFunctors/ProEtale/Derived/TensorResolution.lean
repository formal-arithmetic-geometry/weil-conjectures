/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.SixFunctors.ProEtale.Derived.Tensor

/-!
# Resolution independence and functoriality of the pro-étale derived tensor product

The derived tensor product `- ⊗ᴸ -` of `D(X_proét)`
(`AlgebraicGeometry.ProEtale.derivedTensor`) is the left derived bifunctor of the tensor product
of complexes of pro-étale sheaves along the K-flat left derivability structure. This file
records the two properties of blueprint `lem-weil-derived-tensor-resolution-independent` and
`lem-weil-derived-tensor-functorial`:

* a quasi-isomorphism `P ⟶ P'` between K-flat complexes stays a quasi-isomorphism after
  tensoring with any complex (Stacks `064L`), so that `K₁ ⊗ᴸ K₂` may be computed as `P ⊗ K₂` for
  any K-flat resolution `P` of `K₁`;
* the derived tensor product is a functor in each variable, and the two ways of applying a pair
  of morphisms agree.

## Main statements

- `CategoryTheory.MorphismProperty.kFlat.whiskerRight_mem`: the general form of Stacks `064L`,
  for a morphism property with the two-out-of-three property.
- `AlgebraicGeometry.ProEtale.quasiIso_whiskerRight_of_kFlat`: Stacks `064L` for complexes of
  pro-étale sheaves.
- `AlgebraicGeometry.ProEtale.isIso_tensorLeftCounit_app_of_kFlat`: `Qh(P) ⊗ᴸ Qh(K₂) ≅ Qh(P ⊗ K₂)`
  for a K-flat `P`.
- `AlgebraicGeometry.ProEtale.derivedTensor_map_app_comp_map`: functoriality in both variables.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] [MonoidalCategory C] (W : MorphismProperty C)
  [W.HasTwoOutOfThreeProperty]

/-- Blueprint `lem-weil-derived-tensor-resolution-independent`, in general form (Stacks `064L`):
let `α : P ⟶ Q` be a morphism in `W` between `W`-K-flat objects, and let `L` admit a `W`-K-flat
resolution `w : R ⟶ L`. Then `α ▷ L` is in `W`. Indeed in the commutative square
```
  P ⊗ R --α ▷ R--> Q ⊗ R
    |                |
  P ◁ w            Q ◁ w
    v                v
  P ⊗ L --α ▷ L--> Q ⊗ L
```
the top arrow is in `W` because `R` is K-flat, the vertical arrows because `P` and `Q` are, and
`α ▷ L` follows by two-out-of-three. -/
lemma kFlat.whiskerRight_mem {P Q : C} (α : P ⟶ Q) (hα : W α) (hP : W.kFlat P)
    (hQ : W.kFlat Q) {L R : C} (w : R ⟶ L) (hw : W w) (hR : W.kFlat R) : W (α ▷ L) := by
  have h₁ : W (α ▷ R) := hR.2 α hα
  have h₂ : W (P ◁ w) := hP.1 w hw
  have h₃ : W (Q ◁ w) := hQ.1 w hw
  refine W.of_precomp _ _ h₂ ?_
  rw [whisker_exchange]
  exact W.comp_mem _ _ h₁ h₃

end CategoryTheory.MorphismProperty

namespace HomotopyCategory

variable {C : Type u} [Category.{u'} C] [Abelian C] [IsGrothendieckAbelian.{u'} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

/-- Blueprint `lem-weil-derived-tensor-resolution-independent` (Stacks `064L`), in the homotopy
category of a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions: a quasi-isomorphism `α : P ⟶ P'` between K-flat complexes stays a
quasi-isomorphism after tensoring with any complex `K₂`. -/
theorem quasiIso_whiskerRight_of_kFlat {P P' : HomotopyCategory C (ComplexShape.up ℤ)}
    (α : P ⟶ P') (hα : HomotopyCategory.quasiIso _ _ α)
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P)
    (hP' : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P')
    (K₂ : HomotopyCategory C (ComplexShape.up ℤ)) :
    HomotopyCategory.quasiIso _ _ (α ▷ K₂) := by
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  obtain R : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).localizerMorphismKFlat.LeftResolution
    K₂ := Classical.arbitrary _
  exact MorphismProperty.kFlat.whiskerRight_mem _ α hα hP hP' R.w R.hw R.X₁.property

end HomotopyCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- Blueprint `lem-weil-derived-tensor-resolution-independent`: Resolution independence of the
derived tensor product.

For complexes of `A`-valued sheaves on the small pro-étale site of `X`, a quasi-isomorphism
`α : P ⟶ P'` between K-flat complexes induces a quasi-isomorphism `P ⊗ K₂ ⟶ P' ⊗ K₂` for every
complex `K₂` (Stacks `064L`). In particular, for two K-flat resolutions `P ⟶ K₁` and `P' ⟶ K₁`,
any lift `P ⟶ P'` of the identity of `K₁` in the homotopy category is a quasi-isomorphism, and so
is the induced map `P ⊗ K₂ ⟶ P' ⊗ K₂`; the object `P ⊗ K₂` computing `K₁ ⊗ᴸ K₂`
(`AlgebraicGeometry.ProEtale.isIso_μ_Qh_of_kFlat`) does not depend on the resolution. -/
theorem quasiIso_whiskerRight_of_kFlat
    {P P' : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)}
    (α : P ⟶ P') (hα : HomotopyCategory.quasiIso _ _ α)
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P)
    (hP' : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P')
    (K₂ : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)) :
    HomotopyCategory.quasiIso _ _ (α ▷ K₂) :=
  HomotopyCategory.quasiIso_whiskerRight_of_kFlat α hα hP hP' K₂

/-- Blueprint `lem-weil-derived-tensor-resolution-independent`: for a K-flat complex `P` of
pro-étale sheaves, the comparison `Qh(P) ⊗ᴸ Qh(K₂) ⟶ Qh(P ⊗ K₂)` is an isomorphism, so that the
derived tensor product `K₁ ⊗ᴸ K₂` is computed by `P ⊗ K₂` for any K-flat resolution `P` of
`K₁`. -/
theorem isIso_μ_Qh_of_kFlat
    (P : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ))
    (hP : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).kFlat P)
    (K₂ : HomotopyCategory (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh P K₂) :=
  DerivedCategory.isIso_μ_Qh_of_kFlat P K₂ hP

/-- Blueprint `lem-weil-derived-tensor-functorial`: Functoriality of the derived tensor product.

For morphisms `φ : K₁ ⟶ K₁'` and `ψ : K₂ ⟶ K₂'` in `D(X_proét)`, applying the derived tensor
product first in the first and then in the second variable agrees with the other order; the
common value is the induced morphism `φ ⊗ ψ : K₁ ⊗ᴸ K₂ ⟶ K₁' ⊗ᴸ K₂'`. The derived tensor product
being a bifunctor `D(X_proét) ⥤ D(X_proét) ⥤ D(X_proét)`, the assignment carries identities to
identities and composites to composites in each variable (`Functor.map_id`, `Functor.map_comp`,
`MonoidalCategory.tensor_comp`). -/
theorem derivedTensor_map_app_comp_map
    {K₁ K₁' K₂ K₂' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (φ : K₁ ⟶ K₁')
    (ψ : K₂ ⟶ K₂') :
    ((derivedTensor A X).map φ).app K₂ ≫ ((derivedTensor A X).obj K₁').map ψ = φ ⊗ₘ ψ ∧
      ((derivedTensor A X).obj K₁).map ψ ≫ ((derivedTensor A X).map φ).app K₂' = φ ⊗ₘ ψ :=
  ⟨(tensorHom_def φ ψ).symm, (tensorHom_def' φ ψ).symm⟩

end AlgebraicGeometry.ProEtale
