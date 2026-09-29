/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal

/-!
# The derived category of a monoidal closed Grothendieck abelian category is monoidal closed

Let `C` be a Grothendieck abelian category which is monoidal closed, and whose monoidal
structure is compatible with the additive structure in the way that is needed in order to
tensor cochain complexes (`MonoidalPreadditive C` and the `GradedObject` hypotheses below,
which are exactly the ones under which `DerivedCategory C` is monoidal, see
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`). This file states that
the derived category `D(C)` is then again monoidal closed, the monoidal structure being the
derived tensor product `- ⊗^L -`.

Since `MonoidalClosed` only asks for a right adjoint of `X ⊗^L -` for every object `X` of
`D(C)`, no binary `RHom` bifunctor has to be constructed by hand: the bifunctoriality of the
internal hom is produced by the closed structure itself. The proof of the instance below is
therefore organized in the following four steps, of which steps 2–4 are still to be
formalized.

1. **Closedness at the homotopy level** (done in
   `WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom`). For cochain complexes
   `P`, `Y` in `C`, the internal hom complex `CochainComplex.internalHomObj P Y` has
   `(iHom P Y)ⁿ = ∏_{p + n = q} iHom (P.X p) (Y.X q)`, with differential
   `(-1)ᵖ • (f ≫ d_Y - d_P ≫ f)` on the factor indexed by `(p, q)` (the products exist since
   `C` is Grothendieck abelian). The tensor-hom bijection `(P ⊗ X ⟶ Y) ≃ (X ⟶ iHom P Y)` is
   plain currying on morphisms of complexes, and currying with the sign `(-1) ^ (p * n)` on
   cochains of degree `n` commutes with `δ`, so it is compatible with homotopies. This gives
   `HomotopyCategory.tensorHomAdjunction P : tensorLeft P ⊣ H_P` on
   `K(C) := HomotopyCategory C (ComplexShape.up ℤ)`, with `H_P = HomotopyCategory.internalHom P`.
2. **Fixing one variable of the binary derived tensor.** Deduce from the fact that the derived
   tensor product is the binary left derived functor of the tensor product on `K(C)` (the
   `IsLeftDerivedFunctor₂` instance in
   `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`) that `Qh.obj P ⊗^L -`
   is the (unary) left derived functor of `P ⊗ -`.
3. **Deriving the adjunction.** Right derive `H_P` using K-injective resolutions, which exist
   since `C` is Grothendieck abelian
   (`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`), and apply
   `CategoryTheory.Adjunction.derived` to `P ⊗ - ⊣ H_P` to obtain `Qh.obj P ⊗^L - ⊣ R H_P`,
   i.e. `Closed (Qh.obj P)` for every `P` in `K(C)`. Only the individual right derived
   functors are needed here, not their functoriality in `P`.
4. **Transport to an arbitrary object.** Every `X : DerivedCategory C` is isomorphic to
   `Qh.obj P` for some `P` (essential surjectivity of the localization functor), and
   closedness transfers along an isomorphism of objects, since an isomorphism `Qh.obj P ≅ X`
   induces a natural isomorphism `Qh.obj P ⊗^L - ≅ X ⊗^L -`, along which the adjunction of
   step 3 can be transported (`CategoryTheory.Adjunction.ofNatIsoLeft`).

Once the instance is available, its internal hom is *the* derived internal hom; identifying it
with the concrete hom-complex-of-a-K-injective-replacement model is further work, which is what
an `RHom` API would be about.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The derived category of a monoidal closed Grothendieck abelian category is monoidal
closed for the derived tensor product: for every `X : DerivedCategory C`, the functor
`X ⊗^L -` admits a right adjoint. -/
noncomputable instance monoidalClosed : MonoidalClosed (DerivedCategory C) := sorry

end DerivedCategory
