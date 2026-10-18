/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q147
-/
module

public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# Derived self-tensor multiplication for a flat surjection

Source: Stacks Project, Cotangent Complex, Tag 08R2, proof of cases (1)--(2), and
More on Algebra, Section 06Y5 and Tag 06Y6
(blueprint: lem-trf-flat-epimorphism-derived-self-tensor).

The derived functor and its comparison are those supplied by the recorded
`exists_derivedTensor_second_factor_functor`. The multiplication is its comparison
followed by ordinary multiplication on the degree-zero total complex. Its target
is in `D(B)`, with the `B`-action through the second factor of `B ⊗_A B`.
-/

@[expose] public section

set_option autoImplicit false

universe u wA wB

open CategoryTheory MonoidalCategory

namespace DerivedCategory

/-- Canonical multiplication `B ⊗ᴸ_A B → B[0]`, defined for any commutative ring map.
Source: Stacks Project, Section 06Y5 preceding Tag 06Y6, and Tag 08R2
(blueprint: lem-trf-flat-epimorphism-derived-self-tensor).

Use the comparison of the recorded left-derived tensor functor at the complex
`B[0]` over `A`. The canonical single-complex tensor isomorphism and the single/map
isomorphism identify its underived target with the single complex on
`B ⊗_B (B ⊗_A B)`. The left unitor removes the outer tensor unit, and the ordinary
extension/restriction counit sends `c ⊗ b` to `cb`. Thus the resulting map is the
canonical multiplication, without any choice of an arbitrary morphism or resolution. -/
noncomputable def derivedSelfTensorMultiplication
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)] (f : A →+* B) :
    ((Classical.choose (exists_derivedTensor_second_factor_functor f).2).obj
      ((HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj
        (ModuleCat.of B B))).obj
      (Q.obj ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))) ⟶
    Q.obj ((HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj
      (ModuleCat.of B B)) :=
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  let N := (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).obj
    (ModuleCat.of B B)
  let E := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj M
  let ε := Classical.choose
    (Classical.choose_spec (exists_derivedTensor_second_factor_functor f).2)
  (ε N).app E ≫ Q.map
    ((CochainComplex.mapBifunctorSingle₁Iso (ModuleCat.mixedTensor f).flip M N).hom ≫
      (HomologicalComplex.singleMapHomologicalComplex
        ((ModuleCat.mixedTensor f).flip.obj M) (.up ℤ) 0).hom.app (ModuleCat.of B B) ≫
      (HomologicalComplex.single (ModuleCat.{u} B) (.up ℤ) 0).map
        ((λ_ ((ModuleCat.extendScalars f).obj M)).hom ≫
          (ModuleCat.extendRestrictScalarsAdj f).counit.app (ModuleCat.of B B)))

/-- A flat surjection has invertible canonical derived self-tensor multiplication.
Source: Stacks Project, Tag 08R2, proof of cases (1)--(2), using Tags 00CX, 00HD,
06XZ and 06Y6 (blueprint: lem-trf-flat-epimorphism-derived-self-tensor).

Proof:
1. Regard `B` as an `A`-module through `f`. Flat tensor exactness
   (`lem-weil-pbc-flat-tensor-exact`) makes tensoring any acyclic complex with
   `B[0]` acyclic degree by degree. Thus `B[0]` is K-flat
   (`def-pc-module-kflat-complex`).
2. Apply the recorded `lem-pc-derived-tensor-second-factor-functor` to the identity
   K-flat resolution of this complex. Its comparison identifies the derived tensor
   with the ordinary degree-zero tensor, with `B` acting through the second factor.
   The definition above then represents the very canonical multiplication by `μ[0]`.
3. Ordinary multiplication `μ(b ⊗ c) = bc` has inverse `ν(c) = 1 ⊗ c`.
   The equation `μν = id` is immediate. For `νμ = id`, lift `b` to `a : A`
   using surjectivity and use balancing to obtain
   `b ⊗ c = (a • 1) ⊗ c = 1 ⊗ (a • c) = 1 ⊗ bc`.
   Pure tensors generate the tensor product (`def-weil-pbc-module-tensor-product`),
   so the inverse equation holds everywhere. Both maps are `B`-linear for the
   second-factor action.
4. The single-complex functor and the localization `Q` preserve these inverse
   equations (`def-weil-abstract-derived-category`). Composing this isomorphism
   with the K-flat computation from step 2 proves the assertion in `D(B)` and hence
   also after restriction to `D(A)`. -/
theorem isIso_derivedSelfTensorMultiplication_of_flat_surjective
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    (f : A →+* B) (hf : Function.Surjective f) (hflat : f.Flat) :
    IsIso (derivedSelfTensorMultiplication f) := by
  sorry

end DerivedCategory
