/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleFiniteTorStability

/-!
# The tensor–Hom adjunction on `Dctf(X_proét, Λ)`

Let `X` be of finite type over an algebraic closure `k` of `𝔽_p` and `Λ` a finite ring whose
exponent is invertible on `X`. The pro-étale derived internal Hom carries
`Dctf(X_proét, Λ) × Dctf(X_proét, Λ)` into `Dctf(X_proét, Λ)`
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_derivedHom`): every object of
`Dctf(X_proét, Λ)` is of the form `ν^* G` with `G ∈ Dctf(X_ét, Λ)`, and for those this is
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`.
Together with the stability under `⊗ᴸ`
(`AlgebraicGeometry.ProEtale.constructibleFiniteTor_tensor`), the ambient adjunction
`K ⊗ᴸ - ⊣ RHom(K, -)` restricts to `Dctf(X_proét, Λ)` with the same unit and counit
(`AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.tensorHomAdjunction`).

## Main statements

- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_derivedHom`
- `AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor.tensorHomAdjunction`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] {p : ℕ}
  [Fact p.Prime] [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [HasInvertibleExponent Λ X]

include p aX

/-- Blueprint `proposition-six-operations-dctf--15`, the finite coefficients over `k = 𝔽̄_p`:
for `K, M ∈ Dctf(X_proét, Λ)`, the derived internal Hom `RHom(K, M)` lies in
`Dctf(X_proét, Λ)`. Writing `K ≅ ν^* G` and `M ≅ ν^* G'` with `G, G' ∈ Dctf(X_ét, Λ)`, this is
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory`.
-/
theorem constructibleFiniteTor_derivedHom
    {K M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj M) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_constructibleFiniteTor_iso_mapDerivedCategory Λ hK
  obtain ⟨G', hG', ⟨e'⟩⟩ := exists_constructibleFiniteTor_iso_mapDerivedCategory Λ hM
  exact (DerivedCategory.constructibleFiniteTor _ X).prop_of_iso
    (((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).mapIso e.op).symm.app _ ≪≫
      ((ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).mapIso e')
    (DerivedCategory.constructibleFiniteTor_derivedHom_mapDerivedCategory Λ (p := p) aX hG hG')

/-- Blueprint `proposition-six-operations-dctf--18`, the finite coefficients over `k = 𝔽̄_p`:
for `K ∈ Dctf(X_proét, Λ)`, the tensor–Hom adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on
`Dctf(X_proét, Λ)` is the restriction of the ambient adjunction
`AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction` along the fully faithful inclusions, so
that its unit and counit are the ambient ones. -/
noncomputable def DerivedCategoryFiniteTor.tensorHomAdjunction
    (K : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
          (ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K.obj)
        (fun M ↦ constructibleFiniteTor_tensor Λ K.property M.property) ⊣
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).lift
        ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).ι ⋙
          (ProEtale.derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K.obj))
        (fun M ↦ constructibleFiniteTor_derivedHom Λ (p := p) aX K.property M.property) :=
  (derivedTensorHomAdjunction _ K.obj).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

end AlgebraicGeometry.ProEtale
