/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityScalarComparison

/-! # Geometric Verdier biduality for constructible sheaves

This is the sheaf case, before the separate formal finite-truncation argument.
The target of the structure morphism is required to be isomorphic to the base point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- Geometric Verdier biduality for a constructible sheaf.

Source: Bhatt--Scholze, Lemma 6.7.20 and Proposition 6.8.14; latest blueprint
`sec-six-functors-basics/sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`.

Proof: `X` is noetherian, so `M[0]` is a bounded constructible `ℚ̄_ℓ`-complex and has an
integral model: a finite subextension `E`, a bounded constructible `𝒪_E`-complex `L` and an
isomorphism `e : F L ≅ M[0]`, where `F` is rationalization followed by extension to `ℚ̄_ℓ`
(`exists_padicAlgCl_iso_integralModel`). Integral biduality makes the integral evaluation
transpose `δ_L` invertible (`isIso_biduality_integral_constructible`). The scalar comparison
writes the `ℚ̄_ℓ` evaluation transpose of `F L` as `F δ_L` followed by an isomorphism
(`integral_qbar_biduality_comparison`), so it is invertible. Naturality of the evaluation
transpose along `e` transfers this to `M[0]`.
(blueprint: lem-pd-constructible-sheaf-biduality) -/
theorem isIso_biduality_constructible_sheaf [IsIso S.hom] (a : X ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hM : IsConstructibleModuleObject _ M) :
    IsIso (toIhomIhom
      ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  have _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  have _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  have _ : IsNoetherian X.left := ⟨⟩
  let K : PadicAlgClConstructible X.left ℓ :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj M,
      boundedConstructible_singleFunctor_zero_obj _ M hM⟩
  obtain ⟨E, L, ⟨e⟩⟩ := exists_padicAlgCl_iso_integralModel X.left ℓ K
  let F := (Mod.extendScalars (padicIntegersToPadicSubfield X.left ℓ E)).leftDerivedFunctor ⋙
    derivedExtendScalarsToPadicAlgCl X.left ℓ E
  let W := ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 a).obj (𝟙_ _)).obj
  let W' := ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)).obj
  have hδ : IsIso (toIhomIhom W L.obj) := isIso_biduality_integral_constructible ℓ a E L
  obtain ⟨c, hc⟩ := integral_qbar_biduality_comparison ℓ a E L
  have hF : IsIso (toIhomIhom W' (F.obj L.obj)) := by
    rw [hc]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W')
    ((boundedConstructible _).ι.mapIso e)).1 hF

end AlgebraicGeometry.ProEtale.CondensedRing
