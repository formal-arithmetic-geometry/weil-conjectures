/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityIntegral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityRational
public import WeilConjectures.SixFunctors.ConstructibleSheafBidualityQbar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityBaseField
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityScalarComparison

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

/-- Transport native integral biduality to a condensed constructible sheaf.

Source: Bhatt--Scholze, Lemma 6.7.20 and Proposition 6.8.14; latest blueprint
`sec-six-functors-basics/sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`,
the integral and field coefficient paragraph.

Proof: the finite-type scheme is noetherian. Choose an integral model `L` for `M[0]`
over a finite coefficient extension `E`. The given integral biduality makes `δ_L`
invertible. The canonical scalar comparison identifies `δ_(F L)` with `F(δ_L)`
followed by an isomorphism, hence it is invertible. Naturality along the integral-model
isomorphism `F L ≅ M[0]` finishes the proof. No coefficient-stage category is substituted
for the native condensed derived category.
(blueprint: lem-pd-constructible-sheaf-biduality-devissage) -/
theorem isIso_biduality_constructible_sheaf_of_stage_transport
    [IsIso S.hom] (a : X ⟶ S)
    (hIntegral : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (L : BoundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)),
      IsIso (toIhomIhom
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 a).obj (𝟙_ _)).obj
        L.obj))
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
  have hδ : IsIso (toIhomIhom W L.obj) := hIntegral E L
  obtain ⟨c, hc⟩ := integral_qbar_biduality_comparison ℓ a E L
  have hF : IsIso (toIhomIhom W' (F.obj L.obj)) := by
    rw [hc]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W')
    ((boundedConstructible _).ι.mapIso e)).1 hF

end AlgebraicGeometry.ProEtale.CondensedRing
