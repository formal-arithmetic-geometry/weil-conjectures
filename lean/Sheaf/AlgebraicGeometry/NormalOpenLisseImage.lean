/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.ConstructibleSheaf.FiniteMorphism
import WeilConjectures.ConstructibleSheaf.FinitePushforward
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Constructibility of the direct image from a normal open

Source: the blueprint, `sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-open-lisse-image`,
statement and both proof paragraphs (blueprint: lem-fin-normal-open-lisse-image).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem mono_generic_transpose
    {S : Scheme.{u}} [IsIntegral S] {E : Type u} [Field E]
    (h : Spec (.of E) ⟶ S) (hh : ∀ x, h x = genericPoint S)
    {Λ : Type (u + 1)} [CommRing Λ]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf L]
    (B : Sheaf (Spec (.of E)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj L ≅ B) :
    Mono ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv L B
      e.hom) := by
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h
  let t : L ⟶ (Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj B :=
    adj.homEquiv L B e.hom
  let w := (Spec (.of E)).algClosurePoint (IsLocalRing.closedPoint E)
  let d : Etale.upperStar (ModuleCat.{u + 1} Λ) h ⋙
      (pointSmallEtale w).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      (pointSmallEtale (w ≫ h)).sheafFiber (A := ModuleCat.{u + 1} Λ) :=
    Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) h w
  have ht : (Etale.upperStar (ModuleCat.{u + 1} Λ) h).map t ≫ adj.counit.app B =
      e.hom := (adj.homEquiv L B).symm_apply_apply e.hom
  have hmono : Mono (((pointSmallEtale w).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).map t)) := by
    have he := congrArg ((pointSmallEtale w).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map ht
    rw [Functor.map_comp] at he
    exact mono_of_mono_fac he
  have heq : ((pointSmallEtale (w ≫ h)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map t =
      d.inv.app L ≫ ((pointSmallEtale w).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) h).map t) ≫
            d.hom.app ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj B) := by
    rw [← cancel_epi (d.hom.app L)]
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.comp_map] using
      (d.hom.naturality t).symm
  have : Mono (((pointSmallEtale (w ≫ h)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map t) := by
    have hi : Mono (d.inv.app L) := mono_of_mono_fac (d.inv_hom_id_app L)
    have hj : Mono (d.hom.app ((Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj B)) :=
      mono_of_mono_fac (d.hom_inv_id_app _)
    rw [heq]
    exact mono_comp _ _
  exact Etale.mono_of_mono_sheafFiber_of_isLocallyConstantSheaf (Λ := Λ) (w ≫ h)
    (fun x ↦ hh (w x)) t this

/-- A finite locally constant module sheaf on a nonempty normal open of an integral scheme
of finite type over a field has constructible direct image. The coefficient ring is finite
and commutative, as in the constructibility convention. `IsNormalScheme V` includes
integrality, hence nonemptiness, of `V`.

Source: the blueprint, `sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-open-lisse-image`,
statement and both proof paragraphs (blueprint: lem-fin-normal-open-lisse-image).

Proof plan:
1. The field is Noetherian, so `X` is Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`, and its open `V` is Noetherian by
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`. A finite affine principal-open cover
   shows that `V` is of finite type. Choose a finite etale surjective trivializing cover
   `P → V` by `fin2-lem-lisse-trivialized-finite-etale`. Its finitely many clopen connected
   components `P_a` are nonempty normal integral by `lem-fin-etale-normal-components`, and
   the pullback of `L` on each is a constant finite module `M_a`.
2. The adjunction unit `L → p_* p^* L` is monic. After forgetting module structure it is
   the abelian unit by `lem-weil-pbc-module-direct-image-left-exact` and
   `lem-weil-pbc-module-abelian-inverse-image-comparison`. The finite stalk formula
   `lemma-weil-pbc-finite-stalk-formula` and the germ compatibility of
   `lem-weil-pbc-inverse-image-stalk-germ` identify it with the diagonal into a nonempty
   product of the same stalk. Use `lem-weil-pbc-geometric-stalks-detect-mono`.
3. Each component map `P_a → V` is surjective: its nonempty image is open by
   `lem-weil-pbc-etale-morphism-open-map` and closed by
   `lem-weil-pbc-finite-closed-map-finite-fibres`, while `V` is irreducible. Its generic
   fibre is a nonzero finite-dimensional domain over `K = k(X) = k(V)`, hence a field
   `K_a = k(P_a)` finite over `K`. On affine charts, surjectivity makes the kernel of
   the base ring map lie in the nilradical, and integrality makes it zero.
4. Normalize `X` in `K_a` using `def-fin-normalization-extension`. Its finite map
   `g_a : Y_a → X` extends `P_a → V` by `lem-fin-normalization-extends-cover` and
   `lem-fin-normalization-extension-finite`. The scheme `Y_a` is normal integral by
   `lem-weil-pbc-normalization-in-residue-field-extension`; its quasi-separatedness
   hypothesis follows from `lem-weil-pbc-locally-noetherian-quasi-separated`.
   Finiteness makes `Y_a` of finite type and therefore Noetherian.
5. By `lem-fin-normal-constant-open-image`, the constant sheaf `M_a` extends from
   `P_a` to the constant sheaf on `Y_a`. Composition of direct images, computed by
   fibre products as in `def-weil-pbc-direct-image`, and left exactness give an injection
   `k_* L → ∏_a g_{a,*} M_a`. Glue the constants on the finite disjoint union of the
   `Y_a` to a sheaf `E`; the displayed product is `g_* E` for the finite map `g`.
6. The finite clopen partition makes `E` constructible both in
   `def-weil-pbc-etale-constructible-sheaf` and in `def-constructible-constructible`.
   Its stalks are finite by `lem-weil-pbc-finite-locally-constant-module-values`.
   The representative descriptions in `lem-weil-pbc-filtered-colimit-sets-elementwise`
   and `lem-weil-pbc-filtered-colimit-modules-elementwise` identify the underlying sets
   of the module stalks with set stalks. Use `lem-galois-finite-stalks-comparison` for
   separably closed points, then `lem-weil-pbc-finite-pushforward-finite-stalk-module`
   to conclude that `g_* E` is constructible as a module sheaf.
7. Finally `lem-weil-pbc-constructible-subobjects-noetherian` applied to the injection
   into `g_* E` gives the asserted constructibility of `k_* L`. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open
    {K : Type u} [Field K] {X V : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [IsIntegral X] (k : V ⟶ X) [IsOpenImmersion k] (hV : IsNormalScheme V)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf L] :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) k).obj L) := by
  classical
  have : IsNoetherian X :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
      __ := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K)) }
  let := hV.1
  have hη : genericPoint X ∈ Set.range k := by
    rw [← genericPoint_eq_of_isOpenImmersion k]
    exact Set.mem_range_self _
  have hr : Set.range X.fromSpecFunctionField ⊆ Set.range k := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint X.functionField :=
      (inferInstance : Subsingleton (Spec (.of X.functionField))).elim _ _
    subst x
    simpa only [fromSpecFunctionField, fromSpecStalk_closedPoint] using hη
  let t : Spec (.of X.functionField) ⟶ V :=
    IsOpenImmersion.lift k X.fromSpecFunctionField hr
  have ht : t ≫ k = X.fromSpecFunctionField := IsOpenImmersion.lift_fac _ _ _
  let F := (Etale.upperStar (ModuleCat.{u + 1} Λ) t).obj L
  have : IsFiniteLocallyConstantSheaf F := IsFiniteLocallyConstantSheaf.upperStar t L
  have hF : IsConstructibleEtaleModuleSheaf F :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mpr
      (IsFiniteLocallyConstantSheaf.isConstructibleSheaf inferInstance)
  obtain ⟨E, hE, hAlg, hfin, _, M, hM, ⟨e⟩⟩ :=
    constructible_field_finite_separable_constant X.functionField Λ F hF
  let := hE
  let := hAlg
  let := hfin
  let := hM
  let π := Spec.map (CommRingCat.ofHom (algebraMap X.functionField E))
  let h := π ≫ t
  let f := X.fromSpecOfAlgebraFunctionField E
  let Y := X.normalizationIn E
  let ν := X.fromNormalizationIn E
  let g := f.toNormalization
  have hhk : h ≫ k = f := by simp only [h, Category.assoc, ht]; rfl
  have hgv : g ≫ ν = f := f.toNormalization_fromNormalization
  have : IsFinite ν := X.isFinite_fromNormalizationIn E (X ↘ Spec (.of K))
  let MY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let ME := (constantSheaf (Spec (.of E)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := by
    apply f.isIntegrallyClosed_stalk_normalization
    intro x
    have hx : x = IsLocalRing.closedPoint E := Subsingleton.elim _ _
    subst x
    exact IsIntegrallyClosed.of_equiv
      (stalkClosedPointIso (.of E)).commRingCatIsoToRingEquiv.symm
  obtain ⟨eg, heg⟩ := X.exists_iso_toNormalization_normalizationIn E
  have hu0 := (Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed Λ hn M).1
  let := hu0
  have hu : IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app MY) := by
    change IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (X.fromSpecOfAlgebraFunctionField E).toNormalization).unit.app MY)
    rw [← heg]
    exact Etale.isIso_unit_app_comp (ModuleCat.{u + 1} Λ) eg.hom Y.fromSpecFunctionField MY
  let := hu
  let egc : MY ≅ (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj ME :=
    asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app MY) ≪≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).mapIso
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).app M)
  let eh : (Etale.upperStar (ModuleCat.{u + 1} Λ) h).obj L ≅ ME :=
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) π t).app L ≪≫ e
  let φ : L ⟶ (Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj ME :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv L ME eh.hom
  have hhη : ∀ x, h x = genericPoint V := by
    intro x
    apply k.isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion k]
    change (h ≫ k) x = genericPoint X
    rw [hhk]
    have hx : x = IsLocalRing.closedPoint E := Subsingleton.elim _ _
    subst x
    change X.fromSpecFunctionField (π (IsLocalRing.closedPoint E)) = genericPoint X
    have hp : π (IsLocalRing.closedPoint E) = IsLocalRing.closedPoint X.functionField :=
      (inferInstance : Subsingleton (Spec (.of X.functionField))).elim _ _
    rw [hp]
    exact fromSpecStalk_closedPoint
  have : Mono φ := mono_generic_transpose (Λ := Λ) h hhη L ME eh
  let ψ : (Etale.lowerStar (ModuleCat.{u + 1} Λ) k).obj L ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) ν).obj MY :=
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) k).map φ ≫
      ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h k f hhk.symm).app ME).hom ≫
      ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) g ν f hgv.symm).app ME).inv ≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) ν).map egc.inv
  have hmφ : Mono ((Etale.lowerStar (ModuleCat.{u + 1} Λ) k).map φ) := by
    infer_instance
  have : Mono ψ := by
    dsimp only [ψ]
    have h₁ : Mono
        ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) h k f hhk.symm).app ME).hom := by
      infer_instance
    have h₂ : Mono
        ((Etale.lowerStarComp (ModuleCat.{u + 1} Λ) g ν f hgv.symm).app ME).inv := by
      infer_instance
    have h₃ : Mono ((Etale.lowerStar (ModuleCat.{u + 1} Λ) ν).map egc.inv) := by
      infer_instance
    exact mono_comp _ _
  have : Module.Finite Λ M := Module.Finite.of_finite
  have : IsFiniteSheaf MY := by
    refine ⟨fun Ω _ _ s ↦ ?_⟩
    have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    exact ((ModuleCat.isFinitelyGenerated_iff M).2 inferInstance).of_iso
      ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm
  have : IsLocallyConstantSheaf MY :=
    (Sheaf.isConstant_of_iso Y.smallEtaleTopology (Iso.refl MY)).isLocallyConstantSheaf
  have : IsFiniteLocallyConstantSheaf MY := ⟨⟩
  have : IsConstructibleSheaf MY :=
    IsFiniteLocallyConstantSheaf.isConstructibleSheaf inferInstance
  have hpush := IsConstructibleSheaf.lowerStar_of_isFinite ν MY
  exact isConstructibleEtaleModuleSheaf_of_mono_noetherian ψ
    ((isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr hpush)

end AlgebraicGeometry.Scheme
