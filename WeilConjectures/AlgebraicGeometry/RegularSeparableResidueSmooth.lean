/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.ZetaSeries

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Etale.Field

/-! # Smoothness at a regular point with separable residue field

Source: Stacks Project, Algebra, Tag 00TV.
(blueprint: lem-trf-regular-separable-residue-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A regular point of a scheme locally of finite type over a field is smooth when its
residue field is separable algebraic over the field.

Source: Stacks Project, Algebra, Tag 00TV.
(blueprint: lem-trf-regular-separable-residue-smooth).

Proof: Choose an affine neighbourhood and identify its localization at the point with the
stalk. The induced residue-field isomorphism respects the base field. A separable algebraic
field extension is formally etale, hence formally smooth. The regular-local smoothness
criterion applies to the localization. The smooth locus then supplies the neighbourhood.
-/
theorem regular_separable_residue_smooth
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)]
    (hsep : @Algebra.IsSeparable k (X.residueField x) _ _
      (f.residueFieldAlgebraMap x).toAlgebra) :
    ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (.of k)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have hft := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE ⊤ V hVU).hom]
  let e : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let : Algebra k Γ(X, V) := ((f.appLE ⊤ V hVU).hom.comp e.toRingHom).toAlgebra
  have : Algebra.FiniteType k Γ(X, V) :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ e.surjective)
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let eS : Localization.AtPrime q ≃ₐ[Γ(X, V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.primeCompl _ _
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    .of_ringEquiv eS.symm.toRingEquiv
  let : Algebra k (X.residueField x) := (f.residueFieldAlgebraMap x).toAlgebra
  have : Algebra.IsSeparable k (X.residueField x) := hsep
  let eR : IsLocalRing.ResidueField (Localization.AtPrime q) ≃ₐ[k] X.residueField x := by
    refine AlgEquiv.ofRingEquiv
      (f := IsLocalRing.ResidueField.mapEquiv eS.toRingEquiv) fun a ↦ ?_
    change IsLocalRing.residue (X.presheaf.stalk x)
      (eS (algebraMap k (Localization.AtPrime q) a)) = f.residueFieldAlgebraMap x a
    rw [IsScalarTower.algebraMap_apply k Γ(X, V), eS.commutes]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V hVU ≫
      X.presheaf.germ V x hxV ≫ X.residue x).hom a = _
    have heq : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V hVU ≫
        X.presheaf.germ V x hxV ≫ X.residue x =
        CommRingCat.ofHom (f.residueFieldAlgebraMap x) := by
      change _ = CommRingCat.ofHom (algebraMap (CommRingCat.of k)
        (f.base x).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv ≫ f.residueFieldMap x
      rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
        Scheme.residue_residueFieldMap, f.germ_stalkMap_assoc ⊤ x trivial]
      simp [Scheme.Hom.appLE]
    exact congrArg (fun m ↦ m.hom a) heq
  have : Algebra.IsSeparable k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    Algebra.IsSeparable.of_algHom k (X.residueField x) eR.toAlgHom
  have : Algebra.FormallyEtale k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have h : Algebra.FormallySmooth k (Localization.AtPrime q) :=
    Algebra.FormallySmooth.localization_of_isRegularLocalRing q
  have hx : x ∈ f.smoothLocus := by
    rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ hU V hV hVU hxV]
    change Algebra.FormallySmooth Γ(Spec (.of k), ⊤) (Localization.AtPrime q)
    rw [← RingHom.formallySmooth_algebraMap] at h ⊢
    have heq : algebraMap k (Localization.AtPrime q) =
        (algebraMap Γ(Spec (.of k), ⊤) (Localization.AtPrime q)).comp e.toRingHom := by
      rw [IsScalarTower.algebraMap_eq k Γ(X, V),
        IsScalarTower.algebraMap_eq Γ(Spec (.of k), ⊤) Γ(X, V)]
      rfl
    rw [heq] at h
    have := RingHom.FormallySmooth.respectsIso.2 _ e.symm h
    convert this using 1
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
  refine ⟨f.smoothLocus, hx, Scheme.Hom.smoothLocus_eq_top_iff.mp ?_⟩
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  ext z
  simp

end AlgebraicGeometry
