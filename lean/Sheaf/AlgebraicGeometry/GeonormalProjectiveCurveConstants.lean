/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.GeonormalDimOneSmooth
import Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import Sheaf.AlgebraicGeometry.FiniteSeparableBaseRefinement
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# The constant field of a geometrically normal projective curve

Source: Stacks Project, Varieties, Tag 0GK5, last paragraph.
(blueprint: lem-weil-pbc-geonormal-projective-curve-constants)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem separable_of_separableExtension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (h : Algebra.IsSeparableExtension k L) : Algebra.IsSeparable k L := by
  obtain ⟨s, hs, hsep⟩ := h ⊤ (IntermediateField.fg_of_noetherian ⊤)
  have : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
  have he : s = ∅ := by
    exact Set.eq_empty_iff_forall_notMem.mpr (fun x hx ↦ isEmptyElim (⟨x, hx⟩ : s))
  subst s
  rw [IntermediateField.adjoin_empty] at hsep
  have : Algebra.IsSeparable (⊥ : IntermediateField k (⊤ : IntermediateField k L))
      (⊤ : IntermediateField k L) := hsep
  have : Algebra.IsSeparable k (⊤ : IntermediateField k L) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (⊥ : IntermediateField k (⊤ : IntermediateField k L)) k _
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
    (⊤ : IntermediateField k L) ≃ₐ[k] L)

/-- A nonempty integral geometrically normal projective curve becomes smooth, projective and
geometrically irreducible over its finite separable field of constants.
Source: Stacks Project, Varieties, Tag 0GK5, last paragraph.
(blueprint: lem-weil-pbc-geonormal-projective-curve-constants)

Proof: geometric normality in dimension at most one gives smoothness and geometric reducedness.
The global sections of the proper integral scheme form a finite field extension. Geometric
reducedness makes this extension separable. The canonical map to its spectrum has geometrically
connected fibres by Stein factorization. Refine the smooth projective structure through the
finite separable field. Smoothness and geometric connectedness imply geometric irreducibility,
since every field base change is regular and connected. The canonical factorization of the
structure morphism gives the displayed equation. -/
theorem exists_geonormal_projective_curve_constants
    (k : Type u) [Field k] (Z : Scheme.{u}) [IsIntegral Z]
    (f : Z ⟶ Spec (.of k)) [IsHProjective f]
    (hdim : topologicalKrullDim Z ≤ 1)
    (hnormal : ∀ (L : Type u) [Field L] [Algebra k L],
      ∀ x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
      IsDomain ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
      IsIntegrallyClosed ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (q : Z ⟶ Spec (.of L)),
      Module.Finite k L ∧ Algebra.IsSeparable k L ∧ Smooth q ∧ IsHProjective q ∧
      GeometricallyIrreducible q ∧
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = f := by
  let : Z.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper f := IsHProjective.isProper f
  have : LocallyOfFiniteType (Z ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  have : QuasiCompact (Z ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  obtain ⟨hs, hr, _⟩ :=
    smooth_and_geometricallyReduced_of_geonormal_dim_le_one k Z hdim hnormal
  have : Smooth f := hs
  have : GeometricallyReduced (Z ↘ Spec (.of k)) := hr
  have : IsProper (Z ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  let hfield : IsField Γ(Z, ⊤) := Scheme.isField_globalSections_of_universallyClosed (k := k)
  let : Field Γ(Z, ⊤) := hfield.toField
  let : Algebra k Γ(Z, ⊤) := (Scheme.globalSectionsRingHom k (X := Z)).toAlgebra
  have : Module.Finite k Γ(Z, ⊤) := Scheme.finite_globalSectionsRingHom_of_isProper (k := k)
  have hsep := proper_geometricallyReduced_globalSections_isSeparable k Z hfield
  have : Algebra.IsSeparable k Γ(Z, ⊤) := separable_of_separableExtension k Γ(Z, ⊤) hsep
  have hfac : Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤))) = f :=
    Scheme.toSpecΓ_steinFactorizationBase f
  have : Smooth (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) :=
    hfac.symm ▸ hs
  have : IsHProjective
      (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) := hfac.symm ▸ ‹_›
  obtain ⟨hq, hp, _⟩ :=
    smooth_hProjective_proper_of_finite_separable_base k Γ(Z, ⊤) Z Z.toSpecΓ
  have : Smooth Z.toSpecΓ := hq
  have : GeometricallyConnected Z.toSpecΓ := (Scheme.Hom.steinFactorization_affine f).2.2.1
  exact ⟨Γ(Z, ⊤), inferInstance, inferInstance, Z.toSpecΓ, inferInstance, inferInstance,
    hq, hp, GeometricallyIrreducible.of_smooth_of_geometricallyConnected _, hfac⟩

end AlgebraicGeometry
