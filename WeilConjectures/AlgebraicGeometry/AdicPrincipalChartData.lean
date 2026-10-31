/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicFormalGeometry
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-! # Principal formal opens and their section topologies

Source: Stacks Project, Tag 0AHY, formal-spaces.tex, section-formal-schemes-EGA.
(blueprint: def-per-adic-principal-chart-data)

The colimit in ringed spaces has the colimit topology and the inverse-limit sheaf of rings.
The formal spectrum is the recorded `adicFormalSpec`; no second construction is introduced.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical map from the formal spectrum to the ordinary spectrum, induced by the
closed immersions of its defining thickenings.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
noncomputable def adicFormalSpecToSpec (R : CommRingCat.{u}) (K : Ideal R) :
    adicFormalSpec R K ⟶ (Spec R).toRingedSpace :=
  colimit.desc _
    ((Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace).mapCocone
      { pt := Spec R
        ι :=
          { app := fun n ↦ (Scheme.IdealSheafData.ofIdealTop
              (K.map (Scheme.ΓSpecIso R).inv.hom) ^ n).subschemeι
            naturality := by intros; simp [adicThickeningDiagram] } })

/-- The principal open in a formal spectrum, as the inverse image of the ordinary principal open.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
noncomputable def adicFormalPrincipalOpen (R : CommRingCat.{u}) (K : Ideal R) (s : R) :
    Opens (adicFormalSpec R K) :=
  (Opens.map (adicFormalSpecToSpec R K).hom.base).obj (PrimeSpectrum.basicOpen s)

/-- Completed localization at one element, with the extended ideal of definition.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
abbrev adicCompletedAway (R : CommRingCat.{u}) (K : Ideal R) (s : R) :=
  AdicCompletion (K.map (algebraMap R (Localization.Away s))) (Localization.Away s)

/-- The canonical homomorphism into the completed principal localization.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
noncomputable def adicCompletedAwayMap (R : CommRingCat.{u}) (K : Ideal R) (s : R) :
    R →+* adicCompletedAway R K s :=
  (algebraMap (Localization.Away s) (adicCompletedAway R K s)).comp
    (algebraMap R (Localization.Away s))

/-- The canonical map from the ring into the global sections of its formal spectrum.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
noncomputable def adicFormalGlobalSection (R : CommRingCat.{u}) (K : Ideal R) :
    R →+* (adicFormalSpec R K).presheaf.obj (op ⊤) :=
  (SheafedSpace.Γ.map (adicFormalSpecToSpec R K).op).hom.comp
    (Scheme.ΓSpecIso R).inv.hom

/-- The pseudo-discrete topology on sections of a scheme: the initial topology for restrictions
onto quasi-compact open subspaces, each endowed with the discrete topology.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
@[instance_reducible]
def schemePseudoDiscreteSectionTopology (Y : Scheme.{u}) (U : Y.Opens) :
    TopologicalSpace (Y.presheaf.obj (op U)) :=
  ⨅ (V : Y.Opens) (h : V ≤ U) (_ : IsCompact (V : Set Y)),
    TopologicalSpace.induced (Y.presheaf.map (homOfLE h).op) ⊥

/-- The inverse-limit topology on sections of the formal spectrum. Each quotient sheaf has
its pseudo-discrete topology; the maps are the actual colimit cocone components.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
@[instance_reducible]
noncomputable def adicFormalSectionTopology (R : CommRingCat.{u}) (K : Ideal R)
    (U : Opens (adicFormalSpec R K)) :
    TopologicalSpace ((adicFormalSpec R K).presheaf.obj (op U)) :=
  ⨅ n : ℕ, TopologicalSpace.induced
    ((colimit.ι
      (adicThickeningDiagram (Scheme.IdealSheafData.ofIdealTop
        (K.map (Scheme.ΓSpecIso R).inv.hom)) ⋙ Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace) n).hom.c.app (op U))
    (schemePseudoDiscreteSectionTopology
      ((adicThickeningDiagram (Scheme.IdealSheafData.ofIdealTop
        (K.map (Scheme.ΓSpecIso R).inv.hom))).obj n)
      ((Opens.map (colimit.ι
        (adicThickeningDiagram (Scheme.IdealSheafData.ofIdealTop
          (K.map (Scheme.ΓSpecIso R).inv.hom)) ⋙ Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace) n).hom.base).obj U))

/-- A continuous formal-spectrum morphism inducing a specified ring map. The triangle fixes the
map on primes, continuity is imposed on every section ring, and global sections extend the
specified ring map. Source: Stacks Tag 0AHZ
(blueprint: def-per-adic-principal-chart-data). -/
def IsAdicFormalSpectrumMap {R S : CommRingCat.{u}} (K : Ideal R) (L : Ideal S)
    (φ : R →+* S) (F : adicFormalSpec S L ⟶ adicFormalSpec R K) : Prop :=
  F.hom.base ≫ (adicFormalSpecToSpec R K).hom.base =
      (adicFormalSpecToSpec S L).hom.base ≫ (Spec.map (CommRingCat.ofHom φ)).base ∧
    (∀ U : Opens (adicFormalSpec R K),
      @Continuous _ _ (adicFormalSectionTopology R K U)
        (adicFormalSectionTopology S L ((Opens.map F.hom.base).obj U))
        (F.hom.c.app (op U))) ∧
    (SheafedSpace.Γ.map F.op).hom.comp (adicFormalGlobalSection R K) =
      (adicFormalGlobalSection S L).comp φ

/-- The positive quotient-localization inverse system of a principal formal open.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
noncomputable def adicLocalizedQuotientTower (R : CommRingCat.{u}) (K : Ideal R) (s : R) :
    ℕᵒᵖ ⥤ CommRingCat.{u} :=
  Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (Localization.Away (Ideal.Quotient.mk (K ^ (n + 1)) s)))
    (fun n ↦ CommRingCat.ofHom (by
      have h := IsLocalization.Away.map
        (Localization.Away (Ideal.Quotient.mk (K ^ (n + 2)) s))
        (Localization.Away ((Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
          (Ideal.Quotient.mk (K ^ (n + 2)) s)))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (K ^ (n + 2)) s)
      simpa only [Ideal.Quotient.factor_mk] using h))

/-- The canonical section of a principal open induced by an element of the original ring.
Source: Stacks Tag 0AHY (blueprint: def-per-adic-principal-chart-data). -/
noncomputable def adicFormalPrincipalSection (R : CommRingCat.{u}) (K : Ideal R) (s : R) :
    R →+* (adicFormalSpec R K).presheaf.obj (op (adicFormalPrincipalOpen R K s)) :=
  ((adicFormalSpec R K).presheaf.map (homOfLE le_top).op).hom.comp
    (adicFormalGlobalSection R K)

/-- Characterization of the canonical completed-localization comparison: it is continuous and
extends restriction from the original ring. Source: Stacks Tag 0AHY
(blueprint: def-per-adic-principal-chart-data). -/
def IsAdicPrincipalSectionComparison (R : CommRingCat.{u}) (K : Ideal R) (s : R)
    (e : (adicFormalSpec R K).presheaf.obj (op (adicFormalPrincipalOpen R K s)) ≃+*
      adicCompletedAway R K s) : Prop :=
  e.toRingHom.comp (adicFormalPrincipalSection R K s) = adicCompletedAwayMap R K s ∧
    @IsHomeomorph _ _ (adicFormalSectionTopology R K (adicFormalPrincipalOpen R K s))
      ((K.map (adicCompletedAwayMap R K s)).adicTopology) e

end AlgebraicGeometry
