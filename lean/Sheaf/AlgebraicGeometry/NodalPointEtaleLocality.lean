/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.JacobsonSpace
import Sheaf.AlgebraicGeometry.EtaleCompletedLocalRingIso

/-! # Étale locality of nodal completed local algebras

Source: Stacks Project, curves.tex, Tag 0C57, lemma-node-etale-local, and section-nodal
(blueprint: lem-trf-nodal-point-etale-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical coefficient map into the maximal-ideal completion of a local ring.
It is the composite of constants on `Spec k`, pullback to global sections, the germ map,
and the completion map. No coefficient field or splitting is chosen.
Source: Stacks Project, curves.tex, section-nodal and Tag 0C57
(blueprint: lem-trf-nodal-point-etale-locality). -/
noncomputable def Scheme.Hom.completedLocalScalarMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    k →+* AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) :=
  (algebraMap (X.presheaf.stalk x)
    (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x))).comp
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom)

private theorem residue_bijective_of_retraction
    {k R : Type u} [Field k] [CommRing R] [IsLocalRing R]
    (i : k →+* R) (r : R →+* k) (h : ∀ a, r (i a) = a) :
    Function.Bijective ((IsLocalRing.residue R).comp i) := by
  have hr : Function.Surjective r := fun a ↦ ⟨i a, h a⟩
  have := hr.isLocalHom
  let l := IsLocalRing.ResidueField.lift r
  refine ⟨RingHom.injective _, fun z ↦ ⟨l z, ?_⟩⟩
  apply l.injective
  exact (IsLocalRing.ResidueField.lift_residue_apply r (i (l z))).trans (h (l z))

private theorem nodalCompletion_residue_bijective
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (h : Nonempty
      (@AlgEquiv k
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
        _ _ _ (f.completedLocalScalarMap x).toAlgebra inferInstance)) :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom) := by
  let : Algebra k (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x)) := (f.completedLocalScalarMap x).toAlgebra
  obtain ⟨a⟩ := h
  let aug : (MvPowerSeries (Fin 2) k ⧸
      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}) →+* k :=
    Ideal.Quotient.lift _ MvPowerSeries.constantCoeff (by
      change Ideal.span _ ≤ RingHom.ker MvPowerSeries.constantCoeff
      apply Ideal.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      simp)
  let i := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom
  apply residue_bijective_of_retraction i
    (aug.comp (a.toRingHom.comp (algebraMap (X.presheaf.stalk x) _)))
  intro c
  change aug (a (f.completedLocalScalarMap x c)) = c
  change aug (a (algebraMap k _ c)) = c
  rw [a.commutes]
  change aug (Ideal.Quotient.mk _ (algebraMap k (MvPowerSeries (Fin 2) k) c)) = c
  simp [aug, MvPowerSeries.algebraMap_apply]

private theorem completedLocalScalarMap_naturality
    {k : Type u} [Field k] {C D : Scheme.{u}} (f : C ⟶ Spec (.of k))
    (e : D ⟶ C) (y : D) (c : k) :
    (e.stalkMap y).hom
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.Γgerm (e y)).hom c) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (e ≫ f).appTop ≫ D.presheaf.Γgerm y).hom c) := by
  change (e.stalkMap y)
      (C.presheaf.germ ⊤ (e y) trivial
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

private theorem etale_completedLocalAlgEquiv
    {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (e : D ⟶ C) [Etale e] (y : D)
    (hres :
      Function.Bijective
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.Γevaluation (e y)).hom) ∨
      Function.Bijective
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (e ≫ f).appTop ≫ D.Γevaluation y).hom)) :
    e y ∈ closedPoints C ∧ y ∈ closedPoints D ∧ Nonempty
      (@AlgEquiv k
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
          (C.presheaf.stalk (e y)))
        (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y))
          (D.presheaf.stalk y))
        _ _ _ (f.completedLocalScalarMap (e y)).toAlgebra
        ((e ≫ f).completedLocalScalarMap y).toAlgebra) := by
  let : Algebra k (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
      (C.presheaf.stalk (e y))) := (f.completedLocalScalarMap (e y)).toAlgebra
  let : Algebra k (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y))
      (D.presheaf.stalk y)) := ((e ≫ f).completedLocalScalarMap y).toAlgebra
  obtain ⟨hc, hd, _, g, hg, hbij⟩ := etale_completedLocalRing_iso f e y hres
  refine ⟨hc, hd, ⟨AlgEquiv.ofBijective
    ({ g with commutes' := ?_ } : _ →ₐ[k] _) hbij⟩⟩
  intro c
  change g (f.completedLocalScalarMap (e y) c) = (e ≫ f).completedLocalScalarMap y c
  apply AdicCompletion.ext_evalₐ
  intro n
  dsimp only [Scheme.Hom.completedLocalScalarMap, RingHom.comp_apply]
  rw [hg n _
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.Γgerm (e y)).hom c)
    (by simp [AdicCompletion.algebraMap_apply])]
  rw [completedLocalScalarMap_naturality f e y c]
  simp [AdicCompletion.algebraMap_apply]

/-- Nodal completed local `k`-algebras are invariant under an étale map of curves;
either nodal presentation also forces both points to be closed.
Source: Stacks Project, curves.tex, Tag 0C57, lemma-node-etale-local, and section-nodal
(blueprint: lem-trf-nodal-point-etale-locality).

Proof:
1. The constant coefficient map on the nodal power-series quotient, composed with a
   nodal presentation and the stalk completion map, retracts the structural map from k
   to the stalk. A surjective map from a local ring to a field is local; its induced
   residue-field embedding has this retraction as a right inverse on constants.
   Injectivity of that embedding proves that the structural residue map is bijective.
2. Apply lem-trf-etale-completed-local-ring-iso in the appropriate alternative. It gives
   closedness of both points and a bijective completed stalk map with specified values
   in every quotient by a power of the maximal ideal. Germ naturality and that formula
   show that this map preserves the canonical scalars. Package it as a k-algebra
   equivalence, then compose the nodal presentation with it or its inverse.
-/
theorem nodalPoint_etale_locality
    {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hpure : C.IsPureDimension 1) (e : D ⟶ C) [Etale e] (y : D) :
    (Nonempty
      (@AlgEquiv k
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
          (C.presheaf.stalk (e y)))
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
        _ _ _ (f.completedLocalScalarMap (e y)).toAlgebra inferInstance) ↔
      Nonempty
        (@AlgEquiv k
          (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) (D.presheaf.stalk y))
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
          _ _ _ ((e ≫ f).completedLocalScalarMap y).toAlgebra inferInstance)) ∧
    ((Nonempty
      (@AlgEquiv k
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
          (C.presheaf.stalk (e y)))
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
        _ _ _ (f.completedLocalScalarMap (e y)).toAlgebra inferInstance) ∨
      Nonempty
        (@AlgEquiv k
          (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y)) (D.presheaf.stalk y))
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
          _ _ _ ((e ≫ f).completedLocalScalarMap y).toAlgebra inferInstance)) →
      e y ∈ closedPoints C ∧ y ∈ closedPoints D) := by
  let : Algebra k (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e y)))
      (C.presheaf.stalk (e y))) := (f.completedLocalScalarMap (e y)).toAlgebra
  let : Algebra k (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk y))
      (D.presheaf.stalk y)) := ((e ≫ f).completedLocalScalarMap y).toAlgebra
  have _hpure := hpure
  have forward := fun h ↦ etale_completedLocalAlgEquiv f e y
    (Or.inl (nodalCompletion_residue_bijective f (e y) h))
  have backward := fun h ↦ etale_completedLocalAlgEquiv f e y
    (Or.inr (nodalCompletion_residue_bijective (e ≫ f) y h))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    obtain ⟨_, _, ⟨g⟩⟩ := forward h
    obtain ⟨a⟩ := h
    exact ⟨g.symm.trans a⟩
  · intro h
    obtain ⟨_, _, ⟨g⟩⟩ := backward h
    obtain ⟨a⟩ := h
    exact ⟨g.trans a⟩
  · rintro (h | h)
    · exact ⟨(forward h).1, (forward h).2.1⟩
    · exact ⟨(backward h).1, (backward h).2.1⟩

end AlgebraicGeometry
