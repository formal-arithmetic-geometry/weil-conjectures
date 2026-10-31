/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Independence of irreducibility from the strict-henselization presentation

Source: Stacks Project, More on Algebra, Tag 06DM, and Algebra, Tags 04GU and 04GW.
(blueprint: lem-dl-a1-strict-henselization-irreducible-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

open CategoryTheory CategoryTheory.Limits

variable {R S : Type u} [CommRing R] [CommRing S]

private def changeBase (e : S →+* R) : CommAlgCat.{w} R ⥤ CommAlgCat.{w} S where
  obj X := by
    let := ((algebraMap R X).comp e).toAlgebra
    exact CommAlgCat.of S X
  map {X Y} f := by
    let := ((algebraMap R X).comp e).toAlgebra
    let := ((algebraMap R Y).comp e).toAlgebra
    exact CommAlgCat.ofHom {
      toRingHom := f.hom.toRingHom
      commutes' := fun s ↦ by
        change f.hom (algebraMap R X (e s)) = algebraMap R Y (e s)
        exact f.hom.commutes (e s) }
  map_id X := by ext x; rfl
  map_comp f g := by ext x; rfl

private def changeBaseIdIso (f : R →+* R) (hf : f = .id R) : changeBase.{u, w} f ≅ 𝟭 _ :=
  NatIso.ofComponents fun X ↦ CommAlgCat.isoMk <|
    @AlgEquiv.ofRingEquiv (f := RingEquiv.refl X) _ _ _ _ _ _
      ((changeBase f).obj X).algebra X.algebra fun r ↦ by subst hf; rfl

private def changeBaseCompIso {T : Type u} [CommRing T]
    (f : R →+* S) (g : S →+* T) (gf : R →+* T) (hgf : gf = g.comp f) :
    changeBase.{u, w} gf ≅ changeBase g ⋙ changeBase f :=
  NatIso.ofComponents fun X ↦ CommAlgCat.isoMk <|
    @AlgEquiv.ofRingEquiv (f := RingEquiv.refl X) _ _ _ _ _ _
      ((changeBase gf).obj X).algebra
      ((changeBase f).obj ((changeBase g).obj X)).algebra fun r ↦ by subst hgf; rfl

private def changeBaseEquiv (e : R ≃+* S) : CommAlgCat.{w} R ≌ CommAlgCat.{w} S where
  functor := changeBase e.symm.toRingHom
  inverse := changeBase e.toRingHom
  unitIso := (changeBaseIdIso _ rfl).symm ≪≫
    changeBaseCompIso _ _ _ e.symm_toRingHom_comp_toRingHom.symm
  counitIso := (changeBaseCompIso _ _ _ e.toRingHom_comp_symm_toRingHom.symm).symm ≪≫
    changeBaseIdIso _ rfl
  functor_unitIso_comp X := by ext x; rfl

private noncomputable def comparePointedColimits
    (K L : Type (max u v)) [CommRing K] [Algebra R K] [CommRing L] [Algebra S L]
    (F : CommAlgCat.{max u v} R ≌ CommAlgCat.{max u v} S)
    (e : F.functor.obj (CommAlgCat.of R K) ≅ CommAlgCat.of S L)
    (h : ∀ C : CommAlgCat.{max u v} R,
      Algebra.Etale S (F.functor.obj C) ↔ Algebra.Etale R C)
    (c : Cocone (Algebra.strictHenselizationPointedDiagramIn.{u, v} R K))
    (hc : IsColimit c)
    (d : Cocone (Algebra.strictHenselizationPointedDiagramIn.{u, v} S L))
    (hd : IsColimit d) : F.functor.obj c.pt ≅ d.pt := by
  let PR : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Algebra.Etale R X.left
  let PS : ObjectProperty (Over (CommAlgCat.of S L)) := fun X ↦ Algebra.Etale S X.left
  let : PS.IsClosedUnderIsomorphisms := {
    of_iso := fun {X Y} i hi ↦ by
      exact @Algebra.Etale.of_equiv S X.left Y.left _ _ _ _ _ hi
        (CommAlgCat.algEquivOfIso ((Over.forget _).mapIso i)) }
  let E₀ := (Over.postEquiv (CommAlgCat.of R K) F).trans (Over.mapIso e)
  have heq : PS.inverseImage E₀.functor = PR := by
    funext X
    exact propext (h X.left)
  let E := E₀.congrFullSubcategory heq
  let c' := F.functor.mapCocone c
  have hc' : IsColimit c' := isColimitOfPreserves F.functor hc
  have hd' : IsColimit (d.whisker E.functor) := hd.whiskerEquivalence E
  exact hc'.coconePointUniqueUpToIso hd'


/-- Geometric unibranchness expressed using one strict henselization is invariant under
an isomorphism of local rings and under the choices of residue separable closure and
colimit presentation.

Source: Stacks Project, More on Algebra, Tag 06DM, and Algebra, Tags 04GU and 04GW.
(blueprint: lem-dl-a1-strict-henselization-irreducible-transport).

Proof: The local-ring isomorphism identifies the maximal ideals, hence the residue
fields. Transport the residue-field action on the second separable closure through
this identification. Uniqueness of separable closures supplies a compatible field
isomorphism. Restriction of scalars through the base isomorphism and composition of
pointings with the field isomorphism then give inverse equivalences between the two
categories of pointed etale algebras. Etaleness is invariant under ring isomorphisms,
so both functors preserve the full subcategories defining the diagrams. Their
forgetful diagrams are naturally isomorphic after restriction of scalars. Transport
one colimit cocone along this equivalence; uniqueness of colimits and the recorded
identifications with H and J give a ring isomorphism H ≃+* J. The induced spectrum
homeomorphism transports irreducibility. This argument also includes different
colimit presentations with the same residue closure, using its identity isomorphism. -/
theorem irreducible_strictHenselization_of_equiv
    (R S : Type u) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (e : R ≃+* S)
    (K H : Type (max u v)) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing H] [Algebra R H]
    (P : StrictHenselizationPresentationIn.{u, v} R K H)
    [IrreducibleSpace (PrimeSpectrum H)] :
    ∀ (L J : Type (max u v)) [Field L]
      [Algebra (IsLocalRing.ResidueField S) L]
      [IsSepClosure (IsLocalRing.ResidueField S) L]
      [Algebra S L] [IsScalarTower S (IsLocalRing.ResidueField S) L]
      [CommRing J] [Algebra S J],
      StrictHenselizationPresentationIn.{u, v} S L J →
        IrreducibleSpace (PrimeSpectrum J) := by
  classical
  intro L J _ _ _ _ _ _ _ Q
  let er := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra (IsLocalRing.ResidueField R) L :=
    ((algebraMap (IsLocalRing.ResidueField S) L).comp er.toRingHom).toAlgebra
  have : Algebra.IsSeparable (IsLocalRing.ResidueField R) L :=
    Algebra.IsSeparable.of_equiv_equiv er.symm (RingEquiv.refl L) (by
      ext r
      change algebraMap (IsLocalRing.ResidueField S) L (er (er.symm r)) =
        algebraMap (IsLocalRing.ResidueField S) L r
      rw [er.apply_symm_apply])
  let : IsSepClosure (IsLocalRing.ResidueField R) L :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField S), inferInstance⟩
  let ef := IsSepClosure.equiv (IsLocalRing.ResidueField R) K L
  have he (r : R) : ef (algebraMap R K r) = algebraMap S L (e r) := by
    rw [IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) K,
      ef.commutes]
    change algebraMap (IsLocalRing.ResidueField S) L
      (er (IsLocalRing.residue R r)) = algebraMap S L (e r)
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
      ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply S (IsLocalRing.ResidueField S) L]
    rfl
  let F := changeBaseEquiv.{u, max u v} e
  let ik : F.functor.obj (CommAlgCat.of R K) ≅ CommAlgCat.of S L :=
    CommAlgCat.isoMk <|
      @AlgEquiv.ofRingEquiv (f := ef.toRingEquiv) _ _ _ _ _ _
        (F.functor.obj (CommAlgCat.of R K)).algebra (CommAlgCat.of S L).algebra
        (fun s ↦ by
          change ef (algebraMap R K (e.symm s)) = algebraMap S L s
          rw [he, e.apply_symm_apply])
  have het (C : CommAlgCat.{max u v} R) :
      Algebra.Etale S (F.functor.obj C) ↔ Algebra.Etale R C := by
    let : Algebra S R := e.symm.toRingHom.toAlgebra
    let : Algebra R S := e.toRingHom.toAlgebra
    let : Algebra S C := (F.functor.obj C).algebra
    have : Algebra.Etale S R := RingHom.Etale.of_bijective e.symm.bijective
    have : Algebra.Etale R S := RingHom.Etale.of_bijective e.bijective
    have : IsScalarTower S R C := .of_algebraMap_eq' rfl
    have : IsScalarTower R S C := .of_algebraMap_eq (fun r ↦ by
      change algebraMap R C r = algebraMap R C (e.symm (e r))
      rw [e.symm_apply_apply])
    constructor
    · intro hc
      have : Algebra.Etale S C := hc
      exact Algebra.Etale.comp R S C
    · intro hc
      have := hc
      exact Algebra.Etale.comp S R C
  let i := (F.functor.mapIso P.identification).symm ≪≫
    comparePointedColimits K L F ik het P.cocone P.isColimit Q.cocone Q.isColimit ≪≫
      Q.identification
  let ei : H ≃+* J := (CommAlgCat.algEquivOfIso i).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv ei).irreducibleSpace_iff.mp inferInstance

end Algebra
