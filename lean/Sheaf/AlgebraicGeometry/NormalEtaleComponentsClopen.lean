/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Connected.Clopen
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.AlgebraicGeometry.NormalEtale
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Clopen components of an etale scheme over a locally Noetherian normal base

Source: Bhatt--Scholze, The pro-etale topology for schemes, proof of Lemma 7.4.10,
p. 71, first paragraph; Stacks Project, Tags 0BQ3 and 0357
(blueprint: lem-a1-normal-etale-components-clopen).
-/

@[expose] public section

universe u v

open CategoryTheory

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false in
-- Changing the base to ULift puts all rings in the common algebra universe.
private def liftBase (A : Type u) [CommRing A] :
    CommAlgCat.{max u v} A ≌ CommAlgCat.{max u v} (ULift.{v} A) := by
  let F : CommAlgCat.{max u v} A ⥤ CommAlgCat.{max u v} (ULift.{v} A) :=
    { obj := fun B ↦
        letI : Algebra (ULift.{v} A) B := ULift.algebra' A B
        CommAlgCat.of (ULift.{v} A) B
      map := fun {B C} f ↦ by
        letI : Algebra (ULift.{v} A) B := ULift.algebra' A B
        letI : Algebra (ULift.{v} A) C := ULift.algebra' A C
        exact CommAlgCat.ofHom
          { f.hom.toRingHom with commutes' := fun a ↦ f.hom.commutes a.down } }
  let G : CommAlgCat.{max u v} (ULift.{v} A) ⥤ CommAlgCat.{max u v} A :=
    { obj := fun B ↦
        letI : Algebra A B :=
          ((algebraMap (ULift.{v} A) B).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        CommAlgCat.of A B
      map := fun {B C} f ↦ by
        letI : Algebra A B :=
          ((algebraMap (ULift.{v} A) B).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        letI : Algebra A C :=
          ((algebraMap (ULift.{v} A) C).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
        exact CommAlgCat.ofHom
          { f.hom.toRingHom with commutes' := fun a ↦ f.hom.commutes (ULift.up a) } }
  exact
    { functor := F
      inverse := G
      unitIso := NatIso.ofComponents (fun B ↦ by
        apply CommAlgCat.isoMk
        exact @AlgEquiv.ofRingEquiv A B (G.obj (F.obj B)) _ _ _ B.algebra
          (G.obj (F.obj B)).algebra (RingEquiv.refl B) (fun _ ↦ rfl)) (by intros; ext; rfl)
      counitIso := NatIso.ofComponents (fun B ↦ by
        apply CommAlgCat.isoMk
        exact @AlgEquiv.ofRingEquiv (ULift.{v} A) (F.obj (G.obj B)) B _ _ _
          (F.obj (G.obj B)).algebra B.algebra (RingEquiv.refl B) (fun _ ↦ rfl))
        (by intros; ext; rfl) }

private lemma liftBase_etale (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    Algebra.Etale (ULift.{v} A) ((liftBase.{u, v} A).functor.obj B) ↔
      Algebra.Etale A B := by
  let : Algebra (ULift.{v} A) B := ULift.algebra' A B
  have : IsScalarTower A (ULift.{v} A) B := by
    constructor
    intro a b c
    change (a * b.down) • c = a • b.down • c
    exact mul_smul a b.down c
  have : Algebra.Etale A (ULift.{v} A) := Algebra.Etale.of_equiv ULift.algEquiv.symm
  constructor
  · intro h
    change Algebra.Etale (ULift.{v} A) B at h
    have := h
    exact Algebra.Etale.comp A (ULift.{v} A) B
  · intro h
    have := h
    exact Algebra.Etale.of_restrictScalars A (ULift.{v} A) B

private noncomputable def pointedLift (A : Type u) (K : Type (max u v))
    [CommRing A] [Field K] [Algebra A K] :
    let K' := (liftBase.{u, v} A).functor.obj (CommAlgCat.of A K)
    ObjectProperty.FullSubcategory (fun S : Over (CommAlgCat.of A K) ↦
      Algebra.Etale A S.left) ≌
    ObjectProperty.FullSubcategory (fun S : Over K' ↦ Algebra.Etale (ULift.{v} A) S.left) := by
  let E := Over.postEquiv (liftBase.{u, v} A) (X := CommAlgCat.of A K)
  let K' := (liftBase.{u, v} A).functor.obj (CommAlgCat.of A K)
  let Q : ObjectProperty (Over K') :=
    fun S ↦ Algebra.Etale (ULift.{v} A) S.left
  let : Q.IsClosedUnderIsomorphisms := ⟨fun {S T} i h ↦ by
    have : Algebra.Etale (ULift.{v} A) S.left := h
    change Algebra.Etale (ULift.{v} A) T.left
    let i' : S.left ≅ T.left := (Over.forget K').mapIso i
    exact Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso i')⟩
  exact E.congrFullSubcategory (Q := Q) (by
    ext S
    exact liftBase_etale A S.left)

-- Transport both the specified colimit and its residue separable-closure structure.
private theorem strictPresentation_domain
    (A : Type u) (K H : Type (max u v)) [CommRing A] [IsLocalRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, v} A K H) : IsDomain H := by
  classical
  let R := ULift.{v} A
  let e : R ≃+* A := ULift.ringEquiv
  let : IsLocalRing R := e.symm.isLocalRing
  let : IsDomain R := MulEquiv.isDomain _ e.toMulEquiv
  let : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  let E₀ := liftBase.{u, v} A
  let : Algebra R K := ULift.algebra' A K
  have : IsLocalHom e.toRingHom :=
    ⟨fun x hx ↦ hx.map e.symm.toMonoidHom⟩
  let eκ := IsLocalRing.ResidueField.mapEquiv e
  let : Algebra (IsLocalRing.ResidueField R) K :=
    ((algebraMap (IsLocalRing.ResidueField A) K).comp eκ.toRingHom).toAlgebra
  have : IsSepClosure (IsLocalRing.ResidueField R) K :=
    ⟨IsSepClosure.sep_closed (IsLocalRing.ResidueField A),
      Algebra.IsSeparable.of_equiv_equiv eκ.symm (RingEquiv.refl K) (by
        ext x
        simp [RingHom.algebraMap_toAlgebra])⟩
  have : IsScalarTower R (IsLocalRing.ResidueField R) K := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap A K r.down =
      algebraMap (IsLocalRing.ResidueField A) K
        (IsLocalRing.ResidueField.map e.toRingHom (IsLocalRing.residue R r))
    rw [IsLocalRing.ResidueField.map_residue]
    exact IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) K r.down
  let E := pointedLift.{u, v} A K
  let D := Algebra.strictHenselizationPointedDiagramIn.{u, v} A K
  let D' := Algebra.strictHenselizationPointedDiagram R K
  let d : E.functor ⋙ D' ≅ D ⋙ E₀.functor :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let c := E₀.functor.mapCocone P.cocone
  let hc : IsColimit c := isColimitOfPreserves E₀.functor P.isColimit
  let cE := (Cocone.precompose d.hom).obj c
  let hcE : IsColimit cE := (IsColimit.precomposeHomEquiv d c).symm hc
  let c' := (Cocone.precompose (E.invFunIdAssoc D').inv).obj (cE.whisker E.inverse)
  let hc' : IsColimit c' :=
    (IsColimit.precomposeHomEquiv (E.invFunIdAssoc D').symm _).symm
      (hcE.whiskerEquivalence E.symm)
  let H' := E₀.functor.obj (CommAlgCat.of A H)
  let : Algebra R H := ULift.algebra' A H
  have hH : Algebra.IsStrictHenselization R K H :=
    ⟨c', ⟨hc'⟩, ⟨E₀.functor.mapIso P.identification⟩⟩
  obtain ⟨hloc, _⟩ := Algebra.strictHenselization_local_maximalIdeal R K H hH
  have := hloc
  obtain ⟨hsmall, hfilt⟩ := Algebra.pointedEtale_small_filtered R K
  let := hsmall
  let := hfilt
  let I := ObjectProperty.FullSubcategory
    (fun T : Over (CommAlgCat.of R K) ↦ Algebra.Etale R T.left)
  let S := CategoryTheory.equivSmallModel.{max u v} I
  let : IsFiltered (SmallModel.{max u v} I) := IsFiltered.of_equivalence S
  let B := S.inverse ⋙ D'
  let cb := c'.whisker S.inverse
  let hcb := hc'.whiskerEquivalence S.symm
  let : HasColimit B := ⟨⟨cb, hcb⟩⟩
  let i := (colimit.isColimit B).coconePointUniqueUpToIso hcb ≪≫
    E₀.functor.mapIso P.identification
  change IsLocalRing H at hloc
  let : IsLocalRing H := hloc
  let ei : ↥(colimit B) ≃+* H := (CommAlgCat.algEquivOfIso i).toRingEquiv
  let : IsLocalRing ↥(colimit B) := ei.symm.isLocalRing
  have hR (p : Ideal R) [p.IsPrime] :
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ p.primeCompl
      p.primeCompl_le_nonZeroDivisors⟩
  have hB (j : SmallModel.{max u v} I) : Algebra.Etale R (B.obj j) :=
    (S.inverse.obj j).property
  obtain ⟨⟨hd, _⟩, _⟩ :=
    CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit R hR B hB
  let : IsDomain ↥(colimit B) := hd
  exact MulEquiv.isDomain _ ei.symm.toMulEquiv

namespace AlgebraicGeometry

/-- An etale scheme over a locally Noetherian scheme with normal local domains is locally
topologically Noetherian and geometrically unibranch. Its irreducible components are clopen,
and its nonempty connected components are irreducible and clopen. The source can be empty.
Strict henselizations are quantified in a common universe at least as large as the stalks.
Source: Bhatt--Scholze, proof of Lemma 7.4.10, p. 71, first paragraph; Stacks Project,
Tags 0BQ3, 0357 and 06DI (blueprint: lem-a1-normal-etale-components-clopen).

Proof:
1. Etaleness (`def-weil-etale-morphism`) gives locally finite presentation
   (`def-sbc-locally-finite-presentation`), hence pointwise finite type. The pointwise
   criterion `lem-weil-pbc-lft-pointwise-criterion` gives locally finite type
   (`def-weil-finite-type-morphism`), so `pqf-lem-locnoeth-lft` makes the source locally
   Noetherian. Choose affine Noetherian neighbourhoods (`pqf-def-locnoeth`); their spaces
   are Noetherian by `lem-sc-affine-noetherian-underlying-space`.
2. The localization at every prime of an affine chart of the base is its corresponding
   stalk (`lem-weil-pbc-affine-open-stalk-localization`), hence a normal domain. Thus the
   chart ring is normal (`def-weil-pbc-normal-ring`).
3. Cover the source by affine etale charts over such base charts. Their rings are normal
   by `lem-weil-pbc-etale-over-normal-ring-normal`; their stalks are normal domains by
   `lem-weil-pbc-affine-open-stalk-localization` and `def-weil-pbc-normal-ring`.
4. A source stalk is also a normal ring by `lem-weil-pbc-localization-normal-domain`.
   Any strict henselization (`def-sc-ring-strict-henselization`) is a pointed-etale colimit
   with essentially small filtered index (`lem-sc-pointed-etale-small-filtered`) and local
   vertex (`lem-sc-ring-strict-henselization-local-maximal-ideal`). By clause (a) of
   `lem-weil-pbc-etale-colimit-normal-local-domain` it is a normal domain. Its spectrum is
   integral by `lem-weil-pbc-spec-domain-stalks-function-field`, hence irreducible by
   `def-pc-integral-scheme`. This is geometric unibranchness at every point.
5. Given an irreducible component and one of its points, choose an affine Noetherian
   neighbourhood. Its stalks are normal by step 3. Clause (2) of `rem-pc-regular-normal`
   makes its components disjoint and clopen. The intersection of the global component
   with this neighbourhood is a component by `lem-sc-components-open-injection`, hence
   open. These intersections cover the global component, so it is open; it is closed by
   `def-weil-irreducible-components`.
6. Two global components meeting at a point restrict to the same component in an affine
   neighbourhood, by the disjointness in `rem-pc-regular-normal`. The injectivity in
   `lem-sc-components-open-injection` identifies them. Thus distinct components are disjoint.
7. Choose a point in a nonempty connected component and an irreducible component through
   it (`lem-sc-irreducible-components-cover`). The latter is clopen by step 5, so
   connectedness forces the former into it (`def-weil-connected-scheme`). Irreducibility
   implies connectedness (`def-weil-irreducible-components`), and maximality gives equality.
   Therefore the connected component is irreducible and clopen. If the source is empty,
   there are no points or nonempty components, and every assertion is vacuous. -/
theorem normal_etale_components_clopen
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (q : Z ⟶ X) [Etale q] :
    (∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ TopologicalSpace.NoetherianSpace U) ∧
    (∀ (z : Z) (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Z.presheaf.stalk z)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Z.presheaf.stalk z)) K]
      [Algebra (Z.presheaf.stalk z) K]
      [IsScalarTower (Z.presheaf.stalk z)
        (IsLocalRing.ResidueField (Z.presheaf.stalk z)) K]
      [CommRing H] [Algebra (Z.presheaf.stalk z) H],
      Algebra.StrictHenselizationPresentationIn.{u, v} (Z.presheaf.stalk z) K H →
        IrreducibleSpace (PrimeSpectrum H)) ∧
    (∀ C : Set Z, C ∈ irreducibleComponents Z → IsClopen C) ∧
    (∀ C : Set Z, Maximal IsConnected C → IsIrreducible C ∧ IsClopen C) := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have hn := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain q hnormal
  have hirr (z : Z) : IsIrreducible (connectedComponent z) := by
    let U : Z.Opens := ⟨connectedComponent z, isOpen_connectedComponent⟩
    have : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    have hd (w : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk w) := by
      let e := (asIso (U.ι.stalkMap w)).commRingCatIsoToRingEquiv
      have := (hn (U.ι w)).1
      exact e.symm.injective.isDomain e.symm.toRingHom
    have : IrreducibleSpace U.toScheme := irreducibleSpace_of_isDomain_stalk _ hd
    change IsIrreducible (U : Set Z)
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using
      (IrreducibleSpace.isIrreducible_univ U.toScheme).image U.ι U.ι.continuous.continuousOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨U, hU, hzU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Z) (x := z) (U := ⊤) trivial
    have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨U, hzU, noetherianSpace_of_isAffineOpen U hU⟩
  · intro z K H _ _ _ _ _ _ _ P
    have := (hn z).1
    have := (hn z).2
    have := strictPresentation_domain (Z.presheaf.stalk z) K H P
    infer_instance
  · intro C hC
    obtain ⟨z, hz⟩ := hC.1.nonempty
    have hsub := hC.1.isConnected.isPreconnected.subset_isClopen
      (isClopen_connectedComponent (x := z)) ⟨z, hz, mem_connectedComponent⟩
    have heq := Set.Subset.antisymm hsub (hC.2 (hirr z) hsub)
    rw [heq]
    exact isClopen_connectedComponent
  · intro C hC
    obtain ⟨z, hz⟩ := hC.1.nonempty
    have hsub := hC.1.isPreconnected.subset_isClopen
      (isClopen_connectedComponent (x := z)) ⟨z, hz, mem_connectedComponent⟩
    have heq := Set.Subset.antisymm hsub (hC.2 isConnected_connectedComponent hsub)
    rw [heq]
    exact ⟨hirr z, isClopen_connectedComponent⟩

end AlgebraicGeometry
