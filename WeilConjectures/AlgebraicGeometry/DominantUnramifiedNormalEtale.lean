/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism

import Mathlib.Topology.Sober
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.RingTheory.PointedEtaleSmallFiltered
import WeilConjectures.AlgebraicGeometry.NormalGeometricallyUnibranch
import WeilConjectures.AlgebraicGeometry.PointwiseUnramifiedDominantEtale
import WeilConjectures.AlgebraicGeometry.EtaleDominantComponentClopen

/-! # Dominant unramified morphisms to normal integral schemes

Source: Stacks Project, Tag 0GS9, lemma-global-unramified-dominant-unibranch-is-etale,
specialized using Tag 0BQ3, lemma-normal-geometrically-unibranch
(blueprint: lem-dl-a1-dominant-unramified-normal-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A connected scheme unramified over a normal integral scheme is étale and irreducible
if one of its irreducible components has dense image.

Source: Stacks Project, Tags 0GS9 and 0BQ3
(blueprint: lem-dl-a1-dominant-unramified-normal-etale).

Proof plan:
1. The local rings of `X` are normal domains, so `X` is geometrically unibranch by
   `lem-dl-a1-normal-geometrically-unibranch` (Tag 0BQ3).
2. Choose the component `C` with dense image and its generic point `ξ`. Continuity implies
   that the closure of `f(ξ)` contains `f(C)`, so `f(ξ)` is the generic point of `X`.
   For every `z ∈ C`, `ξ` specializes to `z`. The unramified hypothesis includes locally
   finite type. Apply `lem-dl-a1-pointwise-unramified-dominant-etale` (Tag 0GS8) to see that
   `f` is étale at each point of `C`.
3. Let `U` be the union of the open subsets where `f` is étale. Étaleness is local on the
   source, so `U → X` is étale. We have `C ⊆ U`, and `C` is an irreducible component of `U`:
   the closure in `Z` of an irreducible subset of `U` containing `C` must equal `C` by its
   maximality in `Z`. Apply `lem-dl-a1-etale-dominant-component-clopen` to conclude that
   `C` is open and closed in `U`. Thus it is open in `Z`, and it is closed in `Z` because
   it is an irreducible component.
4. The component `C` is nonempty, and `Z` is connected. Hence `C = Z`, giving
   irreducibility of `Z`; also `U = Z`, giving étaleness of `f`.
-/
theorem dominant_unramified_normal_etale
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsIntegral X]
    (hnormal : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    [ConnectedSpace Z]
    (hdominant : ∃ C : Set Z, C ∈ irreducibleComponents Z ∧ Dense (f '' C))
    (hunramified : IsUnramified f) :
    Etale f ∧ IrreducibleSpace Z := by
  classical
  have : LocallyOfFiniteType f := hunramified.1
  have : IsOpenImmersion (Limits.pullback.diagonal f) := hunramified.2
  obtain ⟨C, hC, hdense⟩ := hdominant
  have hCclosed := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 hCclosed
  have hξf : IsGenericPoint (f ξ) Set.univ := by
    simpa only [hdense.closure_eq] using hξ.image f.continuous
  have hpoint : ∀ z ∈ C, ∃ U : Z.Opens, z ∈ U ∧ Etale (U.ι ≫ f) := by
    intro z hz
    let A := X.presheaf.stalk (f z)
    let K := SeparableClosure (IsLocalRing.ResidueField A)
    let : Algebra A K := ((algebraMap (IsLocalRing.ResidueField A) K).comp
      (algebraMap A (IsLocalRing.ResidueField A))).toAlgebra
    have : IsScalarTower A (IsLocalRing.ResidueField A) K := by
      apply IsScalarTower.of_algebraMap_eq'
      rfl
    let J := ObjectProperty.FullSubcategory
      (fun S : Over (CommAlgCat.of A K) ↦ Algebra.Etale A S.left)
    have : EssentiallySmall.{u} J := (Algebra.pointedEtale_small_filtered A K).1
    have : Limits.HasColimitsOfShape J (CommAlgCat.{u} A) :=
      Limits.hasColimitsOfShape_of_essentiallySmall J (CommAlgCat.{u} A)
    let D := Algebra.strictHenselizationPointedDiagramIn.{u, u} A K
    let H := Limits.colimit D
    let P : Algebra.StrictHenselizationPresentationIn.{u, u} A K H :=
      { cocone := Limits.colimit.cocone D
        isColimit := Limits.colimit.isColimit D
        identification := Iso.refl _ }
    have : IrreducibleSpace (PrimeSpectrum H) :=
      normal_geometrically_unibranch X hnormal (f z) K H P
    apply etale_at_of_pointwise_unramified_dominant f z K H P
    · exact ⟨ξ, hξ.specializes hz, hξf⟩
    · have : FormallyUnramified ((⊤ : Z.Opens).ι ≫ f) :=
        IsZariskiLocalAtSource.comp (P := @FormallyUnramified)
          (inferInstanceAs (FormallyUnramified f)) _
      exact ⟨⊤, trivial, inferInstance, inferInstance⟩
  let I := {V : Z.Opens // Etale (V.ι ≫ f)}
  let V : I → Z.Opens := Subtype.val
  let U : Z.Opens := ⨆ i, V i
  have hCU : C ⊆ (U : Set Z) := by
    intro z hz
    obtain ⟨W, hzW, hW⟩ := hpoint z hz
    exact (le_iSup V ⟨W, hW⟩) hzW
  have hU : Etale (U.ι ≫ f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (Scheme.Opens.iSupOpenCover V)
    intro i
    change Etale (Z.homOfLE (le_iSup V i) ≫ (⨆ i, V i).ι ≫ f)
    rw [← Category.assoc, Scheme.homOfLE_ι]
    exact i.2
  have hCUcomp : U.ι ⁻¹' C ∈ irreducibleComponents U.toScheme :=
    preimage_mem_irreducibleComponents hC U.ι.isOpenEmbedding
      ⟨ξ, hξ.mem, ⟨⟨ξ, hCU hξ.mem⟩, rfl⟩⟩
  let ξU : U.toScheme := ⟨ξ, hCU hξ.mem⟩
  have hξU : IsGenericPoint ξU (U.ι ⁻¹' C) := by
    rw [IsGenericPoint, U.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image,
      Set.image_singleton]
    exact congrArg (fun S ↦ U.ι ⁻¹' S) hξ.def
  have hcl : IsClopen (U.ι ⁻¹' C) :=
    etale_dominant_component_clopen.{u, u} (normal_geometrically_unibranch X hnormal)
      (U.ι ≫ f) (U.ι ⁻¹' C) hCUcomp ξU hξU (hξf.eq (genericPoint_spec X))
  have himage : U.ι '' (U.ι ⁻¹' C) = C := by
    apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
    intro z hz
    exact ⟨⟨z, hCU hz⟩, hz, rfl⟩
  have hCopen : IsOpen C := by
    rw [← himage]
    exact U.ι.isOpenEmbedding.isOpenMap _ hcl.isOpen
  have hCuniv : C = Set.univ := (show IsClopen C from ⟨hCclosed, hCopen⟩).eq_univ hC.1.1
  have hUtop : U = ⊤ := by
    apply top_unique
    intro z _
    exact hCU (hCuniv.symm ▸ Set.mem_univ z)
  constructor
  · have htop : Etale ((⊤ : Z.Opens).ι ≫ f) := hUtop ▸ hU
    have : Etale (Z.topIso.inv ≫ ((⊤ : Z.Opens).ι ≫ f)) := inferInstance
    simpa only [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] using this
  · apply (irreducibleSpace_def Z).mpr
    change IsIrreducible (Set.univ : Set Z)
    exact hCuniv ▸ hC.1

end AlgebraicGeometry
