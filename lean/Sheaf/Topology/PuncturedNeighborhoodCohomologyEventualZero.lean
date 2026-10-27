/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.Topology.PuncturedNeighborhoodCohomologyDiagram
public import Mathlib.Topology.Spectral.Basic
import Sheaf.Topology.PuncturedNeighborhoodCoefficientPresentation
import Sheaf.Topology.SpectralLimitCohomologyEventualZero

/-! # Elementwise punctured-neighborhood cohomology continuity -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat

attribute [local irreducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem objectPullback_normalized {X Y : TopCat.{u}} (f : X ⟶ Y) :
    @SiteCohomologyFamily.IsPullback _ _ _ _ (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f) inferInstance
      (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)) (Functor.additive_of_preserves_binary_products _))
      inferInstance inferInstance (objectCohomologyPullback f) :=
  Classical.choose_spec (CategoryTheory.siteCohomology_pullback_exists
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) (Opens.map f))

private theorem zero_of_square {A B C D : AddCommGrpCat.{u}}
    (l : A ⟶ B) (r : A ⟶ C) (t : B ⟶ D) (s : C ⟶ D)
    (h : l ≫ t = r ≫ s) (x : A) (hx : l.hom x = 0) : s.hom (r.hom x) = 0 := by
  exact (ConcreteCategory.congr_hom h x).symm.trans
    ((congrArg t.hom hx).trans (map_zero t.hom))

private theorem zero_of_square_iso {A B C D : AddCommGrpCat.{u}}
    (l : A ⟶ B) (r : A ⟶ C) (t : B ≅ D) (s : C ⟶ D)
    (h : l ≫ t.hom = r ≫ s) (x : A) (hx : s.hom (r.hom x) = 0) :
    l.hom x = 0 := by
  apply t.addCommGroupIsoToAddEquiv.injective
  exact (ConcreteCategory.congr_hom h x).trans (hx.trans (map_zero t.hom.hom).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_spectral_eventual_zero
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → (S j ⟶ S i))
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ i : I, f i i le_rfl = 𝟙 (S i))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f j k hjk ≫ f i j hij = f i k (hij.trans hjk))
    (X : TopCat.{u}) [SpectralSpace X] (p : ∀ i : I, X ⟶ S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j), p j ≫ f i j h = p i)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : X.str = ⨅ i : I, TopologicalSpace.induced (p i) (S i).str)
    (F : ∀ i : I, (S i).Sheaf AddCommGrpCat.{u})
    (α : ∀ (i j : I) (h : i ≤ j),
      F i ⟶ (Sheaf.pushforward AddCommGrpCat.{u} (f i j h)).obj (F j))
    (hαid : ∀ (i : I) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i i le_rfl).hom.app (op U) s) s)
    (hαcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i k (hij.trans hjk)).hom.app (op U) s)
        ((α j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
          ((α i j hij).hom.app (op U) s)))
    (P : I ⥤ X.Sheaf AddCommGrpCat.{u}) [HasColimit P]
    (eP : ∀ i : I, P.obj i ≅
      (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i))
    (hP : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq (((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom).hom.app
          (op ((Opens.map (p i)).obj U))
        (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
            (F i)).hom.app (op U) s))
        (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
            (F j)).hom.app (op ((Opens.map (f i j h)).obj U))
              ((α i j h).hom.app (op U) s)))
    (q : ℕ) (i : I) (x : CategoryTheory.Sheaf.H' (F i) q ⊤)
    (hx : (Sheaf.spectralLimitCohomologyMap (p i) (objectCohomologyPullback (p i))
      ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
          (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) q).hom x = 0) :
    ∃ (j : I) (h : i ≤ j),
      (Sheaf.spectralLimitCohomologyMap (f i j h)
        (objectCohomologyPullback (f i j h)) (α i j h) q).hom x = 0 := by
  exact Sheaf.spectralLimit_cohomology_eventual_zero S f hf hfid hfcomp X p hpcomp
    hlimit htop F α hαid hαcomp P eP hP
    (fun i j h ↦ objectCohomologyPullback (f i j h))
    (fun i j h ↦ objectPullback_normalized (f i j h))
    (fun i ↦ objectCohomologyPullback (p i))
    (fun i ↦ objectPullback_normalized (p i)) q i x hx

attribute [local irreducible] objectCohomologyPullback
  Sheaf.spectralLimitCohomologyMap puncturedNeighborhoodCohomologyDiagram
  puncturedNeighborhoodCohomologyCocone

set_option backward.isDefEq.respectTransparency false in

/-- A class that restricts to zero on the punctured generalizations vanishes on a
smaller punctured compact open neighborhood.
Source: Stacks Project, Cohomology, Tags 0A3D(2) and 0A37.
(blueprint: lem-weil-pbc-punctured-neighborhood-cohomology-eventual-zero)

Proof: Use reverse inclusion on compact open neighborhoods of Z. Their punctures are
compact open spectral spaces, the inclusions are spectral, and their inverse limit is the
punctured generalization subspace. For the intersection assertion, exclude any point whose
closure misses Z by a finite union of compact basis opens covering Z inside that closure's
complement. The coordinate indexed by the whole ambient space gives the initial topology.
Restrict A to the stages. Unit-compatible inverse-image composition identifies the
pullbacks with the fixed inverse image of A on the limit, so this is also their coefficient
colimit. Open-subspace cohomology is object cohomology of A on that open: restrict an
injective resolution, using exact extension by zero to preserve injectivity. Under these
identifications the canonical maps are precisely the specified diagram and cocone maps,
by the normalized pullback delta-functor's uniqueness. Apply the eventual-zero half of
cohomological continuity (0A37) to the class whose image is zero. The resulting later stage
is exactly a smaller compact open neighborhood and gives the claimed morphism and equation. -/
theorem puncturedNeighborhood_cohomology_eventual_zero
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
    (N : (compactOpenNeighborhoods Z)ᵒᵖ)
    (x : (puncturedNeighborhoodCohomologyDiagram Z hZ A q).obj N)
    (hx : ((puncturedNeighborhoodCohomologyCocone Z hZ A q).ι.app N).hom x = 0) :
    ∃ (M : (compactOpenNeighborhoods Z)ᵒᵖ) (f : N ⟶ M),
      ((puncturedNeighborhoodCohomologyDiagram Z hZ A q).map f).hom x = 0 := by
  classical
  obtain ⟨d⟩ := puncturedNeighborhood_coefficient_presentation Z hZ A q
  let I := puncturedNeighborhoodIndex Z
  let S : I → TopCat.{u} := puncturedNeighborhoodSpace Z hZ
  let f : ∀ i j : I, i ≤ j → (S j ⟶ S i) := puncturedNeighborhoodTransition Z hZ
  let X : TopCat.{u} := TopCat.of (puncturedGeneralizations Z)
  let p : ∀ i : I, X ⟶ S i := puncturedNeighborhoodProjection Z hZ
  let i : I := OrderDual.toDual (unop N)
  let : Nonempty I := puncturedNeighborhoodIndex_nonempty Z
  let : IsDirected I (· ≤ ·) := puncturedNeighborhoodIndex_directed Z
  let : ∀ j : I, SpectralSpace (S j) := puncturedNeighborhoodSpace_spectral Z hZ hU
  have hf (j k : I) (h : j ≤ k) : IsSpectralMap (f j k h) :=
    puncturedNeighborhoodTransition_spectral Z hZ hU j k h
  have hfid (j : I) : f j j le_rfl = 𝟙 (S j) := TopCat.ext fun _ ↦ Subtype.ext rfl
  have hfcomp (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l) :
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl) :=
    TopCat.ext fun _ ↦ Subtype.ext rfl
  have hpcomp (j k : I) (h : j ≤ k) : p k ≫ f j k h = p j :=
    TopCat.ext fun _ ↦ Subtype.ext rfl
  obtain ⟨hlimit, htop⟩ := puncturedNeighborhood_topologicalLimit Z hZ
  have : SpectralSpace X := puncturedGeneralizations_spectral Z hZ hU
  let : HasColimit d.P := d.hasColimit
  have hz := zero_of_square _ _ _ _ (d.leg_compat i) x hx
  obtain ⟨j, hij, hj⟩ := canonical_spectral_eventual_zero S f hf hfid hfcomp
    X p hpcomp hlimit htop d.F d.α d.alpha_id d.alpha_comp d.P d.eP d.pullback_compat
      q i ((d.eH i).hom.hom x) hz
  let g : N ⟶ op (OrderDual.ofDual j) :=
    (homOfLE (show OrderDual.ofDual j ≤ unop N from hij)).op
  refine ⟨op (OrderDual.ofDual j), g, ?_⟩
  exact zero_of_square_iso _ _ _ _ (d.map_compat i j hij) x hj


end TopCat
