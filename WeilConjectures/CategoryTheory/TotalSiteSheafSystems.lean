/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TotalSitePseudofunctor
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaves on a coherent total site as compatible systems

Source: Stacks Project, `spaces-simplicial.tex`, Tags 09WC and 09WF, Case A and the
compatible-family discussion (blueprint: lem-trf-slice-site-total-systems).

The inverse images are the sheafified left Kan extensions. Their comparisons are
mates of the supplied pseudofunctor comparisons, not arbitrary natural isomorphisms.
The presentation below states full faithfulness and essential surjectivity onto all
compatible systems, with the restriction and transition formulas fixing the functor.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory
namespace CoherentSitePseudofunctor

variable {I : Type u} [Category.{v} I]
  {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)

/-- Fibre sheaves of sets. Source: Stacks, Tag 09WF
(blueprint: lem-trf-slice-site-total-systems). -/
abbrev fibreSheaves (i : I) := Sheaf (D.coverage i).toGrothendieck (Type w)

/-- Direct image is precomposition with the continuous transition functor.
Source: Stacks, Tags 00WW and 09WF (blueprint: lem-trf-slice-site-total-systems). -/
def directImage {i j : I} (α : i ⟶ j) : D.fibreSheaves i ⥤ D.fibreSheaves j :=
  letI := D.continuous α
  (F.map α.op.toLoc).toFunctor.sheafPushforwardContinuous (Type w)
    (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- Inverse image is the sheafified left Kan extension, as in the recorded sheaf
adjunction dependency. Source: Stacks, Tags 00WX and 09WF
(blueprint: lem-trf-slice-site-total-systems). -/
noncomputable def inverseImage {i j : I} (α : i ⟶ j) :
    D.fibreSheaves j ⥤ D.fibreSheaves i :=
  letI := D.continuous α
  Functor.sheafPullbackConstruction.sheafPullback (F.map α.op.toLoc).toFunctor
    (Type w) (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- The actual sheafified-Kan-extension adjunction. Source: Stacks, Tag 00WX
(blueprint: lem-trf-slice-site-total-systems). -/
noncomputable def imageAdjunction {i j : I} (α : i ⟶ j) :
    D.inverseImage α ⊣ D.directImage α :=
  letI := D.continuous α
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (F.map α.op.toLoc).toFunctor (Type w)
    (D.coverage j).toGrothendieck (D.coverage i).toGrothendieck

/-- Direct-image unitor induced by the supplied site unitor.
Source: Stacks, Tags 09WC and 09WF (blueprint: lem-trf-slice-site-total-systems). -/
noncomputable def directImageId (i : I) : D.directImage (𝟙 i) ≅ 𝟭 _ :=
  letI : Functor.IsContinuous (F.map (𝟙 ⟨op i⟩)).toFunctor
      (D.coverage i).toGrothendieck (D.coverage i).toGrothendieck := D.continuous (𝟙 i)
  Functor.sheafPushforwardContinuousId' (Cat.Hom.toNatIso (F.mapId ⟨op i⟩))
    (Type w) (D.coverage i).toGrothendieck

/-- Direct-image compositor induced by the inverse of `F.mapComp`.
Source: Stacks, Tags 09WC and 09WF (blueprint: lem-trf-slice-site-total-systems). -/
noncomputable def directImageComp {i j k : I} (α : i ⟶ j) (β : j ⟶ k) :
    D.directImage α ⋙ D.directImage β ≅ D.directImage (α ≫ β) :=
  letI := D.continuous α
  letI := D.continuous β
  letI : Functor.IsContinuous (F.map (β.op.toLoc ≫ α.op.toLoc)).toFunctor
      (D.coverage k).toGrothendieck (D.coverage i).toGrothendieck := D.continuous (α ≫ β)
  Functor.sheafPushforwardContinuousComp'
    (Cat.Hom.toNatIso (F.mapComp β.op.toLoc α.op.toLoc).symm)
    (Type w) (D.coverage k).toGrothendieck (D.coverage j).toGrothendieck
    (D.coverage i).toGrothendieck

/-- Canonical adjunction-compatible inverse-image unitor, defined by mates.
Source: Stacks, Tags 09WC and 09WF (blueprint: lem-trf-slice-site-total-systems). -/
noncomputable def inverseImageId (i : I) : D.inverseImage (𝟙 i) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso (D.imageAdjunction (𝟙 i)) (D.directImageId i)

/-- Canonical adjunction-compatible inverse-image compositor, defined by mates.
Source: Stacks, Tags 09WC and 09WF (blueprint: lem-trf-slice-site-total-systems). -/
noncomputable def inverseImageComp {i j k : I} (α : i ⟶ j) (β : j ⟶ k) :
    D.inverseImage β ⋙ D.inverseImage α ≅ D.inverseImage (α ≫ β) :=
  Adjunction.leftAdjointCompIso (D.imageAdjunction β) (D.imageAdjunction α)
    (D.imageAdjunction (α ≫ β)) (D.directImageComp α β)

/-- A compatible system, with arbitrary (not necessarily invertible) transition maps.
Source: Stacks, Tag 09WF and its preceding discussion; the identity and composition
laws insert the canonical adjunction-compatible comparisons
(blueprint: lem-trf-slice-site-total-systems). -/
structure SheafSystem where
  obj : ∀ i : I, D.fibreSheaves i
  transition : ∀ {i j : I} (α : i ⟶ j), (D.inverseImage α).obj (obj j) ⟶ obj i
  transition_id : ∀ i : I, transition (𝟙 i) = (D.inverseImageId i).hom.app (obj i)
  transition_comp : ∀ {i j k : I} (α : i ⟶ j) (β : j ⟶ k),
    (D.inverseImageComp α β).hom.app (obj k) ≫ transition (α ≫ β) =
      (D.inverseImage α).map (transition β) ≫ transition α

/-- Morphisms of systems are exactly compatible component maps. Identities and
composition are componentwise. Source: Stacks, Tag 09WF
(blueprint: lem-trf-slice-site-total-systems). -/
structure SheafSystemHom (X Y : D.SheafSystem) where
  app : ∀ i : I, X.obj i ⟶ Y.obj i
  comm : ∀ {i j : I} (α : i ⟶ j),
    (D.inverseImage α).map (app j) ≫ Y.transition α = X.transition α ≫ app i

/-- The full-faithfulness and essential-surjectivity presentation of the system
category. `restriction` and `map_restriction` fix fibre restriction on objects and
morphisms; `transition_restriction` fixes its transition as the adjoint of restriction
along the Cartesian lift `(α,id)`. `map_bijective` ranges over ALL compatible maps;
`essentially_surjective` ranges over ALL systems. Thus these are the equivalence
criterion with its specified evaluation functors, rather than an arbitrary category
carrying some transitions. `HEq` only compares restriction maps whose endpoints
are identified by the preceding presheaf equality.
Source: Stacks, Tag 09WF (blueprint: lem-trf-slice-site-total-systems). -/
structure SheafSystemPresentation where
  system : Sheaf D.totalTopology (Type w) → D.SheafSystem
  restriction : ∀ (X : Sheaf D.totalTopology (Type w)) (i : I),
    ((system X).obj i).obj = (Pseudofunctor.CoGrothendieck.ι F i).op ⋙ X.obj
  map : ∀ {X Y : Sheaf D.totalTopology (Type w)},
    (X ⟶ Y) → D.SheafSystemHom (system X) (system Y)
  map_restriction : ∀ {X Y : Sheaf D.totalTopology (Type w)} (h : X ⟶ Y) (i : I),
    HEq ((map h).app i).hom (Functor.whiskerLeft (Pseudofunctor.CoGrothendieck.ι F i).op h.hom)
  transition_restriction : ∀ (X : Sheaf D.totalTopology (Type w)) {i j : I}
    (α : i ⟶ j) (V : F.obj ⟨op j⟩),
    HEq (((D.imageAdjunction α).homEquiv _ _ ((system X).transition α)).hom.app (op V))
      (X.obj.map (Pseudofunctor.CoGrothendieck.cartesianLift V α).op)
  map_bijective : ∀ X Y : Sheaf D.totalTopology (Type w),
    Function.Bijective (map (X := X) (Y := Y))
  essentially_surjective : ∀ S : D.SheafSystem,
    ∃ (X : Sheaf D.totalTopology (Type w)) (e : ∀ i : I, (system X).obj i ≅ S.obj i),
      ∀ {i j : I} (α : i ⟶ j),
        (D.inverseImage α).map (e j).hom ≫ S.transition α =
          (system X).transition α ≫ (e i).hom

/-- Sheaves on the generated total site are equivalent to all compatible systems,
with fibre restriction and componentwise compatible morphisms as specified above.
Each inverse image preserves finite limits, exactly the morphism-of-sites assumption.
No transition map is required to be an isomorphism.
Source: Stacks, Tags 09WC and 09WF, Case A and the preceding compatible-family
construction (blueprint: lem-trf-slice-site-total-systems).

Proof: (1) Precomposition gives the direct images and the recorded sheafified-Kan
adjunction gives their left adjoints. The site unitors and compositors induce the
right-adjoint comparisons; taking mates gives precisely `inverseImageId` and
`inverseImageComp`. The adjoint-composition coherence lemma gives their coherence.
(2) Transpose each transition under `imageAdjunction`. The inverse-image identity
and cocycle become the direct-image identity and cocycle by the unit equation for
mates and the composite adjunction Hom bijection. The same bijection converts
compatibility of component maps. (3) Restrict a total sheaf along each vertical
embedding. Its sheaf condition follows by extending a fibre matching family to
the generated total sieve and gluing there, using covering pullbacks only.
(4) Restriction along `(α,id)` supplies the adjoint transitions. Naturality and the
CoGrothendieck composition formula give the cocycle, with the actual non-strict
unitors. (5) Conversely a system defines the presheaf with value `F_i(U)` and
restriction `F_i(f)` after the adjoint transition along `(α,f)`. Naturality and
the cocycle prove composition; the unitor cancels in the identity and vertical
restriction formulas. (6) For a pullback of a generating vertical cover, use the
covering pullbacks of `totalSite_of_coherent_pseudofunctor` and glue in the source
fibre. Pulling back that covering again and using fibre separatedness proves the
matching identity at every arrow. The generated-precoverage sheaf criterion gives
the total sheaf condition, also for empty coverings. (7) Compatible component maps
extend uniquely by their components; naturality at `(α,id)` gives the converse.
The two constructions recover objects, arbitrary-arrow restrictions and morphisms,
proving the asserted full faithfulness and essential surjectivity. -/
theorem totalSite_sheaf_systems
    {I : Type u} [Category.{v} I]
    {F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, w}} (D : CoherentSitePseudofunctor I F)
    (h : ∀ (i j : I) (α : i ⟶ j), PreservesFiniteLimits (D.inverseImage α)) :
    Nonempty D.SheafSystemPresentation := by
  sorry

end CoherentSitePseudofunctor
end CategoryTheory
