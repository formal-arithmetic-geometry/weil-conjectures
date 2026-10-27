/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.SfOpenClosedTriangleData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.ExactDerivedAdjunction

/-! # The derived triangle of an exact sheaf localization sequence

The construction retains the two given maps on every complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace WeilConjectures

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (F H : C ⥤ C) [F.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (ε : F ⟶ 𝟭 C) (η : 𝟭 C ⟶ H)

/-- The presentation obtained by localizing the two given termwise maps.
Source: Stacks 0152; blueprint localization, integral sheaf sequence
(blueprint: lem-sf-exact-localization-triangle). -/
abbrev sfExactLocalizationPresentation : SfRecollementPresentation (DerivedCategory C) where
  openTerm := F.mapDerivedCategory.{w,w}
  closedTerm := H.mapDerivedCategory.{w,w}
  counit := Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
    F.mapDerivedCategory.{w,w} (𝟭 _)
    { app := fun B ↦ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ε (.up ℤ)).app B)
      naturality := by
        intro B B' f
        dsimp
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ε (.up ℤ)).naturality f) }
  unit := Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (𝟭 _) H.mapDerivedCategory.{w,w}
    { app := fun B ↦ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex η (.up ℤ)).app B)
      naturality := by
        intro B B' f
        dsimp
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex η (.up ℤ)).naturality f) }

@[reassoc]
theorem sfExactLocalizationPresentation_counit (B : CochainComplex C ℤ) :
    (sfExactLocalizationPresentation F H ε η).counit.app (DerivedCategory.Q.obj B) =
      F.mapDerivedCategoryFactors.hom.app B ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ε (.up ℤ)).app B) := by
  dsimp only [sfExactLocalizationPresentation]
  rw [Localization.liftNatTrans_app]
  change F.mapDerivedCategoryFactors.hom.app B ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]

@[reassoc]
theorem sfExactLocalizationPresentation_unit (B : CochainComplex C ℤ) :
    (sfExactLocalizationPresentation F H ε η).unit.app (DerivedCategory.Q.obj B) ≫
        H.mapDerivedCategoryFactors.hom.app B =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (.up ℤ)).app B) := by
  dsimp only [sfExactLocalizationPresentation]
  rw [Localization.liftNatTrans_app]
  change (𝟙 _ ≫ _ ≫ H.mapDerivedCategoryFactors.inv.app B) ≫
    H.mapDerivedCategoryFactors.hom.app B = _
  simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- A short exact sequence of exact functors gives the indicated distinguished
triangle, with the original maps. Source: Stacks 0152; blueprint localization,
integral sheaf sequence (blueprint: lem-sf-exact-localization-triangle).
Proof: on a complex take the degreewise short exact sequence and its standard
connecting map. The exact-functor factorization isomorphisms identify its first
and third vertices with the derived functor values. Every derived object is
isomorphic to the image of a complex; naturality transports the triangle. -/
theorem sfExactLocalizationPresentation_distinguished
    (hz : ε ≫ η = 0)
    (hs : ∀ M, (ShortComplex.mk (ε.app M) (η.app M)
      (by simpa using congr_app hz M)).ShortExact)
    (K : DerivedCategory C) :
    ∃ δ, Triangle.mk ((sfExactLocalizationPresentation F H ε η).counit.app K)
      ((sfExactLocalizationPresentation F H ε η).unit.app K) δ ∈ distTriang _ := by
  let P := sfExactLocalizationPresentation F H ε η
  have hcomplex (B : CochainComplex C ℤ) :
      ∃ δ, Triangle.mk (P.counit.app (DerivedCategory.Q.obj B))
        (P.unit.app (DerivedCategory.Q.obj B)) δ ∈ distTriang _ := by
    let S : ShortComplex (CochainComplex C ℤ) :=
      ShortComplex.mk ((NatTrans.mapHomologicalComplex ε (.up ℤ)).app B)
        ((NatTrans.mapHomologicalComplex η (.up ℤ)).app B) (by
          ext n
          exact congr_app hz (B.X n))
    have hS : S.ShortExact :=
      HomologicalComplex.shortExact_of_degreewise_shortExact S (fun n ↦ hs (B.X n))
    let a := F.mapDerivedCategoryFactors.app B
    let c := H.mapDerivedCategoryFactors.app B
    let δ := c.hom ≫ DerivedCategory.triangleOfSESδ hS ≫ a.inv⟦(1 : ℤ)⟧'
    refine ⟨δ, isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
      _ (Triangle.isoMk _ _ a (Iso.refl _) c ?_ ?_ ?_)⟩
    · simpa [P, S, a] using
        sfExactLocalizationPresentation_counit F H ε η B
    · simpa [P, S, c] using
        sfExactLocalizationPresentation_unit F H ε η B
    · simp [δ, Category.assoc, ← Functor.map_comp]
  let B := (DerivedCategory.Q (C := C)).objPreimage K
  let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨δ, hδ⟩ := hcomplex B
  refine ⟨P.closedTerm.map e.inv ≫ δ ≫ (P.openTerm.map e.hom)⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hδ _
      (Triangle.isoMk _ _ (P.openTerm.mapIso e.symm) e.symm
        (P.closedTerm.mapIso e.symm) ?_ ?_ ?_)⟩
  · simpa [P] using (P.counit.naturality e.inv).symm
  · simpa [P] using (P.unit.naturality e.inv).symm
  · simp [Category.assoc, ← Functor.map_comp]

/-- The kernel of a reflective localization has no shifted maps to its image.
Source: blueprint localization, disjoint-support paragraph
(blueprint: lem-sf-exact-localization-triangle).
Proof: the left adjoint kills the kernel of its unit, since it preserves kernels
and takes the unit to an isomorphism. Exactness gives the same statement on
complexes and every shift. The derived adjunction identifies the requested Hom
with a Hom whose source is zero. -/
theorem sfExactLocalizationKernel_orthogonality
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory.{w} D]
    (L : C ⥤ D) (R : D ⥤ C) (a : L ⊣ R)
    [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [IsIso a.counit]
    [(kernel a.unit).Additive]
    [PreservesFiniteLimits (kernel a.unit)] [PreservesFiniteColimits (kernel a.unit)]
    (K M : DerivedCategory C) (n : ℤ) :
    Subsingleton (((kernel a.unit).mapDerivedCategory.obj K)⟦n⟧ ⟶
      (L ⋙ R).mapDerivedCategory.obj M) := by
  have : R.Full := a.fullyFaithfulROfIsIsoCounit.full
  have : R.Faithful := a.fullyFaithfulROfIsIsoCounit.faithful
  have hk (N : C) : IsZero (L.obj ((kernel a.unit).obj N)) := by
    let e := L.mapIso (PreservesKernel.iso ((evaluation C C).obj N) a.unit) ≪≫
      PreservesKernel.iso L (a.unit.app N)
    exact (isZero_kernel_of_mono (L.map (a.unit.app N))).of_iso e
  have hz : IsZero (L.mapDerivedCategory.obj
      ((kernel a.unit).mapDerivedCategory.obj K)) := by
    apply L.isZero_mapDerivedCategory_obj
    intro r
    exact (hk ((DerivedCategory.homologyFunctor C r).obj K)).of_iso
      (L.mapIso (((kernel a.unit).mapDerivedCategoryHomologyFunctorIso r).symm.app K))
  have hz' : IsZero (L.mapDerivedCategory.obj
      (((kernel a.unit).mapDerivedCategory.obj K)⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero hz).of_iso
      ((L.mapDerivedCategory.commShiftIso n).app _)
  have : Subsingleton (L.mapDerivedCategory.obj
      (((kernel a.unit).mapDerivedCategory.obj K)⟦n⟧) ⟶ L.mapDerivedCategory.obj M) :=
    ⟨fun _ _ ↦ hz'.eq_of_src _ _⟩
  have hR : Subsingleton (((kernel a.unit).mapDerivedCategory.obj K)⟦n⟧ ⟶
      R.mapDerivedCategory.obj (L.mapDerivedCategory.obj M)) :=
    (Adjunction.homEquiv (a.mapExactDerivedCategory) _ _).symm.subsingleton
  let e := Iso.homCongr (Iso.refl (((kernel a.unit).mapDerivedCategory.obj K)⟦n⟧))
    ((Functor.mapDerivedCategoryCompIso L R).app M)
  exact ⟨fun f g ↦ e.injective (@Subsingleton.elim _ hR (e f) (e g))⟩

end WeilConjectures
