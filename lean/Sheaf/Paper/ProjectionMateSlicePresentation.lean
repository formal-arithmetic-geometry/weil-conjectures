/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedTensorEdgeInducedAdjunction
import all Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.Paper.SheafSliceDerivedComparison
import Sheaf.CategoryTheory.ElementRestrictionHom
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Local presentations of the canonical projection mate

Source: Stacks Project, Cohomology on Sites, Tag 0944, the locality argument;
Modules on Sites, Tag 04IF
(blueprint: lem-sbc-projection-mate-slice-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w w'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The coefficient category on the ordinary site-object slice. This abbreviates the
existing category without choosing any data. Source: Stacks 04IF
(blueprint: lem-sbc-projection-mate-slice-presentation). -/
abbrev projectionSliceModules (Y : RingedTensorCorner.{u, w}) (U : Y.site) :=
  SheafOfModules.{u} (((sheafCompose Y.topology
    (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring).over U)

/-- Exact restriction of the ordinary unbounded derived category.
Source: Stacks 04IF (blueprint: lem-sbc-projection-mate-slice-presentation). -/
noncomputable abbrev projectionSliceRestriction (Y : RingedTensorCorner.{u, w})
    (U : Y.site) [HasDerivedCategory.{w'} (projectionSliceModules Y U)] :
    Y.mateDerived ⥤ DerivedCategory (projectionSliceModules Y U) :=
  (localizedSystemRestriction.{u, u, u} Y.ring U).mapDerivedCategory

/-- A local exact presentation of a projection mate, including the equation of actual
arrows. The coefficient is arbitrary; perfectness is not part of these data.
Source: Stacks 04IF and 0944
(blueprint: lem-sbc-projection-mate-slice-presentation). -/
structure ProjectionMateSlicePresentation
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) (E : X.mateDerived)
    (U : Y.site) [HasDerivedCategory.{w'} (projectionSliceModules Y U)] where
  source : DerivedCategory (projectionSliceModules Y U) ⥤
    DerivedCategory (projectionSliceModules Y U)
  target : DerivedCategory (projectionSliceModules Y U) ⥤
    DerivedCategory (projectionSliceModules Y U)
  [sourceShift : source.CommShift ℤ]
  [targetShift : target.CommShift ℤ]
  sourceExact : source.IsTriangulated
  targetExact : target.IsTriangulated
  mate : source ⟶ target
  shiftCompatible : NatTrans.CommShift mate ℤ
  sourceComparison : (Functor.curryObj Y.tensor).obj (e.right.obj E) ⋙
      projectionSliceRestriction Y U ≅ projectionSliceRestriction Y U ⋙ source
  targetComparison : (e.left ⋙ (Functor.curryObj X.tensor).obj E ⋙ e.right) ⋙
      projectionSliceRestriction Y U ≅ projectionSliceRestriction Y U ⋙ target
  equation (P : Y.mateDerived) :
    (projectionSliceRestriction Y U).map (e.projection a b E P) ≫
        targetComparison.hom.app P =
      sourceComparison.hom.app P ≫ mate.app ((projectionSliceRestriction Y U).obj P)

private theorem edge_left_derived_comparison
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (F : Y.mateModules ⥤ X.mateModules) [F.Additive] (i : e.pullback ≅ F)
    (L : Y.mateDerived ⥤ X.mateDerived)
    (eps : DerivedCategory.Q ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor eps (HomologicalComplex.quasiIso Y.mateModules (.up ℤ))] :
    ∃ t : e.left ≅ L, ∀ K : CochainComplex Y.mateModules ℤ,
      t.hom.app (DerivedCategory.Q.obj K) ≫ eps.app K =
        e.epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app K) := by
  have := e.isLeftDerived
  obtain ⟨epsc, hc, hrep⟩ := CategoryTheory.leftDerivedOnComplexes e.pullback
    (𝟭 X.mateDerived) e.left e.epsilon
  have := hc
  let j := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex i (.up ℤ)) DerivedCategory.Q
  let t := Functor.leftDerivedNatIso e.left L epsc eps
    (HomologicalComplex.quasiIso Y.mateModules (.up ℤ)) j
  refine ⟨t, ?_⟩
  intro K
  simpa only [t, Functor.leftDerivedNatIso_hom, j,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, hrep K] using
    Functor.leftDerivedNatTrans_app e.left L epsc eps
    (HomologicalComplex.quasiIso Y.mateModules (.up ℤ)) j.hom K

private theorem derived_counit_comparison
    {A B : Type*} [Category A] [Category B] {L L' : A ⥤ B} {R R' : B ⥤ A}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (t : L ≅ L') :
    ∃ r : R ≅ R', ∀ E : B,
      L.map (r.hom.app E) ≫ t.hom.app (R'.obj E) ≫ adj'.counit.app E =
        adj.counit.app E := by
  let r := conjugateIsoEquiv adj adj' t.symm
  refine ⟨r, ?_⟩
  intro E
  rw [reassoc_of% (t.hom.naturality (r.hom.app E))]
  have h : L'.map (r.hom.app E) ≫ adj'.counit.app E =
      t.inv.app (R.obj E) ≫ adj.counit.app E :=
    conjugateEquiv_counit adj adj' t.inv E
  rw [h]
  simp

/-- The counit projection mate admits an exact local presentation on
any ordinary site-object slice, with its actual restriction equation.

Source: Stacks Project, Modules on Sites, Tag 04IF; Cohomology on Sites, Tag 0944,
first sentence of the proof and the subsequent projection/base-change compatibility
(blueprint: lem-sbc-projection-mate-slice-presentation).

Proof:
1. Use RingedTensorEdge.inducedModuleAdjunction to construct the induced ringed morphism
   and identify its module right adjoint, preserving unit and counit. The proved helpers
   edge_left_derived_comparison and derived_counit_comparison identify the derived
   models, with the comparison fixed on every complex, and preserve their counit.
   Replace the ordinary slice at U by the element site of the sheafified representable,
   using element_restriction_hom. On the source use the inverse image of that sheaf.
   ringedSheafSliceDerivedComparison supplies the induced ringed morphism, its exact
   restrictions, the pullback comparison theta and its invertible exchange mate beta.
2. On the two slice module categories use flat-term K-flat derived tensor and the
   K-flat/K-injective derived adjunction. These local derived models may have a different
   Hom universe. Work first in a common universe at least as large as both specified
   universes and u+1; localization uniqueness gives equivalences with each specified
   model, compatible with Q, exact restriction and shifts. Perform the slice construction
   there and transport the resulting functors and equation back through these equivalences.
   The module equivalence of step 1 transports them to the ordinary slice.
3. Fix the restricted source object E_U. Put F_U(Q)=R_U(E_U) tensor Q and
   G_U(Q)=R_U(E_U tensor L_U(Q)). ringedProjectionMateExact supplies their shift structures,
   exactness and shift-compatible counit mate.
4. Restriction/tensor comparison and beta identify restriction of the global source
   functor with F_U after restriction. Beta and theta identify the target functor with
   G_U after restriction. These are natural isomorphisms on every coefficient object.
5. Apply ringedExchangeTensorCoherence to the ringed slice square. Its equality of
   projectionFirst and exchangeFirst is exactly the displayed equation after composing
   with the inverses of the comparisons just described. Transport through the ordinary
   slice equivalence preserves that equation and all triangulated structures.
   No perfectness or boundedness hypothesis is involved. -/
theorem projectionMateSlicePresentation
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) (E : X.mateDerived)
    (U : Y.site) [HasDerivedCategory.{w'} (projectionSliceModules Y U)] :
    Nonempty (ProjectionMateSlicePresentation e a b E U) := by
  sorry

end SheafOfModules
