/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.Paper.FiniteDiscreteExchangeRealization
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Finite discrete internal coefficients and etale exchange

Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3
(blueprint: lem-weil-pbc-finite-discrete-exchange-comparison).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor


-- Fix the size bound explicitly to avoid a recursive instance search on this site.
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

private noncomputable def arrowIsoOfObjectIso
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (η : F ⟶ G) {M N : C} (e : M ≅ N) :
    Arrow.mk (η.app M).hom ≅ Arrow.mk (η.app N).hom :=
  Arrow.isoMk (P.ι.mapIso (F.mapIso e)) (P.ι.mapIso (G.mapIso e))
    (congrArg (fun t ↦ t.hom) (η.naturality e.hom))

private theorem nonemptyArrowIsoOfObjectIso
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty D)
    {F G : C ⥤ P.FullSubcategory} (η : F ⟶ G) {M N : C} (e : M ≅ N) :
    Nonempty (Arrow.mk (η.app M).hom ≅ Arrow.mk (η.app N).hom) :=
  ⟨arrowIsoOfObjectIso P η e⟩

-- Bounded devissage is formulated over an abstract abelian category. This avoids
-- reducing the concrete coefficient-module representation when using its API.
private theorem boundedArrowComparison
    {C A D E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category A] [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    [Category D] [Category E]
    (F0 : A ⥤ DerivedCategory C) [F0.CommShift ℤ] [F0.Full] [F0.IsTriangulated]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (Q : ObjectProperty (DerivedCategory C))
    (hQ : ∀ M, Q M ↔ DerivedCategory.TStructure.t.bounded M ∧
      ∀ n, P ((DerivedCategory.homologyFunctor C n).obj M))
    {R : ObjectProperty D} {S T : Q.FullSubcategory ⥤ R.FullSubcategory} (η : S ⟶ T)
    {S' T' : A ⥤ E} (θ : S' ⟶ T') (F1 : E ⥤ D)
    (hsingle : ∀ M, P M → F0.essImage ((DerivedCategory.singleFunctor C 0).obj M))
    (hstep : ∀ L (hL : Q (F0.obj L)),
      Nonempty (Arrow.mk (η.app ⟨F0.obj L, hL⟩).hom ≅ Arrow.mk (F1.map (θ.app L))))
    (N : Q.FullSubcategory) :
    ∃ L, Nonempty (Arrow.mk (η.app N).hom ≅ Arrow.mk (F1.map (θ.app L))) := by
  have horigin : F0.essImage N.obj :=
    DerivedCategory.prop_of_bounded F0.essImage P hsingle N.obj
      ((hQ N.obj).mp N.property).1 ((hQ N.obj).mp N.property).2
  obtain ⟨L, ⟨e⟩⟩ := horigin
  have hL : Q (F0.obj L) := by
    apply (hQ _).mpr
    refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm
      ((hQ N.obj).mp N.property).1, ?_⟩
    intro n
    exact P.prop_of_iso ((DerivedCategory.homologyFunctor C n).mapIso e.symm)
      (((hQ N.obj).mp N.property).2 n)
  let M : Q.FullSubcategory := ⟨F0.obj L, hL⟩
  let eMN : M ≅ N := ObjectProperty.isoMk _ e
  refine ⟨L, ?_⟩
  exact (nonemptyArrowIsoOfObjectIso R η eMN.symm).map2
    (fun p q ↦ p ≪≫ q) (hstep L hL)

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]



/-- Finite discrete internal coefficients compare to the actual etale exchange.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3;
Stacks Project, Tag 09AL
(blueprint: lem-weil-pbc-finite-discrete-exchange-comparison).

Proof in words. A continuous map to the discrete ring B is locally constant, so the
condensed continuous-function ring is the constant ring, and its inverse image on
T is the constant B ring sheaf. Internal modules over this ring and sheaves of
ULift B-modules are identified by retaining the underlying additive sheaf and scalar
action. The supplied hEncoding gives the equivalence from internal modules over the
sheafified constant ring to module-valued sheaves, together with its underlying
abelian sheaf comparison. Transfer along the constant-ring identification. These
inverse constructions are additive and exact, as detected on abelian sheaves.
Derive this equivalence and compose it
with exact etale-to-pro-etale inverse image to obtain the realization functor F.
The realization is full and triangulated. Its essential image contains constructible
sheaves in degree zero, so existing bounded triangulated devissage gives an etale
bounded-below complex L realizing N. Exact inverse image commutes with pullback, while bounded-below
site comparison identifies derived direct image of etale-origin objects with the
pro-etale direct image. Both comparisons come from the same underived adjunctions;
their equations for units, counits, and composition identify the actual exchange maps.
Apply the realization to the etale exchange at L and transport the pro-etale exchange
along the origin isomorphism. This gives the claimed arrow isomorphism. Finiteness and
ℓB = 0 ensure bounded constructible pushforward in the present finite-type setting.
No properness or Cartesian hypothesis is used. Empty schemes and the zero ring give
the same construction with zero objects. -/
theorem finiteDiscreteExchange_comparison
    (hB : (ℓ : B) = 0)
    (sq : CommSq g' f' f g)
    (N : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X))
    (hEncoding : ∀ T : Scheme.{u},
      ∃ G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))) ⥤
            Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B)),
        G.IsEquivalence ∧ Nonempty (G ⋙
          sheafCompose (Scheme.ProEt.topology T)
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ≅
          Mod.forget (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))))) :
    ∃ (F : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} B))) ⥤
        DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) Y')))
      (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} B)))),
      Nonempty (Arrow.mk ((boundedConstructibleBaseChange
          (Profinite.continuousMapRingObj.{u} B) ℓ k sq).app N).hom ≅
        Arrow.mk (F.map ((Etale.baseChange
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L))) := by
  obtain ⟨F0, cs, hfull, htri, hsingle, F1, hsteps⟩ :=
    finiteDiscreteExchange_stepRealization B ℓ k hB sq hEncoding
  let := cs
  let := hfull
  let := htri
  let P : ObjectProperty (FiniteDiscreteInternalModules B X) :=
    ProEtale.IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ _root_.constructible_of_iso e h⟩
  refine ⟨F1, ?_⟩
  refine boundedArrowComparison F0 P
    (ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X))
    (fun _ ↦ Iff.rfl)
    (boundedConstructibleBaseChange (Profinite.continuousMapRingObj.{u} B) ℓ k sq)
    (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq) F1 hsingle ?_ N
  intro L hL
  obtain ⟨H⟩ := hsteps L hL
  exact H.nonemptyArrowIso

end AlgebraicGeometry.ProEtale.CondensedRing
