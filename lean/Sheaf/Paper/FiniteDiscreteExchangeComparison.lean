/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

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
The bounded constructible finite-coefficient origin theorem gives an etale bounded
complex L realizing N. Exact inverse image commutes with pullback, while bounded-below
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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
