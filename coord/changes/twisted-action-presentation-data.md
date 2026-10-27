# CategoryTheory.TwistedActionRingedSite.ModulePresentation

## Reason

Extract the existing data into a public data module so that genuine construction and
closed-comparison obligations can be stated without importing their consumer theorem.
Separate the restriction fields from created limits and exactness, which are now proved
from the source fixed-pair constructions. No mathematical condition is removed from
ModulePresentation, OrbitPresentation or Presentation. No definition selects an arbitrary
witness of an unproved existence theorem. The statement of presentation is unchanged.

All original data declarations move, with their full names, to
Sheaf.CategoryTheory.TwistedActionRingedSiteData, publicly re-exported by the item.
Only ModulePresentation's parent hierarchy changes: its original Site fields and restriction
fields are inherited through RestrictionPresentation. The remaining definitions and fields
are verbatim. The old public imports are retained through the data module.

## Old

```lean
structure ModulePresentation extends Site J s R a where
  /-- The translation is an autoequivalence, not an arbitrary endofunctor. -/
  translation : Modules R ≌ Modules R
  /-- Its forward functor is the explicitly defined module translation. -/
  translation_eq : translation.functor = sigma J s R a
  /-- Module sheaves on the constructed site are exactly the fixed pairs. -/
  modules : Modules coefficient ≌ Pairs (sigma J s R a)
  /-- Restriction is exactly forgetting the pair, naturally. -/
  restriction :
    modules.functor ⋙ forgetPairs (sigma J s R a) ≅
      SheafOfModules.pushforward
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map coefficientRestriction.inv)
  /-- The structure isomorphism is recovered from the degree-minus-one generator. -/
  module_generator (M : Modules coefficient) (X : C)
      (x : ((sigma J s R a).obj (modules.functor.obj M).obj.a).val.obj (op X)) :
    (restriction.hom.app M).val.app (op (s.inverse.obj X)) x =
      M.val.map ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
        ((restriction.hom.app M).val.app (op X)
          ((modules.functor.obj M).obj.str.val.app (op X) x))
  /-- Addition is the inherited addition of underlying module morphisms. -/
  modules_add {M N : Modules coefficient} (f g : M ⟶ N) :
    (modules.functor.map (f + g)).hom.f =
      (modules.functor.map f).hom.f + (modules.functor.map g).hom.f
  /-- The set-sheaf version presents invertible translation actions. -/
  sets : Sheaf topology (Type u) ≌
    Pairs (s.inverse.sheafPushforwardContinuous (Type u) J J)
  /-- Forgetting the set action is ordinary restriction. -/
  setsRestriction : sets.functor ⋙
      forgetPairs (s.inverse.sheafPushforwardContinuous (Type u) J J) ≅
    inclusion.sheafPushforwardContinuous (Type u) J topology
  /-- The set action too is recovered from the degree-minus-one generator. -/
  set_generator (M : Sheaf topology (Type u)) (X : C)
      (x : (sets.functor.obj M).obj.a.obj.obj (op (s.inverse.obj X))) :
    (setsRestriction.hom.app M).hom.app (op (s.inverse.obj X)) x =
      M.obj.map ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
        ((setsRestriction.hom.app M).hom.app (op X)
          ((sets.functor.obj M).obj.str.hom.app (op X) x))
  /-- The geometric morphism has the direction Sh(C) to Sh(C semidirect Z). -/
  geometric : RingedToposMorphism (ring R) (ring coefficient)
  /-- Its inverse image is the set restriction functor. -/
  geometric_inverse : geometric.inverse =
    inclusion.sheafPushforwardContinuous (Type u) J topology
  /-- The structural map is the ring restriction isomorphism on underlying sets. -/
  structural : IsIso geometric.ringMap
  /-- Under the displayed inverse-image equality the structural ring map is restriction. -/
  structural_eq : geometric.ringMap =
    (eqToHom geometric_inverse).app ((sheafCompose topology (forget RingCat)).obj
      (ring coefficient)) ≫
      (sheafCompose J (forget RingCat)).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map coefficientRestriction.hom)
  /-- Module restriction is its module pullback by the adjunction universal property. -/
  modulePullback : (modules.functor ⋙ forgetPairs (sigma J s R a)) ⊣ geometric.modules
  /-- Forgetting the module action is conservative. -/
  conservative : (forgetPairs (sigma J s R a)).ReflectsIsomorphisms
  /-- Forgetting creates all limits in the fixed universe. -/
  createsLimits : CreatesLimitsOfSize.{u, u} (forgetPairs (sigma J s R a))
  /-- Forgetting creates all colimits in the fixed universe. -/
  createsColimits : CreatesColimitsOfSize.{u, u} (forgetPairs (sigma J s R a))
  /-- Exactness, expressed without a second abelian structure on fixed pairs. -/
  exact_limits : PreservesFiniteLimits (forgetPairs (sigma J s R a))
  /-- Exactness includes cokernels as well as kernels. -/
  exact_colimits : PreservesFiniteColimits (forgetPairs (sigma J s R a))
```

## New

```lean
structure RestrictionPresentation extends Site J s R a where
  /-- The translation is an autoequivalence, not an arbitrary endofunctor. -/
  translation : Modules R ≌ Modules R
  /-- Its forward functor is the explicitly defined module translation. -/
  translation_eq : translation.functor = sigma J s R a
  /-- Module sheaves on the constructed site are exactly the fixed pairs. -/
  modules : Modules coefficient ≌ Pairs (sigma J s R a)
  /-- Restriction is exactly forgetting the pair, naturally. -/
  restriction :
    modules.functor ⋙ forgetPairs (sigma J s R a) ≅
      SheafOfModules.pushforward
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map coefficientRestriction.inv)
  /-- The structure isomorphism is recovered from the degree-minus-one generator. -/
  module_generator (M : Modules coefficient) (X : C)
      (x : ((sigma J s R a).obj (modules.functor.obj M).obj.a).val.obj (op X)) :
    (restriction.hom.app M).val.app (op (s.inverse.obj X)) x =
      M.val.map ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
        ((restriction.hom.app M).val.app (op X)
          ((modules.functor.obj M).obj.str.val.app (op X) x))
  /-- Addition is the inherited addition of underlying module morphisms. -/
  modules_add {M N : Modules coefficient} (f g : M ⟶ N) :
    (modules.functor.map (f + g)).hom.f =
      (modules.functor.map f).hom.f + (modules.functor.map g).hom.f
  /-- The set-sheaf version presents invertible translation actions. -/
  sets : Sheaf topology (Type u) ≌
    Pairs (s.inverse.sheafPushforwardContinuous (Type u) J J)
  /-- Forgetting the set action is ordinary restriction. -/
  setsRestriction : sets.functor ⋙
      forgetPairs (s.inverse.sheafPushforwardContinuous (Type u) J J) ≅
    inclusion.sheafPushforwardContinuous (Type u) J topology
  /-- The set action too is recovered from the degree-minus-one generator. -/
  set_generator (M : Sheaf topology (Type u)) (X : C)
      (x : (sets.functor.obj M).obj.a.obj.obj (op (s.inverse.obj X))) :
    (setsRestriction.hom.app M).hom.app (op (s.inverse.obj X)) x =
      M.obj.map ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
        ((setsRestriction.hom.app M).hom.app (op X)
          ((sets.functor.obj M).obj.str.hom.app (op X) x))
  /-- The geometric morphism has the direction Sh(C) to Sh(C semidirect Z). -/
  geometric : RingedToposMorphism (ring R) (ring coefficient)
  /-- Its inverse image is the set restriction functor. -/
  geometric_inverse : geometric.inverse =
    inclusion.sheafPushforwardContinuous (Type u) J topology
  /-- The structural map is the ring restriction isomorphism on underlying sets. -/
  structural : IsIso geometric.ringMap
  /-- Under the displayed inverse-image equality the structural ring map is restriction. -/
  structural_eq : geometric.ringMap =
    (eqToHom geometric_inverse).app ((sheafCompose topology (forget RingCat)).obj
      (ring coefficient)) ≫
      (sheafCompose J (forget RingCat)).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map coefficientRestriction.hom)
  /-- Module restriction is its module pullback by the adjunction universal property. -/
  modulePullback : (modules.functor ⋙ forgetPairs (sigma J s R a)) ⊣ geometric.modules
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Restriction together with its created limits, colimits, and exactness.
Source: step 5 of the twisted action-site construction
(blueprint: lem-sf-twisted-action-ringed-site). -/
structure ModulePresentation extends RestrictionPresentation J s R a where
  /-- Forgetting the module action is conservative. -/
  conservative : (forgetPairs (sigma J s R a)).ReflectsIsomorphisms
  /-- Forgetting creates all limits in the fixed universe. -/
  createsLimits : CreatesLimitsOfSize.{u, u} (forgetPairs (sigma J s R a))
  /-- Forgetting creates all colimits in the fixed universe. -/
  createsColimits : CreatesColimitsOfSize.{u, u} (forgetPairs (sigma J s R a))
  /-- Exactness, expressed without a second abelian structure on fixed pairs. -/
  exact_limits : PreservesFiniteLimits (forgetPairs (sigma J s R a))
  /-- Exactness includes cokernels as well as kernels. -/
  exact_colimits : PreservesFiniteColimits (forgetPairs (sigma J s R a))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.TwistedActionRingedSite | U3 | Existing data are re-exported; proof constructs the successive structures. |

`tools/downstream.py Sheaf.CategoryTheory.TwistedActionRingedSite --uses ModulePresentation`
and the same command for `Presentation` report zero downstream modules and only the item's
own uses. Direct import search likewise finds no current Lean consumer. DAG parents remain
attached to the unchanged presentation theorem; none is withdrawn or pruned. No adapted
module held by another group and no source-library edit is included. Targets retain their
statements; the mathematical meaning of the data is unchanged. The independent reader
should check the relocation and inherited projections together with this record.

## Status

landed 20261023T105703-L-3592432 2026-10-23 (merge of deliver/U3/Sheaf.CategoryTheory.TwistedActionRingedSite)
