# AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants

## Reason

The queue and `coord/retire-items.tsv` classify
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants` as a duplicate of
the adopted upstream module. The upstream theorem is fully proved and has the
same proposition; only the syntax of the action-compatibility binders differs.
Withdraw the Sheaf duplicate and attach the DAG node to the upstream declaration.

## Old

The duplicate Sheaf declaration has the signature:

```lean
theorem etaleGlobalSections_galoisInvariants
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (T : (Spec (.of K)).Etale) (hT : Limits.IsTerminal T)
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
    (hi : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      (i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z)
    : ∃ t : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
        F.obj.obj (op T) ≃+ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
          (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ),
      ∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (φ : F ⟶ F') (z : F.obj.obj (op T)),
        (t F' (φ.hom.app (op T) z)).val = (E.functor.map φ).hom.hom (t F z).val
```

## New

Withdraw the duplicate module and preserve the adopted upstream declaration:

```lean
theorem etaleGlobalSections_galoisInvariants
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (T : (Spec (.of K)).Etale) (hT : Limits.IsTerminal T)
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
    (hi : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) →
      ∀ (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
      ∀ (z : F.obj.obj (op X)),
      (i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) ((pointSmallEtale
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x F.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' F.obj z)
    : ∃ t : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
        F.obj.obj (op T) ≃+ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
          (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ),
      ∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (φ : F ⟶ F') (z : F.obj.obj (op T)),
        (t F' (φ.hom.app (op T) z)).val = (E.functor.map φ).hom.hom (t F z).val
```

Its action-compatibility proof binders use anonymous implications instead of
names. The old signature is checked by direct application of this theorem in
`scratchpad/Check.lean`; the proposition and universe parameters are unchanged.
The node retains its statement, proof and dependency edges, and its Lean
attachment names the upstream declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| None | n/a | downstream.py reports zero downstream modules; no adaptation required. |

The historical consumer `Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology`
is already an empty withdrawn module; its node now attaches to the upstream
`sheafHAddEquivContinuousCohomology` declaration. Searches of live and quarantined
Lean sources find no other consumer of this duplicate. All existing DAG
references still resolve through the retained node, now attached upstream.

The adopted source root import `WeilConjectures.lean` remains unchanged.

## Status

landed 20261021T012412-L-2185859 2026-10-21 (merge of deliver/N1/Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants)
