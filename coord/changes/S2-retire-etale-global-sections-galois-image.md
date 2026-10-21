# AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_image

## Reason

The assigned retirement row in coord/retire-items.tsv identifies this Sheaf module
as a duplicate of the adopted upstream module. Both versions have proved bodies
and no sorry. Retain the existing upstream declaration and remove only the Sheaf
copy. A compiler-checked example of the exact old signature is proved by applying
the upstream theorem without any adaptation of arguments or hypotheses.

The upstream action-compatibility condition spells two nondependent named proof
binders as anonymous implication binders. This changes neither the proposition
nor its universe parameters. No definition or target statement changes.

## Old

The duplicate declaration in
Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage has this signature:

```lean
theorem etaleGlobalSections_galoisInvariants_image
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
    (x : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj T)
    : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (v : (E.functor.obj F).obj.V),
      v ∈ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
        (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) ↔
      ∃ z : F.obj.obj (op T),
      (i.inv.app F) ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber T x F.obj z) = v
```

Its sole direct consumer privately imports that Sheaf module.

## New

Withdraw the duplicate Sheaf module. The preserved declaration in
WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage has this signature:

```lean
theorem etaleGlobalSections_galoisInvariants_image
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
    (x : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj T)
    : ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (v : (E.functor.obj F).obj.V),
      v ∈ (@Representation.invariants ℤ _ (E.functor.obj F).obj.V _ _
        (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) ↔
      ∃ z : F.obj.obj (op T),
      (i.inv.app F) ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber T x F.obj z) = v
```

Migrate the direct consumer's private import to the upstream module. Its theorem
signature and proof body remain byte-for-byte unchanged. The existing DAG node
aux-etale-global-sections-image retains its statement and all dependency edges;
its Lean attachment now names the existing upstream theorem, with the upstream
signature recorded verbatim. No DAG node or adopted source declaration is removed.

## Users

The downstream.py output lists the following five downstream modules. Only the
first imports the withdrawn module or uses its theorem directly. Holder records
were read on 2026-10-21; unedited transitive consumers require no forced adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants | unclaimed | Change only the private import on line 13 to the upstream module; compiled successfully. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Transitive consumer; unchanged theorem type and parent interface; no edit. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | D9 | Transitive consumer; unchanged theorem type and parent interface; no edit. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Transitive consumer; unchanged theorem type and parent interface; no edit. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Transitive consumer; unchanged theorem type and parent interface; no edit. |

The retained parent DAG node lem-sc-etale-global-sections-galois-invariants still
uses aux-etale-global-sections-image with exactly its previous statement. Searching
quarantine and the current DAG found no additional Lean importer requiring edits.
The unit sk-thm-br has no realized nodes displaced by this attachment change.

Validation: the original assigned module and the adapted consumer compile cleanly
through lcompile.py. A separate scratch example checks the exact old signature
against the upstream theorem; #print axioms for that theorem reports only propext,
Classical.choice and Quot.sound. import_direction.py accepts the new import.

## Status

landed 20261021T004842-L-1795220 2026-10-21 (merge of deliver/S2/Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage)
