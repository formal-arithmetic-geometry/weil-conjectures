# AlgebraicGeometry.Scheme.exists_fieldSection_of_invariant_germ

## Reason

The current queue and coord/retire-items.tsv assign retirement of this zero-hole
Sheaf twin in favor of its existing upstream theorem. The upstream coefficient
universe is max (u+1) v; its sole direct consumer supports max u v. A direct import
swap cannot preserve that consumer. Use ULift and transport the action through the
stalk comparison equivalence, then lower the section supplied by the upstream theorem.

## Old

```lean
theorem exists_fieldSection_of_invariant_germ
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (action : MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F))
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : F.obj.obj (op X)),
      action.smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
        (pointSmallEtale s).toPresheafFiber X x' F.obj z)
    (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : (pointSmallEtale s).fiber.obj (etaleSpec K L))
    (hx : x.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype)))
    (m : (pointSmallEtale s).sheafFiber.obj F)
    (hm : ∀ g ∈ L.fixingSubgroup, action.smul g m = m) :
    ∃ z : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj z = m
```

## New

Withdraw the local module and attach its node to the unchanged upstream declaration:

```lean
theorem exists_fieldSection_of_invariant_germ
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (action : MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F))
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) →
      ∀ (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X),
      x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
      ∀ (z : F.obj.obj (op X)),
      action.smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
        (pointSmallEtale s).toPresheafFiber X x' F.obj z)
    (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : (pointSmallEtale s).fiber.obj (etaleSpec K L))
    (hx : x.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype)))
    (m : (pointSmallEtale s).sheafFiber.obj F)
    (hm : ∀ g ∈ L.fixingSubgroup, action.smul g m = m) :
    ∃ z : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj z = m
```

The sole consumer fieldSections_stalkInvariants keeps its exact existing signature,
public imports, definitions, and action construction. Its private import uses the
upstream module, with private imports of Preserves.Ulift and Action.TransferInstance.
Its surjectivity branch lifts F, uses the germ comparison to transfer its actual
action and fixed element, applies the upstream theorem, and lowers the resulting
section. No source-library file or target is modified; no axioms or holes are added.

## Users

The downstream.py --uses check finds the item and one external user. The direct
importer scan also finds exactly that consumer. Neither module has a current local
claim lock; this dispatcher assignment gives Q2 the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative | Q2 | Withdraw the zero-hole duplicate; node now points to the upstream theorem. |
| Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants | unclaimed | Preserve its exact signature and public imports, and bridge the universe difference in the proof. |

The other 40 transitive downstream modules do not mention the retired declaration
and retain the consumer's existing API. DAG parents continue to cite the original
node, now realized upstream; the unit sk-prop-h2 has no realization at this node.
No dependency or unit argument is withdrawn.

## Status

landed 20261020T163315-L-3728615 2026-10-20 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative)
