# AlgebraicGeometry.Scheme.exists_fieldSection_of_finiteGalois_invariant_representative

## Reason

The item is listed as `retire` in coord/queue.tsv and coord/retire-items.tsv, with zero
holes. Its declaration duplicates an existing upstream theorem. The two interfaces
are not interchangeable: the upstream coefficient universe is max (u + 1) v, whereas
the Sheaf consumer supports max u v. Preserve that consumer signature exactly and
integrate the descent argument into its proof, using the already proved upstream
finiteGaloisSectionsDescent and automorphism-extension declarations. No upstream
file, declaration signature, attribute or public import is changed. No target changes.

## Old

The retired local declaration had this signature:

```lean
theorem exists_fieldSection_of_finiteGalois_invariant_representative
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
    (E : FiniteGaloisIntermediateField K Ks) (hLE : L ≤ E.toIntermediateField)
    (y : (pointSmallEtale s).fiber.obj (etaleSpec K E))
    (hy : y.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)))
    (z : F.obj.obj (op (etaleSpec K E)))
    (hinj : Function.Injective
      ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj))
    (hz : ∀ g ∈ L.fixingSubgroup,
      action.smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) :
    ∃ w : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj w =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z
```

## New

The local module is withdrawn. Its DAG attachment records this existing, unchanged
upstream declaration instead:

```lean
theorem exists_fieldSection_of_finiteGalois_invariant_representative
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
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
    (E : FiniteGaloisIntermediateField K Ks) (hLE : L ≤ E.toIntermediateField)
    (y : (pointSmallEtale s).fiber.obj (etaleSpec K E))
    (hy : y.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)))
    (z : F.obj.obj (op (etaleSpec K E)))
    (hinj : Function.Injective
      ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj))
    (hz : ∀ g ∈ L.fixingSubgroup,
      action.smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) :
    ∃ w : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj w =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z
```

The consumer exists_fieldSection_of_invariant_germ retains its exact existing
signature and public imports. Its private descent import and final theorem invocation
are replaced by the automorphism invariance, restriction-sheaf construction, section
descent and germ-naturality proof. Its node now names those dependencies directly.

## Users

`tools/downstream.py ... --uses exists_fieldSection_of_finiteGalois_invariant_representative`
reports the following two modules; there is only one external direct importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Sites.FiniteGaloisInvariantGermDescent | U1 | Withdraw the queued duplicate module; attach its node to the existing upstream declaration. |
| Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative | unclaimed | Keep the signature and public imports; use finite Galois sections descent directly in the proof. |

The other 40 transitive importers do not use the retired declaration. They keep the
same consumer theorem and its coefficient universe. The source-library counterpart
is preserved verbatim and is not deleted or weakened. The two node attachments and
proof routes now distinguish the larger-universe upstream theorem from the direct
smaller-universe proof in the consumer.

## Reconciliation after returned landing

The returned head a5ea5fb3ad6 predated T2's landing 509f8f741dc. The repaired
consumer starts from the current sheaf-dag source, preserving its upstream
FiniteGaloisGermRepresentative import, Preserves.Ulift import and ULift-based
representative construction exactly. Only the retired descent import and final
descent invocation are replaced by the already reviewed direct descent proof.
Current DAG metadata is preserved; the consumer proof plan now also describes
T2's ULift bridge. The reconciled consumer compiles on the server in 6.1 seconds.

## Status

landed 20261020T153023-L-2864800 2026-10-20 (merge of deliver/U1/Sheaf.AlgebraicGeometry.Sites.FiniteGaloisInvariantGermDescent)
