# AlgebraicGeometry.Scheme.fieldSections_stalkInvariants

## Reason

The current retire-items.tsv assignment retires the zero-hole local twin in favor
of the adopted upstream declaration. The upstream theorem has coefficient universe
max (u + 1) v, whereas the local version has max u v. Preserve every consumer
signature and all source-library declarations. Two current consumers already have large
enough universes; W2 independently removed the fourth consumer import. The one-point reconstruction consumer
needs a proof adaptation through ULift; a direct import swap fails to compile.

## Old

```lean
theorem fieldSections_stalkInvariants (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω] [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (s : Spec (.of Ω) ⟶ Spec (.of K)) (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : ∃ (lift : ∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L], (pointSmallEtale s).fiber.obj (etaleSpec K L)) (action : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)), MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F)), (∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L], (lift L).left = Spec.map (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype))) ∧ (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v))), (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω) (hτ : (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω)) (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X) (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) (z : F.obj.obj (op X)), (action F).smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) = (pointSmallEtale s).toPresheafFiber X x' F.obj z) ∧ (∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L], Set.BijOn ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj) Set.univ {m | ∀ g ∈ L.fixingSubgroup, (action F).smul g m = m}) ∧ (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] (j : L →ₐ[K] L') (g : Gal(Ks/K)) (hg : g.toAlgHom.comp L.val = L'.val.comp j) (z : F.obj.obj (op (etaleSpec K L))), (pointSmallEtale s).toPresheafFiber (etaleSpec K L') (lift L') F.obj (F.obj.map (etaleSpecMap j).op z) = (action F).smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧ (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] (j : L →ₐ[K] L') (g g' : Gal(Ks/K)) (hg : g.toAlgHom.comp L.val = L'.val.comp j) (hg' : g'.toAlgHom.comp L.val = L'.val.comp j) (m : (pointSmallEtale s).sheafFiber.obj F) (hm : ∀ h ∈ L.fixingSubgroup, (action F).smul h m = m), (∀ h ∈ L'.fixingSubgroup, (action F).smul h ((action F).smul g m) = (action F).smul g m) ∧ (action F).smul g m = (action F).smul g' m)) ∧ (∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v))) (φ : F ⟶ F'), (∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L] (z : F.obj.obj (op (etaleSpec K L))), (pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F'.obj (φ.hom.app _ z) = (pointSmallEtale s).sheafFiber.map φ ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧ (∀ (g : Gal(Ks/K)) (m : (pointSmallEtale s).sheafFiber.obj F), (pointSmallEtale s).sheafFiber.map φ ((action F).smul g m) = (action F').smul g ((pointSmallEtale s).sheafFiber.map φ m)))
```

## New

Withdraw the local module, preserving the existing upstream declaration verbatim:

```lean
theorem fieldSections_stalkInvariants (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω] [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (s : Spec (.of Ω) ⟶ Spec (.of K)) (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : ∃ (lift : ∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L], (pointSmallEtale s).fiber.obj (etaleSpec K L)) (action : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)), MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F)), (∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L], (lift L).left = Spec.map (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype))) ∧ (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))), (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω), (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω) → ∀ (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X), x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left → ∀ (z : F.obj.obj (op X)), (action F).smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) = (pointSmallEtale s).toPresheafFiber X x' F.obj z) ∧ (∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L], Set.BijOn ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj) Set.univ {m | ∀ g ∈ L.fixingSubgroup, (action F).smul g m = m}) ∧ (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] (j : L →ₐ[K] L') (g : Gal(Ks/K)), g.toAlgHom.comp L.val = L'.val.comp j → ∀ (z : F.obj.obj (op (etaleSpec K L))), (pointSmallEtale s).toPresheafFiber (etaleSpec K L') (lift L') F.obj (F.obj.map (etaleSpecMap j).op z) = (action F).smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧ (∀ (L L' : IntermediateField K Ks) [FiniteDimensional K L] [FiniteDimensional K L'] [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] (j : L →ₐ[K] L') (g g' : Gal(Ks/K)), g.toAlgHom.comp L.val = L'.val.comp j → g'.toAlgHom.comp L.val = L'.val.comp j → ∀ (m : (pointSmallEtale s).sheafFiber.obj F), (∀ h ∈ L.fixingSubgroup, (action F).smul h m = m) → (∀ h ∈ L'.fixingSubgroup, (action F).smul h ((action F).smul g m) = (action F).smul g m) ∧ (action F).smul g m = (action F).smul g' m)) ∧ (∀ (F F' : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) (φ : F ⟶ F'), (∀ (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L] (z : F.obj.obj (op (etaleSpec K L))), (pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F'.obj (φ.hom.app _ z) = (pointSmallEtale s).sheafFiber.map φ ((pointSmallEtale s).toPresheafFiber (etaleSpec K L) (lift L) F.obj z)) ∧ (∀ (g : Gal(Ks/K)) (m : (pointSmallEtale s).sheafFiber.obj F), (pointSmallEtale s).sheafFiber.map φ ((action F).smul g m) = (action F').smul g ((pointSmallEtale s).sheafFiber.map φ m)))
```

Only the realization of the invariant-section node moves upstream. Its mathematical
statement, dependencies, and parent nodes stay. The unit sk-prop-h2 has no statement
or proof step realized by this node; no unit route is bypassed.

In onePoint_selected_lift_section, compose F with uliftFunctor, then compose the
ULift stalk comparison equivalence with the existing change-of-geometric-point
stalk equivalence. Apply upstream invariance to the lifted sheaf, retain that
action on its lifted stalk, and use the comparison formula on germs to compare
it with rho. Lower the resulting finite-field section before pulling it back.
All definitions, public imports, attributes, and consumer signatures remain exact.
The other two delivered consumers replace a proof import only. No upstream file changes.
The obsolete BaseFieldCohomologicalDimension adaptation is removed from the
packet after W2 independently landed a complete proof without the retired import.

## Users

The downstream.py --uses scan lists the item and the three theorem users. The
earlier import scan also listed BaseFieldCohomologicalDimension. W2 independently
removed that import in landing 20261020T174917-L-820235 (ledger 17:49 UTC);
its stale sandbox adaptation is omitted. The three remaining external direct
importers are migrated here; transitive downstream modules retain
the same consumer interfaces. The original node id stays attached to the same
mathematical theorem, now upstream, so unfinished DAG parents retain their dependency.
The returned BaseFieldCohomologicalDimension adaptation was held by W2;
the prior unclaimed entry was stale. Its claim is now closed after landing.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants | B9 | Withdraw the zero-hole duplicate; redirect its node upstream. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | W2 (independently landed) | Returned packet changed line 12 only; now omitted entirely because W2 removed the retired import and proved the theorem. |
| Sheaf.AlgebraicGeometry.EtaleFieldSectionsInvariants | unclaimed | Replace the proof import only; its coefficients are Type (u + 1). |
| Sheaf.AlgebraicGeometry.FieldModuleSectionsInvariants | unclaimed | Replace the proof import only; its coefficients are Type (max (u + 1) v). |
| Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint | unclaimed | Replace the proof import and bridge the smaller coefficient universe in the selected-lift proof. |

For the W2-held BaseFieldCohomologicalDimension, the original was restored in the
sandbox temporarily and deliver3.py was run against the otherwise unchanged
retirement packet. It refused before compilation, with exit code 1:

```text
FAILED: deleted modules are still imported (change these files in the delivery too): lean/Sheaf/AlgebraicGeometry/BaseFieldCohomologicalDimension.lean imports Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
```

This is the actual import/deletion-gate diagnostic, not a Lean elaborator error.
The baseline still contains the old compiled module, and withdrawal lands an
empty module, so a baseline compile cannot demonstrate a missing-import Lean
error here. The forced-adaptation rule for explicit withdrawals in deliver3.py
recognizes precisely this case: the retired import must be migrated even if the
baseline artifact would allow the original to compile. In that returned version the only changed line was
line 12: replace `import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`
with `import WeilConjectures.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`.
The retained upstream theorem supplies the same mathematical dependency used by
step 1 of that consumer's docstring. In the returned adaptation all public imports,
statements, attributes,
visibility and its existing proof body were byte-identical to the then-current main.
The original was restored only for that counterfactual and the adapted version
was restored immediately afterwards. That adapted file compiled (exit 0,
10.4 seconds). The shared checkout then refreshed to W2's independent landing,
whose consumer no longer imports the item and has no holes. The stale adaptation
has therefore been removed from the delivery, preserving W2's complete proof.
The counterfactual describes the returned version, not the newly landed source;
there is no remaining forced adaptation of this consumer.

The import-only one-point variant failed at the application hact F: Lean could
not solve max (u + 1) v = max u v (and the corresponding successor constraint).
The original packet compiled its adapted one-point file in 5.7 seconds.
All three retained consumers pass lcompile.py --all again in this repair,
with cached results (exit 0). stage3_delivery.diff_module
reports no changed statement and no new sorry in any consumer.

Edge cases: ULift.down is an equivalence also on empty section types, so no
nonempty-sheaf assumption is added. Trivial Galois groups and coefficient
universes smaller than the site universe use the same comparison; no assumption
on perfectness or algebraicity of the original geometric-point field is added.
No target or definition used by a target changes its mathematical meaning.

## Status

landed 20261020T230721-L-604799 2026-10-20 (merge of deliver/B9/Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants)
