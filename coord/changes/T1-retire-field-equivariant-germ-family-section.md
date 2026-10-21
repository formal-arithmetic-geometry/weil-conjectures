# AlgebraicGeometry.Scheme.field_equivariant_germ_family_section

## Reason

Retire the zero-hole duplicate listed in coord/retire-items.tsv. The adopted source
already proves the same assertion at a larger coefficient universe. The consumer
needs max u v, and its signature must remain unchanged. An import swap alone fails
with `max (u + 1) v =?= max u v` at the application (remote compiler, 2026-10-21).
Use explicit ULift transport. No source-library declaration or public import changes.

## Old

Withdraw the local declaration:

```lean
theorem field_equivariant_germ_family_section (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω] [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω] (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v))) : let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F), (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω) (hτ : (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω)) (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y) (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left) (z : F.obj.obj (op Y)), ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) → ∀ (X : (Spec (.of K)).Etale) (f : p.fiber.obj X → p.sheafFiber.obj F), (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω) (hτ : (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω)) (x x' : p.fiber.obj X) (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left), f x' = ρ g (f x)) → ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X, p.toPresheafFiber X x F.obj z = f x
```

## New

Use the existing source declaration, unchanged:

```lean
theorem field_equivariant_germ_family_section (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω] [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω] [IsAlgClosed Ω] (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) : let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F), (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω), (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω) → ∀ (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y), y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left → ∀ (z : F.obj.obj (op Y)), ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) → ∀ (X : (Spec (.of K)).Etale) (f : p.fiber.obj X → p.sheafFiber.obj F), (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω), (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω) → ∀ (x x' : p.fiber.obj X), x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left → f x' = ρ g (f x)) → ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X, p.toPresheafFiber X x F.obj z = f x
```

In GaloisStalkActionFull replace the private import with the source module and add
Mathlib.CategoryTheory.Limits.Preserves.Ulift privately. Compose F' with uliftFunctor,
identify its stalk via presheafFiberCompIso and Equiv.ulift, conjugate the action,
and transport the family. The germ comparison proves the canonical action formula;
the existing equivariance calculation proves covariance. Lower the resulting
section, and apply germ comparison to recover the prescribed original germs.
Every public signature and visibility is unchanged, as are all other proof lines.
The item node attaches to the source; its note explains the smaller universe.
The consumer node records the transport. No definition used by a target changes.

## Users

The downstream.py --uses search finds only the item and GaloisStalkActionFull as
textual declaration users. The full transitive downstream list follows. Since the
changed import is private, no later consumer sees a changed public environment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesAction | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | D9 | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFull | unclaimed | Private proof import migrated; ULift preserves the public signature. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFullyFaithful | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.KunnethMapAgrees | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.PunctualTensorBaseChange | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.EtaleCohomology.KunnethOneProper | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.Paper.KunBcKunnethCompat | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |
| Sheaf.Targets.BaseChangeTowardsFields | unclaimed | Unchanged; imports only the preserved consumer interface transitively. |

## Status

landed 20261021T002149-L-1494216 2026-10-21 (merge of deliver/T1/Sheaf.AlgebraicGeometry.FieldEquivariantGermFamilySection)
