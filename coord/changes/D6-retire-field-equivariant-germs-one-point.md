# AlgebraicGeometry.Scheme.field_equivariant_germ_family_section_onePoint

## Reason

The item is a zero-hole retirement in coord/retire-items.tsv (and kind retire in
coord/queue.tsv). The adopted source already proves all three public declarations.
The local copy differs in coefficient universe: max u v versus upstream max (u + 1) v.
Retire the duplicate without changing upstream declarations or consumer signatures.

## Old

The local declarations to withdraw, verbatim:

```lean
theorem onePoint_selected_lift_section
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (x₀ : p.fiber.obj X) (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X),
          p.toPresheafFiber X x₀ F.obj z = f x₀

theorem onePoint_propagate_from_selected_lift
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (x₀ : p.fiber.obj X) (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∀ (z : F.obj.obj (op X)),
          p.toPresheafFiber X x₀ F.obj z = f x₀ →
          ∀ x : p.fiber.obj X,
            p.toPresheafFiber X x F.obj z = f x

theorem field_equivariant_germ_family_section_onePoint
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
        (hτ : (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω))
        (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y)
        (hy : y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left)
        (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
          (hτ : (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω))
          (x x' : p.fiber.obj X)
          (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left),
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X,
          p.toPresheafFiber X x F.obj z = f x 
```

## New

The existing adopted source declarations, retained verbatim in
WeilConjectures.AlgebraicGeometry.FieldEquivariantGermsOnePoint:

```lean
theorem onePoint_selected_lift_section
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (x₀ : p.fiber.obj X) (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
        (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω) →
        ∀ (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y),
        y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left →
        ∀ (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
          (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω) →
          ∀ (x x' : p.fiber.obj X),
          x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X),
          p.toPresheafFiber X x₀ F.obj z = f x₀

theorem onePoint_propagate_from_selected_lift
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (x₀ : p.fiber.obj X) (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
        (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω) →
        ∀ (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y),
        y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left →
        ∀ (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
          (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω) →
          ∀ (x x' : p.fiber.obj X),
          x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
          f x' = ρ g (f x)) →
        ∀ (z : F.obj.obj (op X)),
          p.toPresheafFiber X x₀ F.obj z = f x₀ →
          ∀ x : p.fiber.obj X,
            p.toPresheafFiber X x F.obj z = f x

theorem field_equivariant_germ_family_section_onePoint
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (X : (Spec (.of K)).Etale) [Subsingleton X.left] [Nonempty X.left] :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
        (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω) →
        ∀ (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y),
        y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left →
        ∀ (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
          (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω) →
          ∀ (x x' : p.fiber.obj X),
          x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X,
          p.toPresheafFiber X x F.obj z = f x 
```

The retired module is listed in deleted.txt and becomes an empty module on landing.
No source-library file, public import, attribute, or definition is edited.
All three node attachments retain their declaration names and move to this upstream
module with the exact upstream signatures. Their dependency nodes stay attached and
needed, including for unfinished DAG parents. The selected-lift proof description is
adjusted to the direct upstream proof; the smaller-universe transport is documented.

EtaleGlobalSectionsGaloisImage has coefficients Type (u + 1), so its only change is a
proof import swap. FieldEquivariantGermFamilySection keeps coefficients Type (max u v).
Compose its sheaf F with uliftFunctor, giving a larger-universe sheaf F'. The composite
of Point.presheafFiberCompIso and Equiv.ulift is an equivalence e from the lifted stalk
to the original stalk. Its explicit germ formula sends a lifted germ of z to the germ
of z.down. Conjugate rho by e and transport the prescribed germ family by e.symm.
The original action formula and covariance prove the corresponding hypotheses for F'.
The upstream one-point theorem now produces a section on each singleton component.
Lower it by ULift.down; applying the germ formula to the obtained equality gives the
original prescribed germs. The existing overlap and gluing proof then applies verbatim.
This argument is real proof glue in the consumer, with no new theorem or hole.

Edge cases: ULift.down is an equivalence also for empty section types, so no
nonemptiness hypothesis on F is added. Empty X uses the existing empty singleton cover
and gluing argument. The identity Galois group and arbitrary coefficient universes use
the same transport. No algebraicity or perfectness hypothesis is added to Omega.
The source theorem still handles nonalgebraic geometric-point fields.

The unit sk-prop-h2 has empty realized statement and step lists for these nodes.
No unit route is bypassed: all parent dependencies keep their node ids, now realized
upstream. No target statement or target definition changes meaning.

## Users

Both direct importers are unclaimed. The downstream.py --uses scans for the selected
lift and main one-point declarations find precisely those two external users and the
item itself. An import scan agrees. The complete transitive downstream list is included
below; retaining both public consumer signatures leaves its interfaces identical.
The parser stage3_delivery.diff_module reports no changed signature or new sorry in
both retained consumer files.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint | D6 (item) | Withdraw duplicate; redirect its three DAG attachments upstream. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesAction | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage | unclaimed | Proof import swap only; Type (u + 1) already fits the upstream universe. |
| Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.FieldEquivariantGermFamilySection | unclaimed | Proof import swap and explicit ULift stalk transport; public signature unchanged. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFull | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.GaloisStalkActionFullyFaithful | unclaimed | Transitive consumer; no edit or interface change. |
| Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint | unclaimed | Transitive consumer; no edit or interface change. |

## Status

landed 20261020T235552-L-1190254 2026-10-20 (merge of deliver/D6/Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint)
