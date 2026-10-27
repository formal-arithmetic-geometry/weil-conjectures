# AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_exchangeCube_stalkComparisons

## Reason

The assigned DIFFERENT retirement item is already an empty withdrawn stub, but its
node still attaches the original small-model statement to the absent unprefixed
declaration there. The adopted declaration of that name takes presentations of
strictLocalization and uses strictLocalizationToBase. The node instead records
strictHenselizationScheme and strictHenselizationStructuralMap. Attaching it to the
adopted declaration would discard that distinction without checking the transport.

Both required small-model component statements are already proved. Restore their
conjunction in a distinct StrictLocalSmallModel module and use the existing
smallModel_ names in its proof. This does not repeat either component proof, create
an alias of an existing combined small-model theorem, or add a new mathematical
obligation. The recorded signature is unchanged after removing whitespace and
changing only the declaration name. All point equations, canonical maps, let
bindings, hypotheses and universes remain present.

## Old

The assigned module is currently, verbatim:

```lean
module

/-! Withdrawn: no declarations remain; use the official WeilConjectures twin. -/
```

Its node records this small-model signature (verbatim):

```lean
theorem Etale.isIso_strictHenselization_exchangeCube_stalkComparisons {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S} [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Field Ω] [IsAlgClosed Ω] (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g) (ν : Spec (.of Ω) ⟶ Spec (.of k')) {A B : Type u} [CommRing A] [HenselianLocalRing A] [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)] (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ)) (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ)) (φ : A →+* B) [IsLocalHom φ] (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g) (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ) (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ) (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA) {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A)) (sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ))) (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B)) (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ))) (b : X₁ ⟶ X') (sqB : IsPullback b f₁ f' (eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ))) (hb : b ≫ g' = p₁ ≫ p₀) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) : let jA := eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) let jB := eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) let g₀ := Spec.map (CommRingCat.ofHom φ) let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) let ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB let h : jB ≫ g = g₀ ≫ jA := by simpa only [jB, g₀, jA, Category.assoc] using hφ.symm let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G) let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}])).obj K let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f')_*[AddCommGrpCat.{u + 1}])).obj K let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀ let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀ IsIso (derivedStalkComparison jB t τ ht M₁ N₁ (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)) ∧ IsIso (derivedStalkComparison jB t τ ht M₂ N₂ (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ))
```

## New

The assigned module remains withdrawn through deleted.txt. The existing node now
attaches to Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeStalkIsos,
which states and proves:

```lean
theorem Etale.smallModel_isIso_strictHenselization_exchangeCube_stalkComparisons
    {S T X X' : Scheme.{u}} {g : T ⟶ S} {f : X ⟶ S}
    [QuasiCompact f] [QuasiSeparated f] {f' : X' ⟶ T} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)]
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (φ : A →+* B) [IsLocalHom φ]
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
        strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g)
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    (hρ : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA)
    {X₀ X₁ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (.of A))
    (sq₀ : IsPullback p₀ f₀ f
      (eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)))
    (p₁ : X₁ ⟶ X₀) (f₁ : X₁ ⟶ Spec (.of B))
    (sq₁ : IsPullback p₁ f₁ f₀ (Spec.map (CommRingCat.ofHom φ)))
    (b : X₁ ⟶ X')
    (sqB : IsPullback b f₁ f'
      (eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ)))
    (hb : b ≫ g' = p₁ ≫ p₀)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let jA := eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ)
    let jB := eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ)
    let g₀ := Spec.map (CommRingCat.ofHom φ)
    let t := ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let ht : t ≫ jB = τ := by simpa only [t, jB, Category.assoc] using hρB
    let h : jB ≫ g = g₀ ≫ jA := by simpa only [jB, g₀, jA, Category.assoc] using hφ.symm
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((p₀)^*[AddCommGrpCat.{u + 1}]).obj G)
    let M₁ := (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g)^*[AddCommGrpCat.{u + 1}])).obj K
    let M₂ := (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f')_*[AddCommGrpCat.{u + 1}])).obj K
    let N₁ := (R+((f₀)_*[AddCommGrpCat.{u + 1}]) ⋙
      D+((g₀)^*[AddCommGrpCat.{u + 1}])).obj K₀
    let N₂ := (D+((p₁)^*[AddCommGrpCat.{u + 1}]) ⋙
      R+((f₁)_*[AddCommGrpCat.{u + 1}])).obj K₀
    IsIso (derivedStalkComparison jB t τ ht M₁ N₁
      (exchangeCubeSourceComparison sq₀.toCommSq h G) (q : ℤ)) ∧
    IsIso (derivedStalkComparison jB t τ ht M₂ N₂
      (exchangeCubeTargetComparison sqB.toCommSq hb G) (q : ℤ))
```

The proof uses And.intro (constructor) and applies the existing small-model source
and target theorems with every original argument. The two proof-only imports are
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeStalkIsosSource and
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeTargetStalkIso. The public
imports supply the small strict-henselization structural map, the canonical cube
maps and henselian-ring terminology required by the statement. No definition,
instance, target statement or adopted source-library declaration is changed.

The original node id, statement, statement dependencies, proof dependencies and
unit are retained. Only its Lean attachment, proof text and proof_origin change.
No new node is required: this is the existing node's original conjunction.

## Users

The downstream.py --uses census finds zero current Lean importers and zero uses of
the old assigned module. An exact-import scan of lean/Sheaf, lean/WeilConjectures
and quarantine/ also finds none. No coord/rework.tsv row or J6 return names this
item. The current coord/retire-items.tsv row classifies it DIFFERENT; no archived
item is being removed or replaced.

A complete DAG scan of stmt_deps, proof_deps and proof-step uses finds exactly one
parent, lem-weil-pbc-abelian-stalk-exchange-localization. It retains this node and
its required comparison-isomorphism conclusions; its current adopted Lean proof
uses the full-model analogue and remains unchanged. We do not infer withdrawal
of this mathematical obligation from zero importers. Its original small-model
statement is fully proved in the replacement, and the sk-thm-p1 unit route stays.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | J6 dispatch | Retain withdrawal of colliding stub; repair stale node attachment. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeStalkIsos | J6 new replacement | Prove the original small-model conjunction with a distinct name. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeStalkIsosSource | unclaimed | Existing source theorem reused unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeTargetStalkIso | unclaimed | Existing target theorem reused unchanged. |
| WeilConjectures.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos | adopted source | All signatures, imports and proofs retained verbatim. |
| WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization | adopted source; DAG parent | Same node id and mathematical conclusions available; no source edit. |

The theorem introduces no new assumption in the cases q = 0, zero sheaves, empty
total spaces, arbitrary separably closed point fields or the specified nonstandard
cartesian models: both existing component statements cover all these cases and
receive precisely the same arguments. No choice of data or new definition occurs.

A standalone copy of this complete proof imports the adopted full-model theorem
alongside it and compiles in 6.0 seconds. Both combined theorem axiom checks list
only propext, Classical.choice and Quot.sound. The compile service supplied the
small-model source dependency through its private unpublished-dependency overlay.
The original signature was compared mechanically modulo whitespace and declaration
name. The check is retained at scratchpad/lean/JointModelAxiomCheck.lean.

## Status

landed 20261024T223335-L-1588719 2026-10-24 (merge of deliver/J6/Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsos)
