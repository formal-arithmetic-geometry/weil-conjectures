# AlgebraicGeometry.Scheme.strictHenselization_residue_separable_model

## Reason

The human-approved retirement record `coord/retire-items.tsv` lists the assigned
module as a duplicate of its existing upstream twin. It currently has zero proof
holes. The adopted theorem is proved on upstream's `strictLocalization`, whereas
the duplicate uses `strictHenselizationScheme`. The ring constructions are
canonically isomorphic through `smallStrictHenselizationColimitIso`; their base
maps are the compatible limit legs. These represent the same strict henselization.

A direct import replacement is insufficient: the old structural-map environment
and the canonical environment contain duplicate declaration names. A scratch
compile reproduced the clash at `smallStrictHenselizationColimitIso`. The item's
only legacy consumer feeds a closed chain of five further legacy modules. Each
is unclaimed, has an existing proved twin, and is itself listed for retirement.
Retiring the six modules together avoids loading the incompatible presentations.
The only outside source consumer of the terminal theorem already imports
`WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues`
in `WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison`.

The delivery withdraws exactly those six Sheaf copies and reattaches their seven
DAG declarations to existing upstream modules. All signatures below match after
only `strictHenselizationScheme` → `strictLocalization` and
`strictHenselizationStructuralMap` → `strictLocalizationToBase` (whitespace apart).
No hypothesis, universe or conclusion changes mathematically. Every upstream
module and every target statement and definition remains untouched. No target
semantic review is reopened, since the targets already use the upstream chain.
No existing source-library declaration is removed or reproved with a hole.

## Old

The seven public signatures in the withdrawn copies, verbatim:

`Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel`

```lean
theorem strictHenselization_residue_separable_model
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    [HenselianLocalRing A]
    (z : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme z) :
    ∃ (s : S) (f : S.residueField s →+* IsLocalRing.ResidueField A),
      (letI := f.toAlgebra; ∀ x : IsLocalRing.ResidueField A,
        IsSeparable (S.residueField s) x) ∧
      Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecResidueField s =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ e.hom ≫
          strictHenselizationStructuralMap z
```

`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability`

```lean
theorem Etale.compatibleStrictHenselization_residue_isSeparable
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    [Algebra (IsLocalRing.ResidueField B) k']
    (hAlgebra : algebraMap (IsLocalRing.ResidueField B) k' = (Spec.preimage ρB).hom) :
    ∀ x : IsLocalRing.ResidueField A,
      IsSeparable (IsLocalRing.ResidueField B)
        ((Spec.preimage (ι ≫ ρA)).hom x)
```

`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial`

```lean
theorem Etale.compatibleStrictHenselization_residue_separable_polynomial
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ) :
    ∀ x : IsLocalRing.ResidueField A,
      ∃ p : Polynomial (IsLocalRing.ResidueField B),
        p ≠ 0 ∧ p.Separable ∧
          p.eval₂ (Spec.preimage ρB).hom ((Spec.preimage (ι ≫ ρA)).hom x) = 0
```

`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage`

```lean
theorem Etale.compatibleStrictHenselization_residue_image
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ)
    : ∀ x : IsLocalRing.ResidueField A,
      ∃ y : IsLocalRing.ResidueField B,
        (Spec.preimage ρB).hom y = (Spec.preimage (ι ≫ ρA)).hom x
```

`Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore`

```lean
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues_core
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s)
              (eB : Spec (.of B) ≅ strictHenselizationScheme t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap s =
                eB.hom ≫ strictHenselizationStructuralMap t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictHenselizationStructuralMap t = τ ∧
              True

theorem Etale.compatibleStrictHenselization_residue_square
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      letI := hφ
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g ∧
      ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
        ι ≫ ρA
```

`Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues`

```lean
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s)
              (eB : Spec (.of B) ≅ strictHenselizationScheme t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap s =
                eB.hom ≫ strictHenselizationStructuralMap t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictHenselizationStructuralMap t = τ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
                ι ≫ ρA
```

## New

The same declarations already exist in these upstream modules, with the exact
signatures below. These are references, not new declarations in the delivery.
The six withdrawn paths are listed in `deleted.txt`; the delivery tool lands them
as empty modules. Every affected node retains its identity and mathematical
statement, with its `lean` record pointing to the upstream declaration.

`WeilConjectures.AlgebraicGeometry.StrictHenselizationResidueSeparableModel`

```lean
theorem strictHenselization_residue_separable_model
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    [HenselianLocalRing A]
    (z : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization z) :
    ∃ (s : S) (f : S.residueField s →+* IsLocalRing.ResidueField A),
      (letI := f.toAlgebra; ∀ x : IsLocalRing.ResidueField A,
        IsSeparable (S.residueField s) x) ∧
      Spec.map (CommRingCat.ofHom f) ≫ S.fromSpecResidueField s =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ e.hom ≫
          strictLocalizationToBase z
```

`WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability`

```lean
theorem Etale.compatibleStrictHenselization_residue_isSeparable
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    [Algebra (IsLocalRing.ResidueField B) k']
    (hAlgebra : algebraMap (IsLocalRing.ResidueField B) k' = (Spec.preimage ρB).hom) :
    ∀ x : IsLocalRing.ResidueField A,
      IsSeparable (IsLocalRing.ResidueField B)
        ((Spec.preimage (ι ≫ ρA)).hom x)
```

`WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial`

```lean
theorem Etale.compatibleStrictHenselization_residue_separable_polynomial
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ) :
    ∀ x : IsLocalRing.ResidueField A,
      ∃ p : Polynomial (IsLocalRing.ResidueField B),
        p ≠ 0 ∧ p.Separable ∧
          p.eval₂ (Spec.preimage ρB).hom ((Spec.preimage (ι ≫ ρA)).hom x) = 0
```

`WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage`

```lean
theorem Etale.compatibleStrictHenselization_residue_image
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ)
    : ∀ x : IsLocalRing.ResidueField A,
      ∃ y : IsLocalRing.ResidueField B,
        (Spec.preimage ρB).hom y = (Spec.preimage (ι ≫ ρA)).hom x
```

`WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore`

```lean
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues_core
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictLocalization s)
              (eB : Spec (.of B) ≅ strictLocalization t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictLocalizationToBase s =
                eB.hom ≫ strictLocalizationToBase t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictLocalizationToBase s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictLocalizationToBase t = τ ∧
              True

theorem Etale.compatibleStrictHenselization_residue_square
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B]
    [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (ν : Spec (.of Ω) ⟶ Spec (.of k'))
    (eA : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ))
    (eB : Spec (.of B) ≅ strictLocalization (ν ≫ τ))
    (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B)))
    (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ)
    (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      letI := hφ
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictLocalizationToBase (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g ∧
      ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
        ι ≫ ρA
```

`WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues`

```lean
theorem Etale.projectiveLine_compatibleStrictHenselizationResidues
    {S T : Scheme.{u}} {g : T ⟶ S}
    {k k' Ω : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    [Field Ω] [IsAlgClosed Ω]
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T)
    (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (ψ : S.residueField s ⟶ .of k),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (ψ : T.residueField t ⟶ .of k'),
      ψ.hom.IsIntegral ∧ Spec.map ψ ≫ T.fromSpecResidueField t = τ)
    (ν : Spec (.of Ω) ⟶ Spec (.of k')) :
    let s := ν ≫ ι ≫ σ
    let t := ν ≫ τ
    ∃ (A B : Type u) (cA : CommRing A) (cB : CommRing B),
      letI := cA
      letI := cB
      ∃ (hA : HenselianLocalRing A) (hB : HenselianLocalRing B),
        letI := hA
        letI := hB
        ∃ (sA : IsSepClosed (IsLocalRing.ResidueField A))
          (sB : IsSepClosed (IsLocalRing.ResidueField B)),
          letI := sA
          letI := sB
          ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
            letI := hφ
            ∃ (eA : Spec (.of A) ≅ strictLocalization s)
              (eB : Spec (.of B) ≅ strictLocalization t)
              (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
              (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
              IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictLocalizationToBase s =
                eB.hom ≫ strictLocalizationToBase t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictLocalizationToBase s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictLocalizationToBase t = τ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) =
                ι ≫ ρA
```

## Users

`tools/downstream.py` reports exactly the five downstream modules below for the
assigned module. A full source import scan, including `quarantine/`, finds no
external importer of this six-module set. All five downstream modules are
unclaimed in the current claim records. Each retained mathematical result has its
upstream counterpart and DAG attachment. No module held by another group changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel | K4 | Withdraw duplicate; its DAG attachment selects the existing upstream twin. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability | unclaimed | Withdraw duplicate; its DAG attachment selects the existing upstream twin. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial | unclaimed | Withdraw duplicate; its DAG attachment selects the existing upstream twin. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage | unclaimed | Withdraw duplicate; its DAG attachment selects the existing upstream twin. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unclaimed | Withdraw duplicate; its DAG attachment selects the existing upstream twin. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues | unclaimed | Withdraw duplicate; its DAG attachment selects the existing upstream twin. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged: already imports the upstream endpoint. |

Other textual uses of the seven public names in adopted source modules already
resolve through upstream imports; their files remain unchanged. The seven node
IDs and all incoming dependency references stay in place. In particular the
`sk-thm-p1` realized unit nodes remain attached to proved declarations; this
withdrawal does not rely on their absence from today's import graph.

The polynomial node's proof dependencies are corrected to the two declarations
its existing upstream proof actually uses: residue separability and the proved
minimal-polynomial core. Direct triple-colimit dependencies from its older plan
are removed there; those geometric results remain needed by the upstream
single-model argument and are not globally pruned.

Validation: copied the six unchanged upstream sources into the sandbox's scratch
validation tree and compiled them in import order with `lcompile.py --all`.
All seven public theorems print exactly `propext`, `Classical.choice`, and
`Quot.sound`; none depends on an unfinished proof. Each file compiled in under
four seconds. The source files and their copied signatures were compared before
writing these attachment records. No new theorem, definition or hole is added.

## Status

landed 20261020T155201-L-3206299 2026-10-20 (merge of deliver/K4/Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel)
