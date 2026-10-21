# AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreData

## Reason

Retire the duplicate assigned by coord/queue.tsv (stage 3, retire) and
coord/retire-items.tsv. It has zero holes and no current Lean importers.
Its former Sheaf consumer is already withdrawn, and the sole actual DAG parent,
compatible-strict-henselization-residues-core, is attached to the proved upstream
ProjectiveLineCompatibleStrictHenselizationResiduesCore theorem. That source
module already imports and applies the upstream CoreData theorem. Thus the
mathematical dependency stays needed and is preserved; this is not a withdrawal
based solely on zero importers.

## Old

The retired Sheaf theorem has signature:

```lean
theorem Etale.exists_compatibleStrictHenselizationCoreData
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
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
                strictHenselizationStructuralMap s =
                eB.hom ≫ strictHenselizationStructuralMap t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictHenselizationStructuralMap t = τ
```

## New

The node attaches to the unchanged proved theorem in
WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreData:

```lean
theorem Etale.exists_compatibleStrictHenselizationCoreData
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
              Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
                strictLocalizationToBase s =
                eB.hom ≫ strictLocalizationToBase t ≫ g ∧
              ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
                eA.hom ≫ strictLocalizationToBase s = σ ∧
              ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
                eB.hom ≫ strictLocalizationToBase t = τ
```

The signatures agree verbatim after replacing strictHenselizationScheme by
strictLocalization and strictHenselizationStructuralMap by
strictLocalizationToBase. These are canonical isomorphic presentations, not
definitionally equal names. The retired private localizationComparison and
localizationComparison_base proved exactly this transport using
smallStrictHenselizationColimitIso and the colimit coprojection formula. The
upstream parent already uses the full-colimit presentation, so no transport or
consumer adaptation is needed. None of the hypotheses, ring structures, local
map, residue maps, universal homeomorphisms or three equalities is dropped.

The node proof now records the upstream two-step existence/completion assembly.
All adopted source declarations, signatures, imports and proof bodies stay
unchanged. No target statement or definition changes. No node or unit step is
withdrawn. Only the redundant small-colimit assembly module is retired.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | Y3 | Withdraw duplicate module; retain node on existing upstream theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | already withdrawn | Preserve its empty module. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unchanged source | Sole DAG parent; already imports and directly applies upstream CoreData, then appends True.intro. |
| WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | unchanged source | Existing replacement; no edits. |

The downstream tool reports zero modules downstream of the retired module.
A source search finds no Lean imports of it. The current rework table has no
entry for it. Other DAG occurrences are creation/blueprint provenance, not
statement or proof dependency edges. No module held by another group is changed.

## Status

landed 20261021T005758-L-1892920 2026-10-21 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData)
