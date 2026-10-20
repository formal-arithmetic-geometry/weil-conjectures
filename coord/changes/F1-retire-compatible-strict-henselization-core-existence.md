# AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreExistence

## Reason

Retire the duplicate listed in coord/retire-items.tsv and coord/queue.tsv in favor
of the existing upstream theorem. The upstream theorem uses strictLocalization,
whereas the copy uses strictHenselizationScheme, the small coordinate-ring
colimit. These schemes are canonically isomorphic, rather than definitionally
equal. The consumer must transport its spectrum presentations and structure maps.

The unchanged item also fails to compile against the published build because
its newly landed StrictHenselizationExtension import meets the former Sheaf
StrictHenselization declarations. The packet removes that duplicate proof route.

## Old

The withdrawn Sheaf declaration, verbatim:

```lean
theorem Etale.exists_compatibleStrictHenselizationCoreExistence
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
          ∃ (eA : Spec (.of A) ≅ strictHenselizationScheme s)
            (eB : Spec (.of B) ≅ strictHenselizationScheme t)
            (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
            (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
            IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
            ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
              eA.hom ≫ strictHenselizationStructuralMap s = σ ∧
            ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
              eB.hom ≫ strictHenselizationStructuralMap t = τ
```

Its consumer, Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData,
publicly imported Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap and
privately imported the Sheaf core-existence and core-completion modules.

## New

Withdraw the Sheaf module and attach its node to the existing upstream declaration,
verbatim:

```lean
theorem Etale.exists_compatibleStrictHenselizationCoreExistence
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
          ∃ (eA : Spec (.of A) ≅ strictLocalization s)
            (eB : Spec (.of B) ≅ strictLocalization t)
            (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A)))
            (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))),
            IsUniversalHomeomorphism ρA ∧ IsUniversalHomeomorphism ρB ∧
            ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
              eA.hom ≫ strictLocalizationToBase s = σ ∧
            ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
              eB.hom ≫ strictLocalizationToBase t = τ
```

CoreData keeps its public theorem signature verbatim. It privately imports the
upstream core-existence and core-completion modules. Its public structural-map
import becomes WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap,
which supplies the same small-colimit objects and structural map its signature
uses. The extra Sheaf helper with the same name as upstream's large-colimit
structural-map equation is no longer imported into this proof environment.

The proved private localizationComparison is Spec of the canonical
smallStrictHenselizationColimitIso. The proved private localizationComparison_base
uses Functor.Final.ι_colimitIso_hom to identify limit legs, then the two
structural-map equations to identify the base maps. CoreData first applies the
upstream theorems, then composes eA and eB with this spectrum comparison and
transports the three displayed equalities. All other witnesses are unchanged.
The private helper data are concrete isomorphisms from proved colimit results.

CoreData was also the sole importer of the Sheaf core-completion copy. As its
proof now uses the upstream completion theorem, retire that unused copy in the
same packet and attach compatible-strict-henselization-core-completion to its
upstream twin. Its old signature was:

```lean
theorem Etale.exists_compatibleStrictHenselizationCoreCompletion
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω A B : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [CommRing B] [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g)
    (eA : Spec (.of A) ≅ strictHenselizationScheme s)
    (eB : Spec (.of B) ≅ strictHenselizationScheme t) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictHenselizationStructuralMap s =
        eB.hom ≫ strictHenselizationStructuralMap t ≫ g
```

Its unchanged upstream replacement has signature:

```lean
theorem Etale.exists_compatibleStrictHenselizationCoreCompletion
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω A B : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [CommRing B] [HenselianLocalRing A] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField B)]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g)
    (eA : Spec (.of A) ≅ strictLocalization s)
    (eB : Spec (.of B) ≅ strictLocalization t) :
    ∃ (φ : A →+* B) (hφ : IsLocalHom φ),
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictLocalizationToBase s =
        eB.hom ≫ strictLocalizationToBase t ≫ g
```

No mathematical dependency is discarded: the same core-completion step now uses
this existing large-colimit statement, and CoreData transports its result back
to its original small-colimit presentation. The only DAG parent with this
completion dependency is CoreData; other occurrences are provenance via paths.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence | F1 | Withdraw the duplicate and point its node at the existing source theorem. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion | unclaimed | Retire the unused duplicate after its only consumer migrates; attach its node to the source theorem. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | unclaimed | Replace the private proof imports and transport the presentations; keep its theorem signature verbatim. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unclaimed | No edit; compiled against the adapted CoreData. It explicitly imports its own Sheaf structural-map API. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues | unclaimed | No edit; compiled against both rebuilt downstream modules. |

Only CoreData directly imports either retired module. The two other modules are
its complete transitive consumer closure in the current Lean sources. No source
library declaration, public import, attribute or proof is changed. No target
statement or definition changes. The mathematical node remains needed and is
preserved on its upstream attachment; this is module retirement, not withdrawal
of that mathematical dependency. The unit route is retained.

## Status

landed 20261020T154937-L-3174647 2026-10-20 (merge of deliver/F1/Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreExistence)
