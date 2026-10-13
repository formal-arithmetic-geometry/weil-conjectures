# derivedBaseChange_mayerVietoris_firstTwoSquares

## Reason

The existing declaration has its type colon alone at column zero. leanindex.commands
therefore reads the colon, result type and whole proof as a separate top-level command,
and reports any proof edit as a change to exported commands. stage3_delivery's declaration
parser correctly sees an unchanged signature. This record documents the conservative
interface flag so the ordinary review path can check it. No existing public signature,
definition, visibility, instance, notation or attribute changes. The original global
elaboration options are preserved; the new proof uses scoped transparency options only.
No downstream adaptation is required. Report this parser fault to the maintainer; no
project tool is modified.

## Old

```lean
theorem derivedBaseChange_mayerVietoris_firstTwoSquares
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
:
    ∀ (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X'),
      schemeDerivedQCohProperty X K → schemeDerivedQCohProperty X' K' →
      ∀ ψ : (derivedPullback g').obj K ⟶ K',
    let adjU := mvOpenRestrictionAdjunction X U
    let adjV := mvOpenRestrictionAdjunction X V
    let adjUV := mvOpenRestrictionAdjunction X (U ⊓ V)
    let adjU' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)
    let adjV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V)
    let adjUV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let a₀ := schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫ G.map ψ
    let a₂ := mvBaseChangeMiddle f f' g g' hsq.w K K' ψ U V
    let a₃ := mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V)
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K 0
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' 0
    F.map T.mor₁ ≫ a₂ = a₀ ≫ G.map T'.mor₁ ∧
    F.map T.mor₂ ≫ a₃ = a₂ ≫ G.map T'.mor₂
```

## New

The signature is verbatim identical:

```lean
theorem derivedBaseChange_mayerVietoris_firstTwoSquares
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
:
    ∀ (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X'),
      schemeDerivedQCohProperty X K → schemeDerivedQCohProperty X' K' →
      ∀ ψ : (derivedPullback g').obj K ⟶ K',
    let adjU := mvOpenRestrictionAdjunction X U
    let adjV := mvOpenRestrictionAdjunction X V
    let adjUV := mvOpenRestrictionAdjunction X (U ⊓ V)
    let adjU' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)
    let adjV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V)
    let adjUV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let a₀ := schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫ G.map ψ
    let a₂ := mvBaseChangeMiddle f f' g g' hsq.w K K' ψ U V
    let a₃ := mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V)
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K 0
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' 0
    F.map T.mor₁ ≫ a₂ = a₀ ≫ G.map T'.mor₁ ∧
    F.map T.mor₂ ≫ a₃ = a₂ ≫ G.map T'.mor₂
```

The previous whole proof `:= by sorry` is replaced by the two private biproduct
assembly lemmas applied to the canonical single-open unit and restriction identities.
The one original public import stays public. New imports are proof-only.

## Users

The downstream name-use search lists the two modules below. The 427 other downstream
modules do not mention the declaration and see the same interface.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares | K3 | Its proof changes; exact signature retained. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | Existing application keeps exactly the same type; no edit required. |

## Status

landed 20261013T172656-L-2099698 2026-10-13 (merge of deliver/K3/Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares)
