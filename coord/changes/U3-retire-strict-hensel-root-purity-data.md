# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data

## Reason

Complete the zero-hole retirement assigned in `coord/retire-items.tsv` under the
human-approved hand-off `coord/changes/retire-sheaf-twins-20261020.md`. The Sheaf
copy duplicates the upstream theorem with the canonical small representative
colimit in place of the full affine-neighbourhood colimit. Replace its only direct
consumer's private proof import and application, transport the complete upstream
result through the canonical root-algebra isomorphism, and retire the copy.

## Old

The retired public declaration has this verbatim signature:

```lean
theorem GaloisCover.strict_hensel_root_purity_data
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g →
    IsLocallyNoetherian N ∧
      ∃ (D : Scheme.{u}) (j : D ⟶ N),
        IsRegular D ∧ IsIntegral D ∧ IsEffectiveCartierCenter j ∧
        (∀ z : N, z ∈ V ↔ z ∉ Set.range j) ∧
        ∃ (C : Scheme.{u}) (n : C ⟶ N),
          IsFinite n ∧ Etale (n ∣_ V) ∧
          ∃ (O : N.Opens) (η : D), IsGenericPoint η Set.univ ∧
            j η ∈ O ∧ Etale (n ∣_ O) ∧
          ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
              pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
            ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
              n ∣_ V
```

The only direct consumer imports and applies it as follows:

```lean
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData
```

```lean
      W.strict_hensel_root_purity_data i G R φ f hG hf β hβ barY b hb hg
```

## New

The same mathematical node attaches to this existing upstream declaration,
whose source file is unchanged:

```lean
theorem GaloisCover.strict_hensel_root_purity_data
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g →
    IsLocallyNoetherian N ∧
      ∃ (D : Scheme.{u}) (j : D ⟶ N),
        IsRegular D ∧ IsIntegral D ∧ IsEffectiveCartierCenter j ∧
        (∀ z : N, z ∈ V ↔ z ∉ Set.range j) ∧
        ∃ (C : Scheme.{u}) (n : C ⟶ N),
          IsFinite n ∧ Etale (n ∣_ V) ∧
          ∃ (O : N.Opens) (η : D), IsGenericPoint η Set.univ ∧
            j η ∈ O ∧ Etale (n ∣_ O) ∧
          ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
              pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
            ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
              n ∣_ V
```

The consumer imports the upstream module privately and adds a private import of
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison`. Its new proved
private `small_root_purity_data` retains the old small-model conclusion. Compose
b with `smallStrictHenselizationColimitIso.hom` and use the toBase equation.
`AdjoinRoot.mapRingEquiv` gives the canonical root-algebra comparison. Apply the
upstream theorem and transport D's immersion by composition with the spectrum
isomorphism. The kernel of this immersion is an isomorphic flat pullback of the
old invertible kernel; its support is the complement of the transported open.
Noetherianness, finiteness, both etale restrictions, and the generic-point
neighbourhood transport along the same isomorphism. Compose the comparison on
punctured opens with `pullback.map` to transport the cover isomorphism; its
projection equation follows from the restriction inclusions and pullback
projection identities. The existing nonunit branch now applies:

```lean
      small_root_purity_data i G W R φ f hG hf β hβ barY b hb hg
```

Every public signature, public import, existing docstring, and the rest of the
finite-etale-model proof are unchanged. No public helper is added. No data are
chosen from an unproved theorem. No target statement or definition changes.
The retired path is listed in `deleted.txt`; the tool lands its empty module.
The two existing DAG node copies describe the retained upstream proof and the
consumer's transport. The original proof's root extension, tame normalization
and purity route is preserved in the unit `sk-prop-input-spreading`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | U3 | Assigned duplicate retired; mathematical node reattached to unchanged upstream theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Sole direct importer migrated; private transport proves the original small-model conclusion. Public signature and imports identical. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive consumer unchanged; compiled against the adapted finite-etale model. |

This is the complete `tools/downstream.py --uses` output and direct importer
graph. A scan of the quarantine tree found no additional importer. The only
incoming mathematical dependency is the finite-etale-model node; it still cites
the purity-data node, now attached to the upstream theorem, and additionally
cites the existing colimit-comparison node for its private transport. Neither
node realizes a unit statement or step. Thus no unfinished parent or unit
obligation is withdrawn. The source tree `lean/WeilConjectures/` is unchanged.

## Status

landed 20261021T225220-L-3798519 2026-10-21 (merge of deliver/U3/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData)
