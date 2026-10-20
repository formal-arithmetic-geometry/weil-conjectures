# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data

## Reason

Restore the quarantined module assigned by coord/rework.tsv (sync 5f7b33eac,
2026-10-20). The archived file contains zero holes. Its compile fails at the
retired strictHenselization_structural_ringHom_flat declaration, followed by an
unsolved main goal caused by that missing call.

The upstream replacement uses strictHenselization and strictLocalizationToBase;
this item's unchanged interface uses strictHenselizationRing and
strictHenselizationStructuralMap. These models are canonically isomorphic, not
definitionally equal. The upstream flatness module also publicly imports an
extension declaring the same structural-map lemma name as the small-interface
module, so it cannot simply replace the retired import.

The existing repaired StrictHenselRootNormalizationGenericEtale module supplies
a complete direct colimit proof for precisely this small-ring interface.
Specialize that argument in a proved private helper with a distinct local name.
The neighbourhood maps on global sections form a natural transformation out of
R, each map is flat, and the structural-map identity identifies their composites
with b. RingHom.Flat.of_isColimit proves flatness. No theorem is assumed or split
off, no object is chosen from an unproved existence assertion, and no definition
or public statement changes. The existing root quotient, divisor, and finite
tame normalization argument remains verbatim after its flatness call.

## Old

The public signature in the quarantine archive is:

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

Its proof imports
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat and calls
strictHenselization_structural_ringHom_flat R barY b hb.

## New

The restored public signature is identical:

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

The private proof import is now
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat. The proof calls
purityData_small_strictHenselization_flat R barY b hb, proved in this module.
Every public import, existing declaration signature, and definition body is
preserved. The DAG proof now records the colimit-flatness and etale-flatness
tools directly. Its Lean attachment, mathematical statement, incoming edges,
and blueprint unit route are preserved.

The complete module compiles cleanly through lcompile.py in 5.2 seconds.
#print axioms for the public theorem and the private flatness helper each gives
exactly propext, Classical.choice, Quot.sound. The archive and restored module
both have zero local holes; no hole is closed, added, or split off.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed; quarantined for separate rework | The archived import and call at line 151 retain the identical public signature and argument order. Its archive, rework row, Lean attachment and dependency edges remain intact. No adaptation is forced. |

tools/downstream.py reports unknown module because the item is absent from lean/.
No active Lean file imports the missing Sheaf item. Both lean/ and quarantine/
were searched for its full module name and theorem name. The active upstream
counterpart and its upstream consumer have their own interface and are unchanged.
The DAG parent lem-sbc-strict-hensel-root-finite-etale-model retains its dependency.
No target definition changes and no source-library file is edited.

## Status

landed 20261020T162321-L-3589376 2026-10-20 (merge of deliver/R2/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData)
