# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model

## Reason

Restore the quarantined module assigned by coord/rework.tsv after upstream sync
5f7b33eac. Compiling the archive reproduces the unknown identifier
strictHenselization_structural_ringHom_flat at line 169 in 2.5 seconds.
The archive has zero holes.

The retired Sheaf flatness module is an empty module. Its upstream replacement
has a different interface: strictHenselization and strictLocalizationToBase,
where this theorem retains strictHenselizationRing and
strictHenselizationStructuralMap. The existing upstream theorem therefore does
not apply directly. The repaired StrictHenselRootPurityData module already
contains a complete direct proof for the required small coordinate-ring colimit.
Reuse that argument in a proved private helper, with a distinct private name.

Its R-to-neighbourhood global-section maps form a natural transformation.
Etaleness implies component flatness, and the structural-map equation identifies
the composites with the colimit coprojections as b. RingHom.Flat.of_isColimit
therefore proves b flat. No object is chosen from unproved existence data.
The finite-etale extension, both the unit and nonunit branches, the comparison
isomorphism, and the closed-image surjectivity argument are preserved.

## Old

The public signature in the quarantine archive is:

```lean
theorem GaloisCover.strict_hensel_root_finite_etale_model
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
    ∃ (E : Scheme.{u}) (p : E ⟶ N),
      IsFinite p ∧ Etale p ∧ Function.Surjective p ∧
      ∃ δ : pullback p V.ι ≅ pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
        δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
          pullback.snd p V.ι
```

Its proof imports
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat and calls
strictHenselization_structural_ringHom_flat R barY b hb.

## New

The restored public signature is identical:

```lean
theorem GaloisCover.strict_hensel_root_finite_etale_model
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
    ∃ (E : Scheme.{u}) (p : E ⟶ N),
      IsFinite p ∧ Etale p ∧ Function.Surjective p ∧
      ∃ δ : pullback p V.ι ≅ pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
        δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
          pullback.snd p V.ι
```

The replacement private import is
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat. A proved private helper,
finiteEtaleModel_small_strictHenselization_flat, supplies the missing flatness
fact for exactly this theorem's b and hb. The redundant direct proof import of
Mathlib.RingTheory.Flat.Basic is removed. All public imports and all existing
signatures, definition bodies, and docstrings are preserved verbatim.

The restored file compiles through lcompile.py in 4.9 seconds with both axiom
probes. The public theorem and the private helper each use exactly propext,
Classical.choice, and Quot.sound. There are zero holes before and after this
repair; none is added, closed, or split off.

The node retains its Lean attachment, statement, incoming edges, and unit route.
Its proof and proof_deps now describe the direct colimit argument in place of
the retired structural-flatness call. The archive is preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed; quarantined for separate rework | Its archived theorem call has exactly the same type and argument order. No adaptation is required; its archive and dependency edge remain intact. |

tools/downstream.py reports unknown module because the item is absent from lean/.
There are no current Lean importers of this missing Sheaf item; both lean/ and
quarantine/ were searched for its full module and declaration names. Its one
quarantined importer is listed above. The upstream namesake uses a distinct
strict-henselization interface and remains unchanged. No target definition
changes and no source-library module is edited.

## Status

landed 20261020T174745-L-791879 2026-10-20 (merge of deliver/E2/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel)
