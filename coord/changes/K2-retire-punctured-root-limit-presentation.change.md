# AlgebraicGeometry.Scheme.punctured_root_limit_presentation

## Reason

Retire the duplicate Sheaf module as assigned by coord/retire-items.tsv and the human's
2026-10-20 instruction in coord/changes/retire-sheaf-twins-20261020.md. The item has zero
holes. Its source twin uses a different canonical strict henselization ring, so its
consumer requires a proved isomorphism over the base and transport of the punctured chart.

## Old

The withdrawn Sheaf module has the following public declaration:

```lean
theorem punctured_root_limit_presentation
    (R : CommRingCat.{u}) (f : R) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (D : I ⥤ Scheme.{u}) (c : Cone D)
        (t : D ⟶ (Functor.const I).obj (Spec R)),
        Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
        ∃ e : V.toScheme ≅ c.pt,
          (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
          ∀ j, ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
            Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
            let g := a.hom f
            let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
            let N := Spec (CommRingCat.of A)
            let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
            let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
            ∃ d : V.toScheme ≅ D.obj j,
              d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map a
```

Its only direct importer is Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent.
It also contains the proved private strictHenselization_colimit_comparison, introduced
by F3's earlier ring-colimit retirement.

## New

Use the already proved, unchanged adopted-source declaration:

```lean
theorem punctured_root_limit_presentation
    (R : CommRingCat.{u}) (f : R) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (D : I ⥤ Scheme.{u}) (c : Cone D)
        (t : D ⟶ (Functor.const I).obj (Spec R)),
        Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
        ∃ e : V.toScheme ≅ c.pt,
          (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
          ∀ j, ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
            Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
            let g := a.hom f
            let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
            let N := Spec (CommRingCat.of A)
            let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
            let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
            ∃ d : V.toScheme ≅ D.obj j,
              d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map a
```

Withdraw lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedRootLimitPresentation.lean
through deleted.txt and reattach lem-sbc-punctured-root-limit-presentation to the source
twin. Preserve all source-library declarations, attributes and public imports verbatim.

The only direct consumer retains its entire theorem signature verbatim. Move the private
proved strictHenselization_colimit_comparison there. It constructs the unique isomorphism
of the two colimits and proves compatibility with the two structural morphisms from their
leg equations. Apply the source root-limit theorem to b followed by this isomorphism.
Apply punctured_root_base_change to the ring isomorphism; the second projection of that
pullback is an isomorphism. Compose this chart isomorphism with the source limit comparison,
and prove the structural equation by the pullback condition and its first-projection
formula. The original finite-presentation section-descent argument then applies unchanged.

Replace the private import of the retired copy with its source twin and the existing
source root base-change module. Replace the public Sheaf structural-map wrapper by its
two upstream statement dependencies, as F3 already did in the retired presentation.
This is necessary to avoid bringing both declarations named
strictHenselizationStructuralMap_eq into the same environment: the wrapper's equation
uses the old ring model, whereas the source extension's equation uses the adopted model.
No mathematical definition, hypothesis, conclusion, or target statement changes.

The two backward-definitional-equality options are scoped to the consumer theorem.
They allow elaboration of the spectrum/basic-open coercions in the chart comparison
without unfolding the ring colimit construction. No heartbeat or file-time limit changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation | K2 | Retire duplicate and attach its node to the proved source twin. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent | unclaimed | Migrate its import and transport the punctured chart; theorem signature unchanged. |

The downstream.py query lists only the section-descent consumer downstream of this item.
A direct import search finds that same single consumer. DAG parent references retain the
root-limit node, now attached to the source twin; the consumer node records the comparison
and base-change transport. The unit has no realized step fixed to the withdrawn copy.
The source-library root-limit consumer already uses the source twin and is untouched.

## Status

landed 20261020T221230-L-4161573 2026-10-20 (merge of deliver/K2/Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation)
