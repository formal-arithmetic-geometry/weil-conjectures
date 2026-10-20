# AlgebraicGeometry.Proj.twist_finiteLocal_values

## Reason

The assigned retirement row in `coord/retire-items.tsv` identifies this proved
Sheaf module as a duplicate of the official upstream module. The mathematical
statements agree; the upstream existential span witness has an anonymous binder
where the copy names it `hspan`. This proof-irrelevant binder name does not change
any hypothesis or conclusion. The upstream proof is complete.

## Old

Module `Sheaf.AlgebraicGeometry.ProjTwistFiniteValues` declares:

```lean
theorem twist_finiteLocal_values
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (hspan : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      ∀ (i : Fin n) (p : basicOpen 𝒜 f)
        (e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
          IsLocalization.map (M := Submonoid.powers f)
            (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
            (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
            (Submonoid.powers_le.mpr p.2) z) →
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) =
            IsLocalization.map (M := Submonoid.powers f)
              (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
              (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
              (Submonoid.powers_le.mpr p.2)
              (algebraMap B (Localization.Away f) a) * e x) →
        e (t i) = (s.1 p).1
```

Its direct consumer privately imports that module.

## New

Withdraw the duplicate module and privately import
`WeilConjectures.AlgebraicGeometry.ProjTwistFiniteValues` in its direct consumer.
The unchanged upstream declaration is:

```lean
theorem twist_finiteLocal_values
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      ∀ (i : Fin n) (p : basicOpen 𝒜 f)
        (e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal),
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) =
          IsLocalization.map (M := Submonoid.powers f)
            (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
            (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
            (Submonoid.powers_le.mpr p.2) z) →
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) =
            IsLocalization.map (M := Submonoid.powers f)
              (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
              (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
              (Submonoid.powers_le.mpr p.2)
              (algebraMap B (Localization.Away f) a) * e x) →
        e (t i) = (s.1 p).1
```

Redirect node `new-finite-values` to this existing upstream module and file.
No upstream file, theorem proof, target statement, or definition is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjTwistFiniteValues | W7 | Duplicate withdrawn. |
| Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives | unclaimed | One private import redirects to the upstream twin; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData | unclaimed | Transitive consumer; source and theorem unchanged. |

The downstream scan finds these two consumer modules. The source search finds
only the direct consumer mentioning `twist_finiteLocal_values`. Both consumers
will be compiled against the changed import, and the upstream value theorem's
axioms checked. The upstream twin has no remaining Sheaf twin dependency.

## Status

landed 20261020T145549-L-2413266 2026-10-20 (merge of deliver/W7/Sheaf.AlgebraicGeometry.ProjTwistFiniteValues)
