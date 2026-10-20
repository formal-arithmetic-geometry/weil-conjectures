# AlgebraicGeometry.Proj.twist_finiteLocal_representatives

## Reason

Complete the assigned retirement row
`retire:Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives` in
`coord/retire-items.tsv`. The upstream twin is already proved. Its signature and
proof body agree with the duplicate after changing only the unused existential
span-proof binder from `hspan` to `_`. This changes no hypothesis or conclusion.

## Old

Module `Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives` declares:

```lean
theorem twist_finiteLocal_representatives
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (hspan : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      (∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap B (Localization.Away f) (g i))) →
      ∃ e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) = F z) ∧
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) = F (algebraMap B (Localization.Away f) a) * e x) ∧
        e (t i) = (s.1 p).1)
```

Its sole direct consumer privately imports the duplicate module.

## New

Withdraw the duplicate and privately import
`WeilConjectures.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives` in the
consumer. The existing upstream declaration stays verbatim:

```lean
theorem twist_finiteLocal_representatives
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (s : (twist 𝒜 k).val.obj (op (basicOpen 𝒜 f))) :
    let B := HomogeneousLocalization.Away 𝒜 f
    let M := LocalizedModule.Away f A
    letI : Module B M := Module.compHom M (algebraMap B (Localization.Away f))
    ∃ (n : ℕ) (g : Fin n → B) (_ : Ideal.span (Set.range g) = ⊤)
      (t : ∀ i : Fin n, LocalizedModule.Away (g i) M),
      (∀ (i : Fin n) (p : basicOpen 𝒜 f),
      let F := IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2)
      IsUnit (F (algebraMap B (Localization.Away f) (g i))) →
      ∃ e : LocalizedModule.Away (g i) M →+
          Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal,
        (∀ z : M, e (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M z) = F z) ∧
        (∀ (a : B) (x : LocalizedModule.Away (g i) M),
          e (a • x) = F (algebraMap B (Localization.Away f) a) * e x) ∧
        e (t i) = (s.1 p).1)
```

Redirect the existing node `lem-sc-proj-twist-finite-local-representatives` to
this upstream module, file, and verbatim signature. Retain the mathematical node,
its dependencies, and its proof route. No source-library file changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives | G2 | Proved duplicate withdrawn. |
| Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData | unclaimed | One private import redirects to the upstream twin. All declarations and proofs stay verbatim. |

`tools/downstream.py` finds only this direct consumer; a complete source search
finds no additional importer of the duplicate. No claim or rework row holds the
consumer. The consumer compiles with the new import. The import-direction check
accepts it, and a source-closure scan finds no nonempty Sheaf/upstream twin pair.

## Status

landed 20261020T155158-L-3205175 2026-10-20 (merge of deliver/G2/Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives)
