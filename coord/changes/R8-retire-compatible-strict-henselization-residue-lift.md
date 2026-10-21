# AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationResidueLift

## Reason

The assigned module is listed for duplicate retirement in `coord/retire-items.tsv`.
It has zero proof holes. Its existing adopted twin proves the same lifting theorem
using `strictLocalization` and `strictLocalizationToBase`, in place of the small
representative model and its structural map. The only mathematical DAG parent,
`compatible-strict-henselization-residue-square`, already points to
`WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore`.
That parent imports and calls the upstream twin. The legacy Sheaf parent was
retired by K4 (see `K4-strict-henselization-residue-model-retirement.md`).

This withdraws only the unused Sheaf duplicate and repoints its node to the
existing proved upstream declaration. All adopted source files, declarations,
attributes, signatures and imports remain untouched. The node's mathematical
statement and all incoming node references remain unchanged.

## Old

`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift`:

```lean
theorem Etale.exists_compatibleStrictHenselizationResidueLift
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
    (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    (hres : ρB ≫ Spec.map (CommRingCat.ofHom r) = ι ≫ ρA) :
    ∃ (φ : A →+* B),
      (IsLocalRing.residue B).comp φ = r.comp (IsLocalRing.residue A) ∧
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictHenselizationStructuralMap (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g
```

## New

No new Lean declaration. The existing adopted theorem is selected instead:
`WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift`:

```lean
theorem Etale.exists_compatibleStrictHenselizationResidueLift
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
    (r : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    (hres : ρB ≫ Spec.map (CommRingCat.ofHom r) = ι ≫ ρA) :
    ∃ (φ : A →+* B),
      (IsLocalRing.residue B).comp φ = r.comp (IsLocalRing.residue A) ∧
      Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫
          strictLocalizationToBase (ν ≫ ι ≫ σ) =
        eB.hom ≫ strictLocalizationToBase (ν ≫ τ) ≫ g
```

The small-model statement is recovered without new assumptions as follows. For
both geometric points z, compose e with
`asIso (Spec.map (smallStrictHenselizationColimitIso z).inv)`. The existing proved
`smallStrictHenselizationColimitIso_toBase` identifies the composite structural
map with the original one. Apply the adopted lifting theorem with these two
isomorphisms and the unchanged ρA, ρB and r. Rewrite that same compatibility
in the result. The witness φ and the residue-ring equality are unchanged.
The complete transport proof is in the sandbox's scratch validation file and
is compiled together with unchanged copies of the adopted theorem, its parent,
and the structural comparison theorem. It adds no production declaration.

The following is the compiled proof body of the Old signature (renamed
`originalSmallModelStatement` in scratch), importing the retained upstream lift
and `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison`:

```lean
by
  let eA' : Spec (.of A) ≅ strictLocalization (ν ≫ ι ≫ σ) :=
    eA ≪≫ asIso (Spec.map (smallStrictHenselizationColimitIso (ν ≫ ι ≫ σ)).inv)
  let eB' : Spec (.of B) ≅ strictLocalization (ν ≫ τ) :=
    eB ≪≫ asIso (Spec.map (smallStrictHenselizationColimitIso (ν ≫ τ)).inv)
  have hρA' : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      eA'.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) = σ := by
    simpa only [eA', Iso.trans_hom, asIso_hom, Category.assoc,
      smallStrictHenselizationColimitIso_toBase] using hρA
  have hρB' : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫
      eB'.hom ≫ strictLocalizationToBase (ν ≫ τ) = τ := by
    simpa only [eB', Iso.trans_hom, asIso_hom, Category.assoc,
      smallStrictHenselizationColimitIso_toBase] using hρB
  obtain ⟨φ, hred, hbase⟩ := Etale.exists_compatibleStrictHenselizationResidueLift
    σ τ ι hι ν eA' eB' ρA ρB hρA' hρB' r hres
  have hcA : eA'.hom ≫ strictLocalizationToBase (ν ≫ ι ≫ σ) =
      eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) := by
    simp only [eA', Iso.trans_hom, asIso_hom, Category.assoc,
      smallStrictHenselizationColimitIso_toBase]
  have hcB : eB'.hom ≫ strictLocalizationToBase (ν ≫ τ) =
      eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) := by
    simp only [eB', Iso.trans_hom, asIso_hom, Category.assoc,
      smallStrictHenselizationColimitIso_toBase]
  refine ⟨φ, hred, ?_⟩
  rw [hcA, ← Category.assoc eB'.hom, hcB, Category.assoc] at hbase
  exact hbase
```

The retained theorem, its residue-square caller, the structural comparison lemma,
and this transport proof each print only `propext`, `Classical.choice`, `Quot.sound`.
The exact withdrawal stub also compiles. No validation source is delivered as a
new library declaration.

## Users

`tools/downstream.py` reports zero downstream modules. Exact import/name scans of
`lean/` and `quarantine/` find no external reference to the withdrawn Sheaf
module. The sole incoming DAG node is the residue-square parent above; it already
uses the upstream version, so its dependencies require no edit. The node id is
preserved and its Lean attachment now agrees with that actual parent call.
The fixed `sk-thm-p1` unit route is preserved, including its arbitrary-base step.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift | R8 | Withdraw duplicate. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unclaimed | Already withdrawn; unchanged. |
| WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unclaimed | Unchanged; already imports and calls the retained upstream theorem. |

The duplicate's imports of `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`
and `Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale` disappear with it.
Neither dependency module is withdrawn: they still have other users. The node's
proof dependencies now describe the retained upstream proof, using the full-model
affine-chart theorem and the same henselian colimit lifting theorem. The old
raw triples steps are mediated through the chart theorem; no underlying triples
result is asserted globally unnecessary.

## Status

landed 20261021T111559-L-344874 2026-10-21 (merge of deliver/R8/Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift)
