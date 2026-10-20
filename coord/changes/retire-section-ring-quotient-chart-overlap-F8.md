# AlgebraicGeometry.Scheme.Modules.sectionRing_quotient_charts_overlap

## Reason

The human-authorized retirement row in `coord/retire-items.tsv` assigns
`Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap` to the adopted
source-library twin. The upstream module already proves the same theorem with the
same declaration name and complete proof. The Sheaf module is a duplicate and is
withdrawn through `deleted.txt`; no target statement or source-library file changes.

## Old

The duplicate module declared this full signature, verbatim:

```lean
theorem sectionRing_quotient_charts_overlap
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d e : ℕ) (s : sectionRingGrade L d) (t : sectionRingGrade L e)
    (hd : 0 < d) (he : 0 < e) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (hV : (V : Set X) = nonvanishingLocus (L.tensorPow e) (t.val e))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            g.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hh : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, V.ι ''ᵁ (h ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            h.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e))) :
    X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/SectionRingQuotientChartOverlap.lean`.
The node now attaches to
`WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlap`, declaration
`AlgebraicGeometry.Scheme.Modules.sectionRing_quotient_charts_overlap`. The upstream
module's theorem has the same hypotheses and conclusion and already has a complete
proof. No consumer imports the Sheaf duplicate: the existing compatible-charts
consumer uses the upstream module, so no adaptation is required.

The retained upstream signature, verbatim:

```lean
theorem sectionRing_quotient_charts_overlap
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d e : ℕ) (s : sectionRingGrade L d) (t : sectionRingGrade L e)
    (hd : 0 < d) (he : 0 < e) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (hV : (V : Set X) = nonvanishingLocus (L.tensorPow e) (t.val e))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ), 0 < e → ∀ (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            g.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hh : ∀ (e : ℕ), 0 < e → ∀ (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, V.ι ''ᵁ (h ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            h.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e))) :
    X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h
```

A sandbox check importing the adopted source module and checking the theorem's
signature compiles successfully through `lcompile.py`; its proof uses only the
permitted standard axioms.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap | F8 | Duplicate withdrawn; node attached to upstream theorem. |
| WeilConjectures.AlgebraicGeometry.AmpleProjCompatibleCharts | unclaimed | Unchanged existing upstream consumer; already imports the retained theorem. |

The downstream tool reports zero downstream modules. A scan of both library roots
and quarantined Lean sources found no remaining importer of the
withdrawn Sheaf module. The DAG parent `lem-sc-ample-proj-compatible-quotient-charts` already attaches to
the unchanged upstream compatible-charts consumer, whose proof applies the upstream
overlap theorem. Its dependency ID stays in place. The unit route and all mathematical
proof dependencies stay unchanged; only the duplicate implementation is removed.

## Status

landed 20261020T153003-L-2859582 2026-10-20 (merge of deliver/F8/Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap)
