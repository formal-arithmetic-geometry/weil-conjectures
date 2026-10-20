# AlgebraicGeometry.Scheme.Modules.sectionRing_overlap_sheaf_map

## Reason

Retirement item in coord/retire-items.tsv, under the human's 2026-10-20 hand-off.
The adopted source library already proves the sheaf-map comparison, with the same
objects and conclusion and fewer hypotheses. The Sheaf copy duplicates its public
name. Retire the copy and use the source theorem at its only consumer. No adopted
source module or target statement changes.

## Old

The retired Sheaf module declares:

```lean
theorem sectionRing_overlap_sheaf_map
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
              ⊤)).op (ξ.val (n • e)))
    (hbase : (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base) :
    ∀ W, (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).app W ≫
      (U ⊓ V).toScheme.presheaf.map
        (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj W)).op =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).app W
```

Its consumer imports Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf
and ends its proof with:

```lean
  exact sectionRing_overlap_sheaf_map X L d e s t hd he U V hU hV g h hg hh hbase
```

## New

The existing source-library theorem, unchanged, is:

```lean
theorem sectionRing_overlap_sheaf_map
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
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
              ⊤)).op (ξ.val (n • e)))
    (hbase : (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base) :
    ∀ W, (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).app W ≫
      (U ⊓ V).toScheme.presheaf.map
        (eqToHom congr((TopologicalSpace.Opens.map $hbase.symm).obj W)).op =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).app W
```

The consumer imports WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf
and calls:

```lean
  exact sectionRing_overlap_sheaf_map X L d s hd U V hU g h hg hh hbase
```

The dropped parameters e, t, he and hV were unused in the original proof. The
consumer's own statement retains them and still uses them in the base-map
comparison. The node's mathematical statement stays unchanged: the stronger
upstream theorem supplies it directly. Its lean attachment records the upstream
signature verbatim. The retired file is listed in deleted.txt.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap | unclaimed | Switch the private proof import and remove four unused arguments from the final theorem application; its signature and visibility are unchanged. |
| Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf | D4 | Retire the duplicate module; node now points to the unchanged upstream theorem. |

The downstream.py --uses scan found only the listed consumer and the retiring
module itself. A repository-wide scan found no other importers. Switching only
the import produced an application type mismatch at line 93: e : Nat was supplied
where sectionRingGrade L d was expected. Removing the obsolete arguments fixes it.
No target signature or definition changes, so target statement review is not reopened.

## Status

landed 20261020T135357-L-1816705 2026-10-20 (merge of deliver/D4/Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf)
