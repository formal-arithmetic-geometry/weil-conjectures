# AlgebraicGeometry.Etale.exists_restricted_affine_complex_system_natural

## Reason

Complete the explicit retirement assignment in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural`. Its upstream twin
already contains the same public theorem, with a byte-identical signature, the
same two public imports and two proof imports, and the identical public proof
body. The historical DIFFERENT classification refers to the private
`presentation_of_data` helper; the local version prefixes some unused argument
names with underscores. Both helpers package the same witnesses.

Withdraw the duplicate Sheaf module and attach its existing DAG node to the
upstream declaration. This preserves the mathematical obligation and its full
proof route. The sole live consumer already imports the upstream twin. No live
or quarantined source imports the retiring module. No source-library file is
changed.

## Old

The declaration below is provided by
`lean/Sheaf/AlgebraicGeometry/RestrictedAffineComplexSystemNatural.lean`, and the
node `lem-sbc-restricted-affine-complex-system-natural` points to that file.

```lean
theorem exists_restricted_affine_complex_system_natural {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left] :
    ∃ (T : (Iᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{v + 1}) (B : Cocone T),
    EtaleComplexCohomologyPresentation T B ∧ ∃
    (restrictionIso : ∀ i : (Iᵒᵖ)ᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop.unop)).hom p
        (F i.unop.unop) U ≅ T.obj i)
    (restrictionLimitIso : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅ B.pt),
    (∀ (i : (Iᵒᵖ)ᵒᵖ)
      (t : rawAffineRestrictedCohomology (D.obj (op i.unop.unop)).hom p
        (F i.unop.unop) U),
      B.ι.app i ((restrictionIso i).hom t) = restrictionLimitIso.hom
        (rawAffineRestrictedCohomologyMap (c.π.app (op i.unop.unop)).left
          (D.obj (op i.unop.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop.unop))) p
          (F i.unop.unop) (colimit H)
          ((eH i.unop.unop).inv ≫ colimit.ι H i.unop.unop) U t)) ∧
    (∀ {i j : I} (f : i ⟶ j)
      (t : rawAffineRestrictedCohomology (D.obj (op i)).hom p (F i) U),
      T.map ((opOpEquivalence I).inverse.map f) ((restrictionIso (op (op i))).hom t) =
        (restrictionIso (op (op j))).hom
          (rawAffineRestrictedCohomologyMap (D.map f.op).left
            (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
            (F i) (F j) (φ f) U t))
```

## New

The exact same signature and complete proof remain in
`lean/WeilConjectures/AlgebraicGeometry/RestrictedAffineComplexSystemNatural.lean`.
The node's `lean.module` and `lean.file` point there, and `lean.existing` is true.
The Sheaf path is listed in `deleted.txt`; the delivery tool publishes the
standard empty `module` stub. No replacement declaration is introduced.

All four proof dependencies and all statement dependencies stay. In particular,
this is not a claim that the coefficient-system or generic map-coherence
obligations have been proved without their existing dependencies.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | X7 | Retire the duplicate; its theorem is retained upstream. |
| WeilConjectures.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | unclaimed | Canonical replacement; identical public signature and proof, no edits. |
| WeilConjectures.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | Sole live theorem consumer, already imports the canonical replacement; no adaptation. |

`tools/downstream.py` reports zero modules downstream of the Sheaf copy and its
own declaration as the only named use within that closure. A separate scan of
both library roots and `quarantine/` confirms zero imports of that copy.
The historical Sheaf consumer named in the retirement row is already absent.

The sole actual dependency parent is
`lem-sbc-abelian-raw-cocone-complex-presentation`. Its dependency edge is retained,
and its Lean attachment already points to the upstream consumer above.
The two other nodes containing this id mention it in history/docstrings only;
they do not have dependency edges to it. The unit `sk-lem-failure-field` and its
realized route are unchanged. No target statement or definition changes.

The unchanged upstream proof, its unchanged direct consumer and the exact-signature
probe all compile through `lcompile.py` (26.3 s, 48.5 s and 9.5 s respectively).
The upstream theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

## Status

landed 20261025T164744-L-1073822 2026-10-25 (merge of deliver/X7/Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural)
