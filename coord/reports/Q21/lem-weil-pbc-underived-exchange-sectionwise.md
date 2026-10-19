## Worker report

The module `lean/Sheaf/AlgebraicGeometry/UnderivedExchangeSectionwise.lean` states
`AlgebraicGeometry.underivedExchangeSectionwise` and defines the helper
`AlgebraicGeometry.sectionwiseBaseChangeHom`. The theorem proof is `sorry`, as required
for stage 2. The helper is the canonical morphism
`f'.Etale.obj V ⟶ g'.Etale.obj (f.Etale.obj W)` induced by the Cartesian square and
`a : V ⟶ g.Etale.obj W`, with the pullback lift and its over-`X'` condition written
explicitly.

The theorem has the exact node hypotheses: schemes `X' X Y' Y : Scheme.{u}`, maps
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y`, a
`ChosenCartesianSquare g' f' f g`, and an abelian sheaf
`F : Sheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})`. Its first conjunct quantifies
`V : Y'.Etale`, `W : Y.Etale`, `a : V ⟶ g.Etale.obj W`, and a section `s` of
`f_*F` on `W`; it evaluates `Etale.baseChangeMap` on the actual left-Kan-extension
unit generator followed by `toSheafify`, and equates this with the `g'` adjunction unit
restricted along `sectionwiseBaseChangeHom`. This is the sectionwise representative
rule and records independence after sheafification. Its second conjunct is exactly the
specified adjunct equation for the underived exchange map, using
`Etale.squareUpperStarIso` and the counit of the `f` inverse/direct-image adjunction.
No hypotheses or clauses are added or omitted.

Dependencies used by the module are:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`,
  `AlgebraicGeometry.ChosenCartesianSquare`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar` and
  `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`;
- `WeilConjectures.SixFunctors.BaseChange.Square`,
  `AlgebraicGeometry.Etale.baseChangeMap`,
  `AlgebraicGeometry.Etale.squareUpperStarIso`, and
  `AlgebraicGeometry.Etale.upperStar_map_baseChangeMap_app_counit`;
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
  `AlgebraicGeometry.etaleInverseImageAlgebraicStructures`;
- Mathlib `CategoryTheory.presheafToSheaf` and `CategoryTheory.toSheafify` from
  `Mathlib.CategoryTheory.Sites.Sheafification`.

I checked identity Cartesian squares (the formula reduces to ordinary restriction),
`F = 0`, empty étale test objects, and the square with `X = Y = Spec k` and
`X' = Y' = A¹_k`; the helper uses the adjunction unit before restriction, so it does
not incorrectly require `A` to be an object of `X`'s étale site.

Searches made: `msearch.py Q21 lem-weil-pbc-underived-exchange-sectionwise leanfinder`
for the sectionwise exchange formula (generic sheafification and pullback hits only);
`msearch.py ... loogle "CategoryTheory.mateEquiv, CategoryTheory.sheafificationAdjunction"`
(no hits for the complete statement); `msearch.py ... grep
"baseChangeMap|exchange|sheafPullback.*(app|section)" CategoryTheory/Sites`
(generic Mathlib site infrastructure only); and `rg` over
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project `lean/Sheaf`
for the item id, `underivedExchangeSectionwise`, `sectionwiseBaseChangeHom`, and
`baseChangeMap`. The source contains only the categorical `baseChangeMap` and its
counit theorem; no declaration states this complete sectionwise theorem, so this is
not a duplicate.

No statement correction, new definition node, dependency repair, or
`STATEMENT-DISPUTED` flag is needed. The module compiled cleanly with `scompile.py`.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
