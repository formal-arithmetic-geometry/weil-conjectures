## Worker report

The module `Sheaf.AlgebraicGeometry.OpenSeparatedEtalePushout` states
`AlgebraicGeometry.AlgebraicSpace.exists_openSeparatedEtalePushout`, with its whole
proof postponed by `sorry`. No definition, new node, dependency repair, or statement
correction is required. The source is Stacks Tag 0DVJ,
`literature/stacks-project/spaces-pushouts.tex`, lines 1546–1595, read in full.
The module docstring and theorem docstring contain its source and blueprint ID;
the theorem docstring expands all seven steps of the node's proof.

Hypotheses and conclusions, clause by clause:

- The base scheme is `{S : Scheme.{u}}`; the spaces over S are
  `(W Z V : AlgebraicSpace S)`. `universe u` is explicit and `autoImplicit` is false.
  This uses exactly the existing algebraic-space scheme-test universe convention.
- The S-morphisms are `(j : W ⟶ Z) (q : W ⟶ V)` in the category of spaces over S.
- The open-subspace hypothesis on j is `hj : IsRepresentableWith
  (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`. This is precisely the predicate
  in the recorded `OpenSubspace`, on the given inclusion. It allows a presented
  open immersion, equivalent to its image subfunctor, without requiring a chosen
  subfunctor presentation. No second predicate or private definition is introduced.
- Chartwise etaleness of q is `hq : IsChartwiseEtale q`, using the recorded definition.
- Separatedness is `hsep : IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal q.hom.hom)`.
  This asserts representability and closed immersion on every scheme base change
  of the relative diagonal; it does not require q itself to be representable.
- The output is `∃ (Y : AlgebraicSpace S) (a : Z ⟶ Y) (b : V ⟶ Y)`.
- That b identifies V with an open subspace is the same scheme-test open-immersion
  predicate on `b.hom.hom`. Such maps are monomorphisms by the recorded open-chart
  tests, so this is identification with an open subfunctor, not just an open map.
- The right-hand map is chartwise etale by `IsChartwiseEtale a`.
- `IsPullback j.hom q.hom a.hom b.hom` includes the equation
  `j.hom ≫ a.hom = q.hom ≫ b.hom`, hence aj = bq by faithfulness. Its limiting
  square assertion says exactly that the canonical comparison W -> Z times_Y V,
  with the prescribed projections j and q, is an isomorphism. Sheaf pullbacks
  are the space fibre products by the recorded fibre-product theorem. No arbitrary
  isomorphism is substituted for the comparison.
- For every `C : ClosedSubspace Y`, `IsReduced (C.val : AlgebraicSpace S)` and
  `pointImage C.val.arrow.hom.hom = (pointImage b.hom.hom)ᶜ` specify exactly the
  reduced closed complement in the atlas topology. Existence and uniqueness are
  the recorded reduced-closed-support theorem (the open image has closed complement).
  The conclusion `IsIso (Limits.pullback.snd a.hom C.val.arrow.hom)` refers to the
  actual canonical sheaf projection Z times_Y C -> C. It asserts no reducedness of
  the pullback. Quantifying over presentations of the unique complement avoids
  choosing one or weakening the clause through an unspecified projection.
- For every space H and S-morphisms g, h, `j ≫ g = q ≫ h` is compatibility on W.
  `∃! t : Y ⟶ H, a ≫ t = g ∧ b ≫ t = h` is exactly the pushout factorization
  with both restrictions prescribed, including its uniqueness.
- There are no affine, Noetherian, quasi-compact, finite-type, nonempty, or
  representability hypotheses beyond the hypotheses stated in the node.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`; the full subcategory has the sheaf maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`:
  `AlgebraicSpace.OpenSubspace`, whose existing scheme-test predicate is used above.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointImage`, `AlgebraicSpace.pointTopologicalSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicSpace.IsChartwiseEtale` (definition, lines 47–49).
- `Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`:
  `AlgebraicSpace.exists_unique_reduced_closed_subspace`, with its public dependencies'
  `AlgebraicSpace.ClosedSubspace` and `AlgebraicSpace.IsReduced`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and its sheaf fibre-product interface.
- `def-weil-size-convention` has an explicit convention record and no declaration;
  the explicit level u follows it, with no extra size constraint.

All recorded statement modules are public imports. The already stated proof-only
nodes are imported without `public`: `SpaceOpenChartTests`,
`AlgebraicSpacePointOpenCalculus`, `AlgebraicSpaceCoproduct`,
`FppfSheafCoproductPartition`, `ChartwiseEtalePermanence`, and Mathlib's
`AlgebraicGeometry.Morphisms.Basic` and `AlgebraicGeometry.Limits` for etale
coproducts and scheme coproduct families. The proof-only nodes
`lem-per-space-etale-relation-quotient` and `lem-sfb-space-etale-monomorphism-open`
have no recorded module on the read base, so there is no module to import for them.
They remain named in the proof docstring and the unchanged DAG proof dependencies.

Edge cases checked mathematically before writing: W empty gives the disjoint union
of Z and V; Z empty forces W empty and gives Y = V; V empty forces W empty and gives
Y = Z. With j the identity one obtains Y = V, and with q the identity one obtains
Y = Z. A surjective open b has empty closed complement, whose pullback projection
is still an isomorphism. The statement allows all these cases. Nonrepresentable
chartwise etale q is allowed: only its diagonal is tested for closed immersions.
No arbitrary-index coproduct or additional universe binder enters this finite
pushout statement.

Searches for an existing statement:

- `msearch.py ... leansearch "Pushout along an open immersion and a separated etale
  map of algebraic spaces"`: eight hits, scheme open-immersion pullbacks and open
  immersion properties, no algebraic-space pushout theorem.
- `msearch.py ... leanfinder "Pushout of an open immersion and a separated etale
  morphism of algebraic spaces as an elementary distinguished square"`: eight hits
  about scheme open immersions, etale pullbacks, and formally unramified diagonals;
  no matching pushout statement.
- `msearch.py ... loogle "CategoryTheory.IsPushout, CategoryTheory.IsPullback"`:
  twelve categorical pullback/pushout duality and adhesive-category hits, none
  constructing the required algebraic space.
- `msearch.py ... grep
  "separated.*[Ee]tale.*[Pp]ushout|construct_elementary_distinguished|[Ee]tale[Pp]ushout"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for pushout/Pushout finds algebra and categorical
  constructions; the exact item-ID grep returns no occurrence. `rg` in `lean/Sheaf`
  finds affine-thickening and logarithmic pushouts, not this open/etale pushout.
  `AlgebraicSpaceMorphismProperties.MapIsSeparated` was read and agrees with the
  explicitly expanded relative-diagonal hypothesis; no replacement definition is made.
- Exact-name searches for `exists_openSeparatedEtalePushout` and
  `openSeparatedEtalePushout` in `lean/Sheaf`, `lean/WeilConjectures`, and
  `dag/lean_names_upstream.json` returned no declaration.

Validation: prescribed scompile.py compiled the delivered file separately in both
sandbox and library module modes, each in 1.7 seconds, without errors or warnings.
No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q02

This is a second pass by the same worker; the dispatcher forbids starting another
agent, and the maintainer performs the independent review. Reopened the node,
Stacks 0DVJ, the dependency signatures and the delivered file. Checked that j and q
have the correct common source, that hsep is the relative diagonal over V rather
than an absolute diagonal, and that IsChartwiseEtale does not impose representability.
Checked the pullback's leg order j, q, a, b and the closed-complement projection's
leg order a, C -> Y: snd has target C, as required. Checked the complement is the
complement of the image of b, not the image of a, and uses the recorded atlas topology.
Checked the pushout equations a followed by t = g and b followed by t = h, under
compatibility j followed by g = q followed by h. Checked all binders explicitly,
including the universe, and all empty cases listed above. No mismatch or correction
was found. No new node, definition or hidden finiteness assumption was added.
