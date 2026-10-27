## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceLocallySeparated` states all three
permanence clauses of `lem-sfb-space-locally-separated-base-change` in three named
theorems. All three proofs are `sorry`. There are no definitions, new nodes,
dependency repairs, or statement corrections. Only the item's `lean` field changes.

Clause and hypothesis correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}` in every theorem. The arbitrary
  universe `u` follows the existing algebraic-space interface; it does not constrain
  the base, test schemes, or spaces beyond that interface.
- Algebraic spaces over S are `X Y Y' : AlgebraicSpace S` for base change, and
  `X Y Z : AlgebraicSpace S` for composition. Their morphisms `f`, `g` are morphisms
  in the existing full subcategory; `f.hom.hom` is the underlying natural transformation.
- The node's definition of immersion is expressed by the existing
  `IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)`. This quantifies over
  **every** scheme T over S and every map h_T to the target, with a scheme U,
  projection p, and a genuine representing pullback square. Scheme `IsImmersion`
  agrees with closed immersion followed by open immersion by
  `AlgebraicGeometry.isImmersion_iff_exists` in Mathlib's Immersion module.
  Thus representability is included, rather than separately assumed.
- The node's local-separatedness condition is precisely that predicate applied to
  `pullback.diagonal f.hom.hom`; its target is X ×_Y X, not X ×_S X.
  This is written out rather than introducing a duplicate predicate.
- Arbitrary base change Y' → Y is the unrestricted `g : Y' ⟶ Y` in
  `locallySeparated_baseChange`. The projection X ×_Y Y' → Y' is
  `pullback.snd f.hom.hom g.hom.hom`. The conclusion applies the same immersion
  test to this projection's own relative diagonal. There is no representability,
  flatness, finite-type, quasi-compactness, or separation condition on g.
- Composition is `locallySeparated_comp`: `hf` and `hg` give the two immersion
  diagonals, and the conclusion gives the immersion diagonal of
  `f.hom.hom ≫ g.hom.hom`, which is g composed with f. No extra conclusion is added.
- Every morphism of schemes over S is covered by
  `locallySeparated_yonedaMap`: `{X Y : Over S} (f : X ⟶ Y)` and the conclusion
  concerns `pullback.diagonal (yoneda.map f)`. The functor of points is exactly
  h_X(T) = Hom_S(T,X). No choice of a scheme presentation or algebraic-space
  embedding is needed because the property is already a predicate on these
  presheaf maps. Their natural transformations are precisely the morphisms of
  the corresponding algebraic spaces. Every absolute scheme morphism is covered
  by taking S to be its target and the target structure map to be the identity.
- Sheaf fibre products are rendered by the presheaf fibre products: limits of
  sheaves are computed on underlying presheaves. The existing
  `fibreProduct_isAlgebraicSpace` supplies algebraicity and the full-subcategory
  universal property, so no additional algebraicity hypothesis is imposed.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`. Read their structure declarations and docstrings.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `IsRepresentable` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`. Read the entire module and the full
  signatures; the existing predicate directly supplies the notion the statement needs.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; its `mathlib_match` also
  identifies `IsImmersion` and `isImmersion_iff_exists` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`. Read the signatures and docstrings.
  The immersion module publicly imports the closed-immersion interface.
- `lem-trf-space-fibre-products-etale-covers`: `fibreProduct_isAlgebraicSpace`
  in `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`, read in full.
  It provides the sheaf pullback's algebraicity and universal property.
- Proof dependencies already stated are imported: the scheme permanence leaf
  through `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `FinitePresentation`, and
  `Immersion` (whose imports provide finite type, quasi-compactness,
  quasi-separatedness, separatedness and closed immersion); the scheme diagonal
  and immersion base-change leaves through `Immersion`; scheme fibre products
  through its public imports; Yoneda through `Mathlib.CategoryTheory.Yoneda`.
- `lem-sfb-space-immersion-affine-tests` currently has neither `lean` nor a
  `mathlib_match`. It is a proof dependency only and is not needed to type these
  statements, so it has no module to import. It remains cited in the proof docstrings.

Sources checked directly: `literature/stacks-project/spaces-morphisms.tex`,
`definition-separated`, `lemma-base-change-separated` (03KL),
`lemma-composition-separated` (03KQ), and `lemma-match-separated` (03KY).
These agree with every clause. The current blueprint unit in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
is the six-functor stability unit; this item is its supporting geometric input,
not the unit statement itself. No unit or node correction is needed.

Edge cases checked before writing: empty X, empty Y', identity base change,
identity f or g, non-separated schemes and non-separated base schemes. Empty
pullbacks and their diagonals remain covered by the universal scheme tests.
For schemes with nonclosed diagonal the conclusion asks for an immersion only,
so it does not silently assert separatedness. No field, characteristic,
nonemptiness, connectedness, or quasi-separatedness assumption occurs.
The relative diagonal convention was checked against the source and the two
pullback projections; the chosen second projection has target Y'.

Searches actually run using `msearch.py Q137 lem-sfb-space-locally-separated-base-change`:

- `leanfinder`: “Locally separated morphisms of algebraic spaces are stable under
  base change and composition”. Eight hits, all scheme `IsSeparated` results
  (including `IsSeparated.stableUnderComposition` and
  `IsSeparated.isStableUnderBaseChange`); none states this algebraic-space theorem.
- `loogle`: `"LocallySeparated"`. Zero hits.
- `grep`: `AlgebraicSpace|LocallySeparated|locallySeparated`. Zero Mathlib hits.
- `leansearch`: “Locally separated algebraic space morphisms have an immersion
  diagonal stable under base change”. Eight hits: scheme separatedness,
  `IsImmersion.instDiagonalScheme`, and the general categorical diagonal
  base-change result; none states the requested algebraic-space result.
- `rg` in `lean/WeilConjectures` for `AlgebraicSpace|LocallySeparated|locallySeparated`
  and `grep -rn` for this item id: no hits. The upstream name index also has no
  `IsLocallySeparated`/`locallySeparated` hit.
- `rg` in `lean/Sheaf` for local-separatedness names and the scheme-test immersion
  expression found existing hypotheses in `LocallySeparatedGroupSpaceScheme`,
  `FlatProperPicardAlgebraicSpace`, and polarization material, not permanence
  statements or a predicate definition. The group-space theorem uses exactly
  the same expanded immersion test; its diagonal is absolute because it treats
  a space over a field. It does not replace the relative theorem here.
- All three proposed declaration names were searched in project, upstream and
  Mathlib sources: no collision.

Validation: `scompile.py` compiled both the sandbox and library module modes
successfully under the prescribed 60-second per-file limit. The final module
also sets `autoImplicit false`, so all binders and universe variables are explicit.

## Second reading by Q137

Author's self-check, not an independent review: reopened the node and final module.
Matched the arbitrary scheme S, the relative diagonal, every scheme base-change
immersion test, the projection to Y', both composition hypotheses, and the
scheme-functor-of-points case with the clauses listed above. The diagonal in the
base-change conclusion belongs to `pullback.snd`, not to the original map, and
composition uses the order f then g. No added hypothesis or omitted clause was
found. No definitions or helper existence claims are hidden in a proof. The
maintainer's independent review remains separate from this self-check.
