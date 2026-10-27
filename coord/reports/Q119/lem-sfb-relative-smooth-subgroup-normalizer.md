## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RelativeSmoothSubgroupNormalizer`
states `AlgebraicGeometry.exists_relative_smooth_subgroup_normalizer`, with `sorry`
as its whole proof. The only further declaration is the fully written predicate
`AlgebraicGeometry.IsRelativeGroupSchemeNormalizer`, spelling out the normalizer
functor which this very node introduces. This is a helper for the owning notion,
not a new independent mathematical object. It contains no postponed proof or
chosen data. The node changes only in `lean`; its statement and split are unchanged.

Source checked online: Brian Conrad, *Reductive group schemes*, Proposition 2.1.6,
printed p.61 and proof pp.62--63,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . The displayed normalizer
is an equality normalizer. Example 2.1.10 on p.63 explains why flatness must not be
asserted. The theorem docstring carries all seven steps of the accepted DAG proof.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A is a commutative ring and S = Spec A | `(A : Type u) [CommRing A]`, `Spec (.of A)` |
| Group schemes over S, with multiplication, identity and inverse diagrams | `G H : Grp (Over (Spec (.of A)))`; Mathlib's bundled group objects include `GrpObj` and its diagrams |
| G is affine | `[IsAffine G.X.left]`; over an affine base this is equivalent to an affine structure morphism |
| G is smooth | `[Smooth G.X.hom]` |
| G is of finite presentation | `[LocallyOfFinitePresentation G.X.hom]`; quasi-compactness and quasi-separatedness follow because both source and base are affine, so no case is excluded |
| H embeds as a closed subgroup | `i : H ⟶ G` is a morphism of group objects, and `[IsClosedImmersion i.hom.hom.left]` makes it an embedding |
| The closed subgroup embedding is finitely presented | `[LocallyOfFinitePresentation i.hom.hom.left]`; a closed immersion is automatically quasi-compact and separated |
| H is smooth over S | `[Smooth H.X.hom]` |
| Its fibres are nonempty and geometrically connected | `[GeometricallyConnected H.X.hom]`; Mathlib tests connectedness on every field-valued base change, and its `ConnectedSpace` includes nonemptiness. Testing algebraic closures of residue fields is equivalent |
| Every S-scheme W and point g in G(W) | `W : Over S`, `g : W ⟶ G.X` in the helper predicate |
| Equality c_g(H_W) = H_W as subgroup functors on all W-schemes | For every `U : Over S` and `f : U ⟶ W`, equality of `Set.range (fun h => (f ≫ g) * (h ≫ i.hom.hom) * (f ≫ g)⁻¹)` and `Set.range (fun h => h ≫ i.hom.hom)` |
| N is represented as a subgroup scheme of G | `∃ (N : Grp (Over ...)) (j : N ⟶ G)` and `IsRelativeGroupSchemeNormalizer i j` |
| The representing map is a closed immersion of finite presentation | `IsClosedImmersion j.hom.hom.left` and `LocallyOfFinitePresentation j.hom.hom.left`; the other two finite-presentation conditions follow from closedness |
| N is finitely presented over S | `LocallyOfFinitePresentation N.X.hom ∧ QuasiCompact N.X.hom ∧ QuasiSeparated N.X.hom` |
| The point correspondence is a natural bijection | The predicate is existence of a point factorization through j iff the normalizing condition. Closedness of j implies monicity and hence uniqueness. Composition gives the naturality in W |
| Canonical closed inclusion H into N | `∃! h : H ⟶ N, IsClosedImmersion h.hom.hom.left ∧ h ≫ j = i`; h is a group homomorphism and uniqueness over G specifies the canonical inclusion |
| Arbitrary S' to S | `∀ (S' : Scheme.{u}) (f : S' ⟶ Spec (.of A))`; no flatness, reducedness or affineness hypothesis |
| Normalizer commutes with base change | First, the pulled-back embeddings satisfy `IsRelativeGroupSchemeNormalizer`. Next, for every closed representative `j' : N' ⟶ G_S'` of that normalizer, `∃! e : N_S' ≅ N', e.hom ≫ j' = j_S'` |
| The base-change map is natural/canonical and is an isomorphism | The equality over G_S' and unique isomorphism specify the canonical comparison, independently of the representative. Pullback itself already supplies one, so this clause is not vacuous |
| No flatness or smoothness asserted for N | Neither occurs among the conclusions |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Scheme`, and
  `Scheme.Hom` (def-weil-affine-spectrum and def-pc-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (def-sbc-locally-finite-presentation),
  available through the public Smooth import.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, and the
  morphisms of bundled groups (def-sc-group-scheme). The field-specific terminology
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` was read; its general
  Mathlib group-object definition already works over arbitrary schemes, so the
  field-specific closed-subgroup class is not imposed on a general ring base.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (def-weil-connected-scheme).
  `Mathlib.AlgebraicGeometry.Geometrically.Connected` supplies the existing
  `GeometricallyConnected` predicate, using precisely that connectedness notion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` (def-pc-fibre-product). These are used in
  `Over.pullback` via its recorded source, not recreated privately.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`; its `mapGrp`
  is the existing transport of group objects by finite-product-preserving functors.
  It uses actual scheme fibre products and the pulled-back group operations.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `Hom.group`, activated by
  `open scoped MonObj`, gives the pointwise group multiplication and inverse.

The stated proof dependencies are imported through Smooth (including Noetherian
and finite-presentation results), ClosedImmersion (base-change stability), Gluing,
ZariskisMainTheorem (proper monomorphism criterion), the category theory imports
(Yoneda), and FiniteStability (finite-presentation base change/composition).
The four auxiliary proof dependencies about the Noetherian model, finite jets,
universal jet density and the finite-source factorization locus had no Lean record
or Mathlib match when read. As proof dependencies, they are retained in the DAG and
proof docstring; there is no missing statement dependency and no private restatement.

Searches performed before writing:

- `msearch.py leanfinder`: “The normalizer of a smooth geometrically connected
  subgroup scheme is a finitely presented closed subgroup and commutes with
  arbitrary base change”. Eight hits, including `Subgroup.normal_in_normalizer`,
  topological normal-core results and groupoid normality; none represents this
  relative scheme functor.
- `msearch.py loogle`: `"Scheme", "normalizer"`: zero hits.
- `msearch.py grep`: `normalizer|transporter`, `AlgebraicGeometry`: zero hits.
- `msearch.py leansearch`: “Normalizer functor of a smooth geometrically connected
  closed subgroup scheme is represented by a finitely presented closed subgroup”.
  Eight abstract subgroup-normalizer hits, none with the scheme representability.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, including the item id and the
  proposed full declaration names. No duplicate declaration. Existing Borel and
  Cartan-normalizer statements are over fields with different hypotheses and
  conclusions; `RankOneRoots.normalizer` gives rational normalizer elements, not
  this relative representing scheme.
- DAG definition-node search and `tools/blueprint_refs.py search normalizer`:
  no independent existing relative-normalizer definition or duplicate blueprint
  node was found. No new definition node or dependency repair is needed.

Edge cases checked before writing: the zero ring/empty base is allowed (no
`Nontrivial A` or nonempty-base hypothesis); nonempty fibres are required only
above actual base points. H = G gives N = G; the identity subgroup gives N = G.
Disconnected G is allowed. Nonreduced test schemes and nonflat or nonaffine base
changes are included. The inner quantifier covers every W-scheme, not just points
of W or field extensions, so infinitesimal normalizer conditions are retained.
All scheme and test objects use the same ambient universe u; there is no independent
smaller test universe. No statement defect or STATEMENT-DISPUTED issue was found.

Validation: `scompile.py Q119 lem-sfb-relative-smooth-subgroup-normalizer` checked
both its private sandbox form and its actual library module form successfully;
the actual module compile took 1.8 seconds. No errors or unexpected warnings.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
