## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableEtaleKernelRelation` states
`AlgebraicGeometry.AlgebraicSpace.representable_etale_kernel_relation`, with a
single `sorry` proof and no new definitions. The node changes only in `lean`.

Sources read: `literature/stacks-project/spaces.tex`, Tag 0262,
`lemma-space-presentation`, especially the first proof paragraph (lines 1192ff);
`sites.tex`, Tag 00W2, `lemma-limit-sheaf` (lines 1680ff). As the node explicitly
says, only the representing map is assumed representable, surjective and étale;
the argument does not need the ambient sheaf to be an algebraic space. The
source's scheme-test definition gives surjectivity of both projections as well
as their étaleness.

Hypotheses and clauses, in node order:

- `S : Scheme.{u}` is the base scheme. `F : Sheaf
  (Scheme.fppfTopology.over S) (Type u)` is a sheaf of sets on the big fppf
  over-site. `U R : Over S` are arbitrary schemes over this base.
- `yoneda.obj U` is exactly `T ↦ (T ⟶ U)` in `Over S`; its sections are
  S-morphisms. `p : yoneda.obj U ⟶ F.obj` is the given natural transformation.
- `hrep : IsRepresentable p`, `hsur : IsSurjective p`, and `het : IsEtale p`
  are the dependency's scheme-test predicates, not a new atlas predicate.
- `s t : R ⟶ U` are S-morphisms. `hR : IsPullback (yoneda.map s)
  (yoneda.map t) p p` says that this particular cone represents the kernel pair.
  It is expressed in presheaves: the sheaf forgetful functor creates and
  reflects limits, so this is exactly the asserted sheaf pullback condition.
- The first conjunct supplies `β T : (T ⟶ R) ≃ {ab | p.app (op T) ab.1 =
  p.app (op T) ab.2}` for every test scheme. Its first law specifies
  `(β T r).val = (r ≫ s, r ≫ t)`, so these are the stipulated maps, not
  arbitrary bijections.
- Its second law specifies compatibility for every `g : T' ⟶ T` with
  restriction, namely precomposition on each component. Equality of the
  underlying pairs is equality in the displayed subtype, by proof irrelevance.
- `Mono (pullback.lift s.left t.left (s.w.trans t.w.symm))` states monicity
  of the actual scheme morphism R → U ×_S U. Here `s.w` and `t.w` are the
  commuting S-triangles, so the compatibility proof has the required type.
- `∀ T, Equivalence (fun a b ↦ ∃ r, r ≫ s = a ∧ r ≫ t = b)` says precisely
  that the image on T-points is an equivalence relation. The β law already
  identifies this image with equality of p-values.
- `Surjective s.left ∧ Etale s.left ∧ Surjective t.left ∧ Etale t.left`
  gives both geometric properties for both underlying scheme projections.
- `∃ d : U ⟶ R, d ≫ s = 𝟙 U ∧ d ≫ t = 𝟙 U` gives the diagonal. The
  bijection makes this the unique such morphism and determines its action on
  all T-points to be the diagonal pair.
- `∃ i : R ⟶ R, i ≫ s = t ∧ i ≫ t = s ∧ i ≫ i = 𝟙 R` gives the
  factor interchange and its involutivity. Precomposition with every test
  section gives exactly the swap of the two components.
- There is no `IsAlgebraicSpace F` or representable-diagonal hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace.IsRepresentableWith`,
  `IsRepresentable`, `IsSurjective`, `IsEtale`. Their actual signatures quantify
  over `Over S` and presheaves valued in `Type u`; the theorem uses those exact
  universes and predicates. No repair or copied definition is needed.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.lift` (and its two projections in the interpretation).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- Proof imports: `Mathlib.CategoryTheory.Sites.Limits` supplies
  `Sheaf.isSheaf_of_isLimit` and `Sheaf.createsLimitsOfShape`, as recorded by
  `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`.
  `WeilConjectures.Mathlib.CategoryTheory.Yoneda` supplies
  `Functor.RepresentableBy.existsUnique_iso`, already attached upstream to
  `lem-pc-representable-unique`. The Mathlib match's `Yoneda.fullyFaithful` and
  `Functor.FullyFaithful.isoEquiv` were also read.

Edge cases checked mathematically before drafting: the empty scheme U (all
sectionwise statements and identity maps still make sense, including tests
with no U-sections); p an isomorphism (the diagonal kernel relation); repeated
sections a=b; arbitrary test morphisms including identities; and a sheaf F with
no representable-diagonal hypothesis. The theorem contains no nonemptiness,
separation, finiteness, or extra universe equality assumptions. A choice of β
is only an existential assertion in a theorem, with its maps prescribed; it
introduces no hollow construction.

Searches actually run with `msearch.py Q40 <item>`:

- LeanFinder: `A represented kernel pair of a representable surjective etale
  scheme map to an fppf sheaf is a natural equivalence relation with etale
  surjective projections`. Eight hits, including Zariski local representability
  and étale-site declarations; no theorem with all the item's clauses.
- Loogle: `"IsKernelPair"`. Twelve generic kernel-pair hits. These do not give
  the geometric scheme-test projection properties or the full asserted result.
- grep: `IsKernelPair|kernel.*relation.*[Ee]tale|[Ee]tale.*kernel.*relation`.
  Twenty-four Mathlib hits on generic kernel pairs, regular epimorphisms and
  scheme effective epimorphisms; no exact theorem.
- LeanSearch: `The represented kernel pair of a representable surjective
  etale map to an fppf sheaf has surjective etale projections`. Eight hits,
  mostly generic kernel pairs and an unrelated ring-map result; no exact match.
- Direct `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for
  `kernelRelation|kernel_relation|KernelRelation|Representable.*Etale|
  representable.*[Ee]tale|SchemeTest`, then kernel-pair spellings. The nearby
  `etale_atlas_presentation` requires an algebraic space and sheafification
  data and lacks the explicit β/diagonal/involution clauses.
  `etale_relation_kernel_pair` is the converse direction from a relation
  quotient. Neither states this theorem. Searching the item id in
  `lean/WeilConjectures` found no attachment. Searching the proposed declaration
  and module names there, in `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no collision. No new nodes were needed.

Validation: `scompile.py Q40 lem-a1-representable-etale-kernel-relation
<module path>` passed both sandbox and library module checks, with no errors
or unexpected warnings. All variables and the universe are explicitly bound;
there are no diagnostic commands or local notation/instances in the module.
No statement dispute or node correction.

## Second reading by Q40

Self-check with the node and module open; the dispatched brief prohibits
starting another agent, and independent delivery review belongs to the
maintainer. Checked each correspondence listed above against the actual
signature. In particular the monomorphism is in schemes into the relative
scheme pullback, not merely a mono into a presheaf product. The β maps are
specified by both projections, their target is the exact equality fibre,
and the restriction equation quantifies over every S-morphism. The relation
uses witnesses in the given R, both projection properties are included, and
the diagonal and swap equations have the correct composition order. The
hypothesis is an arbitrary fppf sheaf rather than an algebraic space. No
mismatch was found and no statement change was made. This self-check does
not claim to be an independent worker review.
