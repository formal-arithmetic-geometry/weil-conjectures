## Worker report

The module `Sheaf.AlgebraicGeometry.LogRegularPairRegularPullback` states
`AlgebraicGeometry.logRegularPair_regularPullback`, with one `sorry` and no definitions.
No correction to the mathematical statement is needed. The only added statement
 dependency is the already landed `def-per-strict-log-morphism`.

Sources read: ILO Exposé VI 1.1--1.4, printed p.69 (PDF p.75), including the
strict-local stratum definition and the dense triviality locus/divisorial
identification; VII 3.2, printed p.82 (PDF p.88), for the regular-completion
application. Read the current blueprint's
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`,
Step 3: this node is an auxiliary geometric input, not that unit's statement.
The proof docstring follows all seven steps of the node, including the concrete
prelog pushout and sheafification construction, stalk computation, fs charts,
characteristic identification, regular strata, dimension formula and divisorial
identification. Unstated proof nodes remain unstated and are named in that plan;
they are not new hypotheses on this theorem.

Hypotheses and conclusions, clause by clause:

- Locally Noetherian schemes X and Y: `{X Y : Scheme.{u}}` and the two
  `[IsLocallyNoetherian ...]` binders, with the project universe explicit.
- Scheme morphism g: `(g : Y ⟶ X)`.
- Regularity, meaning flat with geometrically regular fibres: `[Flat g]` and
  `hg`. For each `x : X`, every finite field extension `K` of `X.residueField x`
  is quantified using `[Field K] [Algebra (X.residueField x) K]` and
  `[Module.Finite (X.residueField x) K]`. The fibre after that extension is the
  actual `pullback (g.fiberToSpecResidueField x) (Spec.map ...algebraMap...)`,
  required to satisfy the recorded `IsRegularScheme`. This includes the
  identity extension, and adds no finite-presentation or smoothness condition.
  `K : Type u` includes all finite extensions up to isomorphism and the residue
  field itself; no independent smaller universe makes the test vacuous.
- Nowhere dense closed B: write `U : X.Opens`, with `B = (U : Set X)ᶜ`,
  and `hU : DenseRange U.ι`. A closed subset is nowhere dense exactly when its
  open complement is dense. This is the dense-open-immersion interface required
  by the dependency's recorded pair predicate; no reduced or Cartier structure
  is added to the boundary.
- Divisorial fine saturated log regular pair `(X,B)`: exactly
  `hpair : IsDivisorialFineSaturatedLogRegularPair X U.toScheme U.ι hU`.
- The inverse-image boundary is nowhere dense: the conclusion supplies
  `hV : DenseRange (g ⁻¹ᵁ U).ι`. The underlying open is exactly the inverse
  image of U, so its closed complement is exactly `g ⁻¹' B`.
- The inverse-image pair is divisorial fs log regular: the first conjunct is
  the same dependency predicate for Y and `(g ⁻¹ᵁ U).ι`, using `hV`.
- The inverse-image log structure itself is specified, rather than an unrelated
  fs log structure: `MX`, `MY`, `fsX`, `fsY` and the isomorphisms `eX`, `eY`
  give fs log structures with exactly the source and target divisorial sheaves.
  `eX.hom ≫ divisorialStructuralMap U.ι = MX.alpha` and its target analogue
  fix the structural maps. The morphism `f` is an actual `EtaleLogHom` between
  these bundles, with `f.base = g` and `f.IsStrict`.
  The full recorded strictness definition was read: at every geometric point
  the isomorphism on characteristic monoids must have the graph induced by
  `f.sectionMap`. It is the dependency's explicit equivalent criterion for
  MY to be the log structure associated to `g⁻¹ MX`, adjoining precisely the
  units and identifying the already invertible elements. It is not a bare
  Nonempty isomorphism. Structural compatibility and the injective divisorial
  inclusions also determine all section maps of f: after applying eY, a section
  becomes the pullback of its structural regular function. Consequently the
  existential presentation has precisely the canonical inverse-image map.
- Log regularity of that inverse-image structure: the conjunct
  `(FineSaturatedLogScheme.mk Y inferInstance MY fsY).IsLogRegular` is the
  recorded strict-local stratum/dimension predicate, not a new predicate.
- Its triviality locus: `MY.trivialityLocus = (g ⁻¹ᵁ U : Set Y)`.
- The structural divisorial identification with
  `O_Y ∩ j_* O_(Y minus g⁻¹B)^×`: `eY` is an isomorphism to the recorded
  `divisorialLogPresheaf (g ⁻¹ᵁ U).ι` and its structural equation is explicit.
  The isomorphism is between the underlying monoid presheaves; both sides are
  sheaves by `MY.monoidSheaf` and the returned pair predicate.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, including
  its `iff_flat_stalkMap` equivalence.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`
  (local Noetherianity and the upstream stalkwise `IsRegular`).
- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`,
  `divisorialLogPresheaf`, `divisorialStructuralMap`, and their defining
  divisorial sections, geometric stalks, charts and rank/stratum clauses.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `AlgebraicGeometry.EtaleLogStructure`, `EtaleLogHom`,
  `EtaleLogStructure.IsFineSaturated`, `FineSaturatedLogScheme`,
  `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogStructure.trivialityLocus`.
- `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`:
  `AlgebraicGeometry.EtaleLogHom.IsStrict` and its full `CharacteristicRelation`.
  This is the already landed declaration of `def-per-strict-log-morphism`;
  the node is added to stmt_deps, without changing any other node.

Available proof declarations are imported without `public`, including the
geometric stalk comparison, sharp chart, regular closed-fibre ascent, divisorial
structure, and the recorded Mathlib sheafification/flatness/dimension providers.
The three proof nodes with no declaration (`lem-trf-prelog-pushout-log-axiom`,
`lem-trf-prelog-pushout-hom-extension`, `lem-per-regular-geometric-stalk-map`)
are only proof requirements; none is needed to elaborate the statement.

Edge cases checked before drafting and again against the finished signature:
empty Y is permitted (no Nonempty binder; its empty open is dense); empty B
is U = top (trivial characteristic and unit log structure); the empty X
case forces empty Y; no positive characteristic, positive characteristic rank,
finite type, surjectivity, nonempty boundary or nonempty fibre is imposed.
Arbitrary non-smooth regular morphisms, notably completion maps, are included.

Searches actually run with msearch.py for this item:

- LeanFinder: "A regular morphism preserves a divisorial fine saturated log regular
  pair and its inverse image logarithmic structure". Eight hits, including
  regular sequences under localization, `IsPreimmersion.of_isLocalization`,
  normalization and ordinary smoothness/locality declarations; no match.
- Loogle: `"LogRegular"`. Zero hits.
- Mathlib grep: `log.?[Rr]egular|[Ll]og[Ss]cheme` in AlgebraicGeometry. Zero hits.
- LeanSearch: "Pullback of a divisorial fine saturated log regular scheme under a
  flat morphism with geometrically regular fibres is log regular". Eight hits,
  consisting of ordinary scheme pullback, flatness, properness and affineness
  instances; no logarithmic statement.
- `rg` over `lean/WeilConjectures` for logarithmic regularity and the item id:
  no existing theorem or logarithmic structure to duplicate.
- `rg` over `lean/Sheaf/AlgebraicGeometry` for associated-log, pullback-log and
  strictness interfaces: found and read `AssociatedLogUniversalStalks`,
  `StrictLogPullbackUniversal`, `FineSaturatedLogBlowup`,
  `FSStrictLogMorphism`, `LogIdealChartPresentation`, and the divisorial
  structure theorem. Their statements do not state this regular pullback lemma.
  Strictness is reused instead of defining a second pullback-log notion.
- Exact name/module search in Mathlib/AlgebraicGeometry, WeilConjectures, Sheaf
  and `dag/lean_names_upstream.json`: no collision for the new declaration.
- Transitive DAG check of the added strictness dependency: no path back to
  this item (106 nodes visited), hence it does not introduce a dependency cycle.

Validation: prescribed `scompile.py Q42 ... LogRegularPairRegularPullback.lean`
compiled both the sandbox and the library module cleanly (2.0 s and 2.5 s).
No node fault or STATEMENT-DISPUTED finding.

## Second reading by Q42

This is a second in-thread reading; the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review.
Reopened the node and finished Lean declaration and checked each clause above.
In particular, verified the direction of g and of the fibre map, every finite
extension including the identity, both local Noetherian assumptions, the exact
open complement `g ⁻¹ᵁ U`, and the two structural-map equations. The main risk
was silently returning a divisorial pair without specifying its inverse-image
log structure. The theorem instead returns an actual fs log morphism over g
with the existing graph-normalized strictness criterion, the structural
identifications at both ends, log regularity of MY itself and its exact
triviality locus. No additional premise is used to obtain these objects.
The source pair predicate supplies fs charts, the sheaf condition and its
triviality locus, so the source log realization introduces no stronger
hypothesis. Empty-source and empty-boundary cases survive every binder.
No statement mismatch was found and no mathematical correction was made.
