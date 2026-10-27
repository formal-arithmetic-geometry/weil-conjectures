## Worker report

The delivery states `AlgebraicGeometry.isKoszulRegularImmersionNear_fieldExtension_iff`
in `Sheaf.AlgebraicGeometry.FieldExtensionImmersionKoszulPoints`. Its only postponed
proof is the theorem's `sorry`. The companion definition has real existential data and
no postponed proofs. The accepted Q113 stage-1 split, its statement, and its proof plan
are preserved. The item gains its Lean record and the local-definition node in `stmt_deps`.
The returned packet is repaired by adding a definition-node owner for the existing
closed-chart predicate and citing it from that local definition. The current standing brief §0 explicitly supersedes the
inherited stage-1 refusal: this item is stage 2, has no usable Lean record, and is listed
in `coord/queue.tsv` at stage 2. This repair addresses the independent return on immutable head `446cb12061f9`.

Clause-by-clause correspondence:

- `K/k` is `{k K : Type u} [Field k] [Field K] [Algebra k K]`. The map is the actual
  `algebraMap k K`, with spectrum morphism `Spec.map (CommRingCat.ofHom ...)`.
- The two schemes over `k` are `Z P : Over (Spec (CommRingCat.of k))`. Their structure
  maps are `Z.hom` and `P.hom`; `i : Z ⟶ P` includes the required commutative triangle
  over the base. The immersion assumption is `[IsImmersion i.left]`, not a global
  closed-immersion assumption. `[LocallyOfFiniteType P.hom]` is precisely the stated
  local finite-type assumption. No quasi-compactness, separatedness, smoothness,
  Noetherian assumption, degree bound, or separability assumption is added.
- `P_K` and `Z_K` are the underlying schemes of `Over.pullback` applied to `P` and `Z`
  along the spectrum map of `algebraMap k K`. The definition of `Over.pullback.obj`
  is `Over.mk (pullback.snd ... ...)`, so these underlying schemes are exactly the
  stipulated fibre products, with their canonical structure maps to `Spec K`.
- `i_K` is `((Over.pullback ...).map i).left`. Reading the Mathlib definition shows
  this is `pullback.lift (pullback.fst ... ≫ i.left) (pullback.snd ...)`, so both
  projections are prescribed. It is not an arbitrary square or a supplied map.
- `a` is the actual `pullback.fst Z.hom (Spec.map ...)`. The binder `zK` ranges over
  the underlying points of the actual base-changed scheme `Z_K`.
- The conclusion is `IsKoszulRegularImmersionNear i_K zK ↔
  IsKoszulRegularImmersionNear i.left (a zK)`, in the same order as the node.
- In the new local definition, `∃ V : Z.Opens, z ∈ V` means some source neighbourhood;
  `∃ U : P.Opens` means an open subscheme of the actual target. The map
  `j : V.toScheme ⟶ U.toScheme`, `IsClosedImmersion j`, and the equation
  `j ≫ U.ι = V.ι ≫ i` express precisely the local closed-immersion factorization.
  `CotangentPresentation.IsKoszulImmersion j` is the existing predicate giving,
  at each source point of this chart, an affine target neighbourhood with generators
  of the actual kernel ideal, satisfying `RingTheory.Sequence.IsKoszulRegular`.
  It uses `r : ℕ` and `Fin r`, so zero-length sequences are included. The source
  neighbourhood remains essential: imposing the predicate on a global closed
  factorization would incorrectly require regularity everywhere.

Dependency interfaces read and used:

- `Mathlib.Algebra.Algebra.Defs`, `Algebra`: field extension via its specialization
  to two fields, as expressly allowed by `def-pc-field-extension`'s recorded note.
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`:
  the schemes and morphisms, not alternate encodings.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`: the
  all-affine-pairs finite-type class, as recorded on the finite-type node.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `IsImmersion`: the exact immersion
  clause of `def-weil-closed-immersion`'s `mathlib_match`; its factorization theorem
  `IsImmersion.isImmersion_iff_exists` explicitly gives closed followed by open.
  `IsClosedImmersion` is reused on the local charts.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, `pullback.snd`, and `Mathlib.CategoryTheory.Comma.Over.Pullback`,
  `Over.pullback`: chosen fibre products and their canonical induced morphism.
- `WeilConjectures.RingTheory.KoszulRegularSequence`,
  `RingTheory.Sequence.IsKoszulRegular`: actual higher Koszul homology vanishing,
  reused through the existing chart predicate.
- `Sheaf.AlgebraicGeometry.LciCotangentPresentation`,
  `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion`: its full definition
  at lines 417–420 has no Noetherian, codimension, positive-length, or derived-category
  binder. Its definition-node owner
  `def-sfb-koszul-closed-immersion-chart` is cited by the near-point definition. This existing helper does
  not itself introduce a source neighbourhood or a point argument, so it is not a
  duplicate of the new definition.

Proof imports follow the accepted proof plan wherever declarations are already
recorded: `WeilConjectures.RingTheory.KoszulRegularFlatBaseChange`,
`WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal`, and the Mathlib flatness,
universal-openness, affine-open, residue-field, faithfully-flat and localization
interfaces. The three proof-only nodes `lem-sfb-koszul-closed-immersion-affine-criterion`,
`lem-sfb-koszul-ideal-faithfully-flat-descent`, and
`lem-sfb-koszul-immersion-flat-ascent-etale-descent` currently have no Lean module to
import; they are not needed to type this statement, and no duplicate is introduced.
The theorem docstring carries all seven proof steps, including the restricted
faithfully flat cover construction rather than an unjustified surjectivity of `W → U`.

Edge cases checked mathematically before writing:

- `K = k` gives invariance under the canonical pullback identification.
- Infinite transcendental and purely inseparable extensions satisfy exactly the
  same binders; neither `FiniteDimensional` nor separability occurs.
- Empty `Z_K` has no `zK` and is vacuous, as in the original statement; empty open
  source neighbourhoods cannot falsely witness a condition at an actual point.
- Identity/open immersions allow the empty generating tuple (`r = 0`). The definition
  imposes no positive codimension or proper-ideal condition.
- Regularity may fail away from the chosen point; only the chosen open source
  neighbourhood is tested. Nonregular ideals such as `(x², xy)` are not rendered
  regular by the definition: `IsClosedImmersion` and the actual `j.ker.ideal W`
  prevent substitution of an unrelated ideal or chart.
- One arbitrary common size universe for fields and schemes follows Mathlib's
  scheme/pullback convention; any fixed collection of the mathematical objects
  lies in such a common universe. There is no quantification over test schemes in
  a smaller independent universe, and no added equality of universes for sites.

Searches (raw msearch responses are preserved in the new node's `mathlib_searches`):

- LeanFinder: “An immersion is Koszul regular near a point if and only if it is so
  at every point above it after a field extension”: eight smoothness-related hits,
  no pointwise equivalence.
- LeanSearch: “Koszul regular immersion locally near a source point”: ordinary
  scheme immersions and manifold predicates, no local Koszul predicate.
- LeanFinder: the explicit source-neighbourhood/closed-chart definition query:
  ordinary immersions and smoothness, no match.
- Loogle: `AlgebraicGeometry.IsImmersion, "Koszul"`: zero hits.
- msearch grep: `Koszul.*[Ii]mmersion|[Ii]mmersion.*Koszul` in Mathlib's
  `AlgebraicGeometry`: zero hits.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` found the existing
  `CotangentPresentation.IsKoszulImmersion`, which is reused. Searches for the
  pointwise field-extension statement and its node ID found no existing theorem.
- DAG definition statements were searched for Koszul regular immersions and
  near-point predicates; no definition node supplies this neighbourhood predicate.
  `tools/blueprint_refs.py search 'Koszul regular immersion'` returned zero blueprint
  nodes. `ancestor` reports `None`, matching the item's existing null ancestor;
  the new node follows the item's recorded provenance and prepends its ID to `via`.

Source checks used the current local Stacks `descent.tex` Tag 0694, `divisors.tex`
Tag 063J (definition) and 063G (affine criterion). Tag labels were checked against
`literature/stacks-project/tags/tags`. No statement correction or dispute is needed.

Validation: both delivered modules compiled cleanly with `scompile.py`, separately
in dependency order on the server against the published library; no warnings or
errors. The only `sorry` is the assigned statement's theorem proof.

## New nodes

`def-sfb-koszul-regular-immersion-near` defines exactly the source-neighbourhood
predicate that the item's statement describes in words. Its source is Stacks Tag
063J with the affine formulation of Tag 063G. The existing closed-chart predicate
`CotangentPresentation.IsKoszulImmersion` is used without copying it. The searches
above found neither a DAG definition nor an existing declaration supplying the
source point and source neighbourhood. It has its own module
`Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`, is cited by the item, and has
no theorems or postponed construction data. No dependency module is needed.


`def-sfb-koszul-closed-immersion-chart` owns the existing plain definition
`AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion` in
`Sheaf.AlgebraicGeometry.LciCotangentPresentation:417–420`, with `existing: true`.
It defines the finite-equation condition at every source point and allows length zero.
Its source is Stacks 063G and the ideal hypothesis of 08SJ. The new LeanSearch and
LeanFinder queries for finite Koszul-regular generators on closed-immersion charts
returned only ordinary closed-immersion facts; Mathlib grep returned no hit. Project
search found the plain definition above; a scan of all DAG definition records found
no owner of this declaration. The related lci-duality-data node owns additional
chart/determinant data and not this predicate. Raw tool responses are retained in
this new node's `mathlib_searches`. No module is added for an existing declaration.

## Repair of returned delivery

H12/H2 on immutable head `446cb12061f9`: the original near-point definition cited
`lem-trf-lci-cotangent-presentation`, a theorem node, for a plain helper definition.
Added `def-sfb-koszul-closed-immersion-chart` as an `existing: true` definition node
and replaced that theorem-node citation in both the near-point node's TeX and
`stmt_deps`. The chart node cites only definition nodes. The item's statement,
accepted split, proof plan and both Lean files are unchanged. This is ownership
metadata repair, not a correction of the item's mathematical statement.

## Second reading by Q45

Repair self-check, using the maintainer's independent reading recorded in the return:
that reading found the original theorem statement, pointwise order, canonical
base-change objects and maps, hypotheses and edge cases sound. I reopened the
existing declaration and its docstring: `IsKoszulImmersion` is a plain `def`, with
no closed-immersion typeclass binder and no data chosen from an existence theorem.
The added node therefore explicitly defines its predicate for every scheme morphism;
its interpretation as a closed-immersion chart supplies `IsClosedImmersion`
separately, exactly as `IsKoszulRegularImmersionNear` already does.
For every `x : U`, the existential affine open `W` contains `i x`; `r : ℕ` and
`a : Fin r → Γ(P, W.1)` provide the finite tuple; `IsKoszulRegular a` and
`Ideal.span (Set.range a) = i.ker.ideal W` give precisely the two required clauses.
For general morphisms `i.ker` is Mathlib's largest quasi-coherent ideal contained
in the component-wise kernel; for closed immersions it is the actual kernel
(`Hom.ker_apply`, since closed immersions are quasi-compact). This distinction is
explicit in the new TeX. Empty sources are vacuous; empty tuples are permitted;
no fixed rank, Noetherian or positive-codimension assumption is introduced.
The near-point predicate still requires an actual neighbourhood of the chosen
source point and the same closed factorization equation. The new signature was
compared verbatim with the current server source. No additional agent was started.
