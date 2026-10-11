## Worker report

The module defines `AlgebraicGeometry.fibre_product_neighbourhood_limit`, expressing the
canonical comparison from the pullback of the limiting objects to the limit of the stagewise
pullbacks as an isomorphism. Its hypotheses are a small index category `J`, three diagrams
`X`, `Y`, `S`, structure natural transformations `f` and `g`, and existence of the four limits.
The conclusion is `IsIso` of the canonical `pullback.lift`; the displayed equality proof is
exactly the pullback compatibility condition checked componentwise by `limit.hom_ext`.

Dependencies used are `Sheaf.AlgebraicGeometry.StrictHenselization` (the strict-henselization
construction) and `Sheaf.AlgebraicGeometry.FibreProductLimit` (the surrounding fibre-product
limit infrastructure); the categorical declarations are Mathlib's `pullback`, `limMap`, and
`limit.hom_ext`.

Edge cases checked include an empty index category (the explicit `[HasLimit]` hypotheses retain
the categorical statement), identity structure maps, and degenerate pullbacks. Searches with
`msearch.py` (LeanFinder, Loogle, and grep) found no declaration spelling the strict-henselization
specialization; the project generic comparison theorem was inspected in
`Sheaf.AlgebraicGeometry.FibreProductLimit`.

Resolved by the second reading: the source node names the pointed-etale-neighbourhood diagram and a
quasi-compact, quasi-separated morphism, while the available Lean dependencies expose only the
generic categorical comparison. The delivered statement records that comparison exactly in Lean;
a later bridge should specialize it to the strict-henselization neighbourhood diagram.

## Earlier second reading (a previous round; superseded)

The declaration compiles on the server and its signature matches the recorded `lean.statement`; no additional modules or dependency nodes were added.


## Second reading by R1

I independently read the node, its two proof steps, all three statement-dependency
records, and the dependency declarations. I read the source blueprint lemma and
strict-henselization definition on the server (the literature bodies are absent from
this local read-only clone). I also read Stacks limits.tex, label
lemma-directed-inverse-system-affine-schemes-has-limit (01YW), and categories.tex,
labels lemma-cofinal (04E7) and lemma-cofinal-in-filtered (0BUC). The source lemma
assumes only the qcqs morphism; the geometric point and neighbourhood category come
from its strict-henselization definition. The DAG's direct universal-property proof
is the proof followed in the repaired docstring.

Object/hypothesis/conclusion checklist, with the final Lean and verdict:

- Schemes X and S and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Exact. There is no affine, Noetherian, finite-type, or separated assumption.
- Quasi-compact and quasi-separated f: `[QuasiCompact f] [QuasiSeparated f]`.
  Exact. I read the Mathlib class signatures: quasi-compact preimages of compact
  opens, and quasi-compact diagonal, respectively, as the conventions node says.
  They are hypotheses even though the DAG's categorical proof does not need them.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)`.
  Exact; this is the geometric-point convention, not a point with an unspecified
  residue extension. The recorded strict-henselization API uses this same universe.
- Strict henselization: `Scheme.strictHenselizationScheme s`. Exact: its definition
  is `Spec (strictHenselizationRing s)`, and that ring is the colimit of
  `strictHenselizationDiagram s` over the opposite of the chosen small affine model.
  I read the ring, scheme, coordinate diagram, representative inclusion, and cone
  definitions, not just their names.
- All pointed étale neighbourhoods: `(Scheme.pointSmallEtale s).fiber.Elements`.
  Exact: `pointSmallEtale.fiber` is `Etale.forget S` followed by the covariant Hom
  functor from `Over.mk s`. Its elements are an étale V/S and a lift of s; its
  morphisms preserve that lift. This is the recorded dependency's Mathlib match.
  `CategoryOfElements.π ... ⋙ Scheme.Etale.forget S` retains the maps to S.
- Canonical structure map and projections: the existential `p` and natural
  transformation `q` supply them over S. The `∀ j : SmallModel ...` equation forces
  every affine-representative leg to equal the existing `strictHenselizationCone`
  leg followed by `isoSpec.inv`. This last isomorphism is needed because that cone
  has objects Spec of global sections, whereas q lands in the neighbourhood itself.
  Exact: there is no arbitrary choice of an isomorphism of underlying schemes.
  The representative functor is initial by `strictHenselization_properties`, so
  these equations uniquely determine the full cone; the leg at (S,s) determines p.
  The existential packaging introduces the canonical maps, not additional premises.
- Fibre products and transition maps: `(Over.pullback f ⋙ Over.forget X).mapCone
  { pt := Over.mk p, π := q }`. Exact. I read `Over.pullback`'s implementation:
  its objects are `pullback V.hom f`, its vertex is `pullback p f`, and its maps
  are the canonical fibre-product maps induced by the over-S morphisms q.
  This is V ×_S X rather than X ×_S V; the canonical symmetry preserves both
  projections and identifies the two entire cones, so this factor ordering does
  not alter the statement or its canonical comparison.
- Canonical comparison isomorphism / existence of the inverse limit:
  `Nonempty (IsLimit (...))`. Exact: a specified cone is limiting iff its vertex
  represents that inverse limit with those projections. This includes existence
  and identifies the canonical comparison, with no `[HasLimit]` assumptions.
  `Nonempty` merely makes the IsLimit structure a proposition. The affine-leg
  equation is the specification of the word canonical in the node, not an added
  claim such as an arbitrary equality of maps.

Edge cases: the full index category cannot be empty because (S,s) is an object;
I added no independent index category or Nonempty premise. Empty X is allowed,
and all fibre products and the limiting vertex are then empty. Empty S admits
no geometric point, as in the source, so there is no missing case. Identity f
recovers the strict-henselization neighbourhood limit. There is no characteristic
restriction, positive-dimensional assumption, n parameter, or finiteness premise.
`u` is bound explicitly; schemes, Ω, rings, and the small representative index use
one ambient universe as in the recorded API. The full category may be large: the
statement is an IsLimit assertion for its explicit cone and does not require a
large-limit instance. All object-universe sizes are covered by universe-polymorphism.

Independent searches (2026-10-12):

- LeanFinder via msearch.py: “strict henselization inverse limit of pointed etale
  neighborhoods commutes with base change”; eight unrelated standard-étale/ring
  results, no match.
- Loogle via msearch.py: `CategoryTheory.Over.pullback`; twelve hits, including the
  functor, its adjunction, and object/map formulas. I opened its implementation and
  used the existing functor, without defining a second base-change construction.
- msearch.py grep: `strictHenselizationScheme|fibre_product_neighbourhood_limit|
  isLimitBaseChangeCone`; zero indexed hits. Direct rg of Mathlib, WeilConjectures,
  and lean/Sheaf found the landed strict-henselization API and the generic
  `Scheme.isIso_limit_pullback_comparison` in FibreProductLimit. The latter is
  exactly the first worker's generic statement and is not this specialized node.
  Upstream `isLimitBaseChangeCone` takes an arbitrary cofiltered limit cone and a
  map to a stage; it does not construct the canonical strict-henselization cone
  over all pointed neighbourhoods, and so is not an exact existing match.
- `tools/lean_names_upstream.py show lemma-weil-pbc-fibre-product-limit` and direct
  rg of dag/lean_names_upstream.json and the source trees found no declaration of
  this name. No duplicate statement or new definition node is delivered.

Mismatches repaired: the previous Lean had three arbitrary diagrams, arbitrary
index universes, four limit-existence hypotheses, no qcqs assumptions, no geometric
point, no strict henselization, and a comparison in the opposite direction. Its
mathematical content already occurred in FibreProductLimit. I replaced that
signature with the specialized canonical-limit assertion above, removed the generic
import, added the genuine dependency import and Mathlib over-category pullback,
and expanded the docstring to carry both DAG proof steps and uniqueness. The
node's natural-language statement is correct and unchanged, so no statement_change
is appropriate. Its lean.statement is the exact multiline signature in the file.
The worker's dispute is resolved by this repair. No dependency module, private
copy, hollow definition, local notation, local instance, or theorem proof was added;
the only theorem proof remains sorry.

The dependency initially lacked its server object file; a later compile found it,
so no duplicate was introduced. Final single-file compile: clean, 1.9 seconds,
no errors or warnings. The initial generic push d73f7bf12 was an erroneous interim
delivery; the repaired delivery supersedes it. A concurrent maintainer review repaired that interim push
using a small affine representative cone (reviewer R-fpl). I independently read
that repair after the final dry run: it retains s and qcqs f, fixes the vertex and
legs by equality/HEq, and asserts the base-changed cone is limiting. The present
version states the full neighbourhood cone directly and fixes its restriction to
the same representatives, as the node explicitly indexes all neighbourhoods.
Only the specialized module, lean record, and this report are intended for landing.
