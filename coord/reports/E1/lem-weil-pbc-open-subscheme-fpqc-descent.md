## Worker report

The module states `AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc`, formalizing
Tag 03N0. A family is represented by `I : Type u`, schemes `T : I → Scheme.{u}`,
and morphisms `g : ∀ i, T i ⟶ S`; `hg` is membership of
`Presieve.ofArrows T g` in `Scheme.fpqcPrecoverage S`. Each open subscheme `W_i` and
the descended open are represented by `Scheme.Opens`. Compatibility is equality of
the inverse images along `pullback.fst` and `pullback.snd` on every fibre product.
The conclusion is `∃! V : S.Opens, ∀ i, g i ⁻¹ᵁ V = W i`.

The dependencies `def-pc-scheme`, `def-pc-fibre-product`, and
`def-weil-pbc-fpqc-covering` are used through Mathlib's `Scheme`, pullbacks, and
`Scheme.fpqcPrecoverage`; no project declaration was needed. The empty index case
is admitted by the quantified family and `∃!`; identity covers and empty schemes
are represented by the same types without extra assumptions. Searches used the
node's recorded LeanFinder/Loogle/grep searches and `rg` over `lean/Sheaf` and
`WeilConjectures`; no exact existing theorem was found.

## Earlier second reading (a previous round; superseded)

The statement was checked against the node clause by clause: fpqc covering is `hg`,
open subschemes are `Scheme.Opens`, pairwise pullback equality is `hW`, and existence
and uniqueness are exactly `∃!`. No mismatch found.

## Second reading by E1

Read the item's full node and all three statement dependency nodes, the delivered
module, and Stacks descent.tex, lemma-open-fpqc-covering (Tag 03N0), including
its proof and surrounding context. The repository's literature/stacks-project
checkout is absent here; the local Stacks source is available at
/home/ubuntu/c1-stacks-review/descent.tex (lines 4100–4135), and the covering
definition at /home/ubuntu/c1-stacks-review/topologies.tex (lines 2887–2902).
The source statement agrees with the node and assumes no additional global
Noetherian, separatedness, finiteness, or base-field hypotheses.

Clause-by-clause inventory and verdicts:

- Base scheme S: `{S : Scheme.{u}}`. Exact. Read `Scheme` and `Scheme.Hom`
  in Mathlib.AlgebraicGeometry.Scheme: a locally ringed space locally affine,
  with morphisms of locally ringed spaces, as def-pc-scheme requires.
- Index set I and component schemes T_i: `{I : Type v}` and
  `{T : I → Scheme.{u}}`. Exact for arbitrary set-indexed families; changed
  the first worker's `Type u` to an independent `Type v` to remove the
  unnecessary tie between family size and scheme size.
- Morphisms g_i to S: `(g : ∀ i, T i ⟶ S)`. Exact, with no extra structure.
- Fpqc covering: `hg : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S`.
  Exact. Read `fpqcPrecoverage := propQCPrecoverage @Flat`,
  `propQCPrecoverage := qcPrecoverage ⊓ Scheme.precoverage P`, and the
  QuasiCompactCover and IsCompactOpenCovered definitions. This requires flat
  arrows and joint surjectivity, and finite compact-open image covers of every
  affine open of S. Compact opens have finite affine-open covers, so this is
  equivalent to def-weil-pbc-fpqc-covering's finite affine-open condition.
  Joint surjectivity already follows from that condition. It does not require
  each g_i to be quasi-compact. Thus the dependency's recorded notion is usable.
- Open subschemes W_i: `(W : ∀ i, (T i).Opens)`. Exact. `Scheme.Opens`
  is TopologicalSpace.Opens; `Scheme.Opens.toScheme` and `ι` equip each open
  with the restricted scheme structure. The source itself states open subsets.
- Pairwise compatibility on T_i ×_S T_j: `hW : ∀ (i j : I),
  pullback.fst (g i) (g j) ⁻¹ᵁ W i =
  pullback.snd (g i) (g j) ⁻¹ᵁ W j`. Exact. Read `pullback`, `fst`, `snd`
  in Limits.Shapes.Pullback.HasPullback and the HasPullbacks Scheme instance
  in AlgebraicGeometry.Pullbacks; these are def-pc-fibre-product's chosen
  universal fibre product and its projections. The notation ⁻¹ᵁ is Opens.map
  on the underlying continuous map. Restrict.lean's
  `pullbackRestrictIsoRestrict` identifies this inverse-image open subscheme
  with the scheme-theoretic base change. No private fibre product is used.
- Descended open W of S: `∃! V : S.Opens`. Exact existence and uniqueness
  as an open subset, hence as an open subscheme of S, rather than uniqueness
  of arbitrary schemes up to literal equality.
- Every required inverse image: `∀ i, g i ⁻¹ᵁ V = W i`. Exact; all i are
  inside the one existence-and-uniqueness quantifier, with no clause omitted.

Edge cases: neither I nor S is required to be nonempty. An empty fpqc family
forces the base to be empty by joint surjectivity, and its lattice of opens
has one element, so ∃! remains correct. Empty members and empty W_i are
allowed. Identity covers descend exactly the supplied open. No cardinality,
characteristic, ring-domain, or field assumptions appear; Spec of the zero
ring is an allowed empty scheme. There is no natural-number parameter, and
n = 0 in the covering definition is allowed. All schemes live in an arbitrary
universe u; the family now lives in an independently arbitrary universe v.
No limits indexed by I are taken, so the special index-universe restriction
for filtered limits does not apply. All universes and binders are explicit.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: "descent of open subsets under flat jointly surjective quasi
  compact families". Returned Flat.isQuotientMap_of_surjective and descent
  of morphism properties, including the open-immersion descent instance.
  Opened FlatDescent.lean: the latter descends a property of an already given
  morphism along one surjective flat quasi-compact morphism; it does not
  construct the descended open from compatible opens of a general family.
- Loogle: "IsQuotientMap, IsOpen" returned unknown identifier IsQuotientMap;
  this query provided no evidence for absence.
- LeanSearch: "open subsets with equal inverse images on fiber products
  descend along fpqc coverings" failed with Internal Server Error; recorded
  unavailable, no mathematical verdict inferred from it.
- msearch grep: "openSubscheme|isOpen.*iff.*preimage|
  descendsAlong_isOpenImmersion|isQuotientMap_of_surjective" in
  AlgebraicGeometry found the quotient-map ingredient and morphism-property
  descent, no exact compatible-family open-descent theorem.
- Independently ran rg for open/descen, compatible/open, and fpqc/existsUnique
  across Mathlib/AlgebraicGeometry, WeilConjectures, and lean/Sheaf; checked
  dag/lean_names_upstream.json for the item's name and declaration. No exact
  existing declaration was found. Read the project's
  existsUnique_open_of_etale_fpqc_baseChange: it requires an etale Y over S
  and descends opens of its base changes, a specialized citer of this item.
  Read isOpenImmersion_of_fpqcPrecoverage_pullback: it descends a morphism
  property, not compatible open data. Neither replaces this statement.

Mismatches repaired: the proof docstring previously only named three broad
ingredients and omitted the node's complete argument (H8). It now gives all
five steps, explicitly naming fibre-product points, local affine reduction,
finite standard refinement, quotient-topology openness, and uniqueness with
all the corresponding proof-dependency IDs. Added the conventional copyright
header (H9). Removed the unnecessary index-universe restriction (H3). No
mathematical node correction, new definition node, or dependency module was
needed; there is no hollow definition and the sole theorem retains `sorry`.
The node's lean.statement was updated verbatim from the revised signature.

Validation: scompile.py compiled the complete delivered module cleanly on
the server (1.6 seconds, exit 0), with no errors or warnings. Checked by eye
that all variables and universes are bound. Delivery dry run follows.
