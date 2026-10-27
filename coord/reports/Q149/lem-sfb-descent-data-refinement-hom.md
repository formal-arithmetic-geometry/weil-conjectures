## Worker report

The module `Sheaf.AlgebraicGeometry.DescentDataRefinementHom` states
`AlgebraicGeometry.fullyFaithful_descentData_refinement`, with its sole proof
postponed by `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement corrections. Only the item's `lean` field changes.

Source read: [Rydh, Submersions and effective descent of etale morphisms](https://davidrydh.se/papers/submersion20100305.pdf),
Proposition (5.6), printed p.19 (PDF page 19), and the preceding definitions of
universal descent. As the node already records, the precise Hom-only supporting
lemma and its explicit argument are supplied by the DAG, not stated separately
in that paper. The theorem's docstring carries all five DAG proof steps.

Hypotheses and clauses, matched individually:

- Quasi-separated schemes: the base category is exactly
  `ObjectProperty.FullSubcategory (fun X : Scheme.{u} ↦ QuasiSeparatedSpace X)`.
  Objects carry their quasi-separatedness proof; its morphisms are all scheme
  morphisms, wrapped in `InducedCategory.Hom`, with underlying map `.hom`.
  It imposes no separatedness or finiteness condition on a morphism.
- Size convention: the explicit levels `u v w` bind scheme size and independent
  morphism/object sizes of the fibre categories `Cat.{v, w}`. All test schemes
  and product schemes use the same `Scheme.{u}` bound as the original schemes.
  No implicit universe or equality of independent universes is imposed.
- The contravariant category-valued pseudofunctor is the binder `G` with domain
  `LocallyDiscrete` of the opposite of that full subcategory. Mathlib's
  `Pseudofunctor.mapId`, `mapComp` and its associator/unit laws provide exactly
  the stipulated coherent pullbacks. Its codomain is `Cat`, without a groupoid
  assumption on any fibre.
- For a morphism `p`, its descent category is the existing
  `G.DescentData (fun _ : Unit ↦ p)`. `Unit` indexes one morphism, not an empty
  family. The object component is one object of the fibre. Mathlib's compatible
  `hom` for test spans, `pullHom_hom`, `hom_self`, and `hom_comp` express the
  isomorphism, its naturality, the diagonal identity, and the cocycle. The
  isomorphism property follows from the existing `DescentData.iso` construction.
  Restriction to the actual fibre product gives precisely alpha in the node;
  conversely alpha pulled back along each test span gives Mathlib's structure.
  This is the standard test-span encoding of the same descent data, not a new
  notion or an additional hypothesis. The fibre products and triple products
  are quasi-separated by the cited permanence results.
- A compatible arrow is exactly `Pseudofunctor.DescentData.Hom`: its `hom ()`
  is the underlying arrow, and `comm` says that its two pullbacks commute with
  the two descent isomorphisms, with pseudofunctor comparisons inserted. Thus
  arbitrary, possibly noninvertible, arrows are included.
- The three schemes and two maps are the binders `{U Y S}`, `(a : U ⟶ Y)`,
  and `(b : Y ⟶ S)`. Lean's composite `a ≫ b` is the node's `ba`.
- Universal descent of `ba` is the hypothesis `h`: for every quasi-separated
  `V` and map `s : V ⟶ S`, and every cartesian base-change square with vertex
  `W`, maps `t : W ⟶ U` and `q : W ⟶ V`, the canonical comparison
  `G.toDescentData (fun _ : Unit ↦ q)` is fully faithful. `IsPullback` is on
  the underlying scheme maps `t.hom`, `q.hom`, `a.hom ≫ b.hom`, `s.hom`.
  Quantifying over cartesian representatives is equivalent to using the chosen
  fibre product: fibre products exist, remain quasi-separated, and any two are
  uniquely isomorphic over their factors. Pullback along that isomorphism is an
  equivalence and intertwines the canonical comparisons, so full faithfulness
  is invariant. This adds no mathematical assumption or map to the node.
- The conclusion refers to the existing `DescentData.pullFunctor G`, with
  singleton families `b` and `a ≫ b`, identity base map `p := 𝟙 S`, the unique
  index map `α`, and member map `p' := fun _ ↦ a`. Its commutativity witness is
  just the reversed right-unit equation. This is exactly restriction along a.
  It pulls the underlying objects/arrows back along `a` and pulls the descent
  isomorphisms back, inserting the built-in pseudofunctor comparisons.
- `Nonempty (...).FullyFaithful` is the proposition asserting full faithfulness
  of this specified functor; Mathlib's `FullyFaithful` itself is a data type.
  It asserts bijectivity of every Hom map, hence exactly the existence and
  uniqueness of the compatible lift in the final sentence of the node.
- There is no assumption of descent or surjectivity of `a`, no essential
  surjectivity or object-effectivity assumption on `a ≫ b`, and no topology.

Dependency declarations used and read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; full structure signatures and
  docstrings read in `Scheme.lean`.
- `def-weil-size-convention`: the recorded metatheoretic convention has no
  declaration or module; represented by the explicit universe parameters.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `QuasiSeparated` and
  `quasiSeparated_iff_quasiSeparatedSpace`. The latter identifies the object
  predicate with quasi-separatedness of the structural map. The class and
  the quasi-separated object/source and base-change results were read.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  its projections and lift. The invariant base-change hypothesis uses
  `CategoryTheory.IsPullback`, whose full definition and docstring were read
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`.
- The proof dependency `lem-weil-pbc-qcqs-morphism-permanence` is a Mathlib
  leaf, not an absent Lean attachment. Its relevant declarations are
  `QuasiSeparated.of_quasiSeparatedSpace`,
  `quasiSeparated_isStableUnderBaseChange`, and
  `quasiSeparatedSpace_of_quasiSeparated` in the public QuasiSeparated import.
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` is also imported
  privately for the recorded finite-presentation part of this proof leaf.
- The existing Mathlib constructions `ObjectProperty.FullSubcategory`,
  `Pseudofunctor.DescentData`, `DescentData.Hom`, `toDescentData`, and
  `DescentData.pullFunctor` are used directly; their full signatures,
  construction bodies, and docstrings were read. Nothing is privately copied.

Edge cases checked before writing:

- `a = id`: this reduces to the canonical restriction for an identical cover.
- `b = id`: this is full faithfulness of the canonical comparison for `a`,
  up to the existing identity-descent equivalence.
- Non-surjective `a`: take `U = S`, `Y = S ⊔ S`, with `a` the first inclusion
  and `b` the fold. Then `ba = id`; the original descent cocycle controls the
  unused component. The binders allow this case.
- Empty schemes are admitted as objects of the full subcategory. No
  nonemptiness or covering hypothesis on a map or a fibre was inserted. When
  `U` is empty the universal-descent assumption retains its actual strength;
  it is not discarded. `Unit` still encodes one map out of that empty scheme.
- Arbitrary noninvertible fibre arrows are included: the proof only inverts
  descent isomorphisms, as its five-step docstring explicitly explains.
- Test objects `V = Y` and `V = Y ×[S] Y` exist within the chosen universe and
  quasi-separated subcategory, so the hypothesis covers both uses in the proof.

Searches made (all msearch calls used group Q149 and this item):

- `msearch.py leanfinder`: "Restriction of descent data along a refinement is
  fully faithful if the composite is universally a morphism of descent for a
  category valued pseudofunctor". Eight hits: comparison functors,
  `IsPrestackFor.fullyFaithful`, and definitions of pullback. No exact theorem.
- `msearch.py loogle`: `"fullyFaithfulPullFunctor"`. One hit:
  `CategoryTheory.Pseudofunctor.DescentData.fullyFaithfulPullFunctor` in
  `Mathlib.CategoryTheory.Sites.Descent.Precoverage`. It requires a topology,
  an IsPrestack instance, and covering membership, absent here.
- `msearch.py grep`: `fullyFaithfulPullFunctor|pullFunctor|toDescentData`,
  subdirectory `CategoryTheory/Sites/Descent`. Twenty-three hits locate the
  existing definitions and related topology-dependent results, all reused or
  read instead of duplicated.
- `msearch.py leansearch`: "Fully faithful restriction of descent data when
  composite morphism universally descends arrows". Eight hits, including
  `fullyFaithfulToDescentData` and `FullyFaithful.ofCompFaithful`. None states
  the refinement result under the single-map universal-descent hypothesis.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, with
  `UniversalDescent|universalDescent|QuasiSeparatedScheme|quasiSeparatedScheme`
  and more narrowly `bijective_pullFunctor_map_of_isSheaf`, found no exact
  theorem. The upstream `Mathlib/CategoryTheory/Sites/Descent/Precoverage.lean`
  variant assumes a topology and sheaf hypotheses. Its header and declarations
  were read; those assumptions are not directly present here either.
- `rg` for `lem-sfb-descent-data-refinement-hom` in `lean/WeilConjectures`
  returned no match. `rg` for the proposed fully qualified declaration in the
  source trees and `dag/lean_names_upstream.json` returned no collision.
- DAG searches for the quasi-separated category and category-valued
  pseudofunctor definitions found no separate needed notion;
  `tools/blueprint_refs.py search 'descent data'` found four blueprint nodes,
  all about different fpqc module or scheme descent statements. Mathlib already
  supplies every categorical notion used here, so no new node is necessary.

Validation: `scompile.py` compiled both its sandbox check and the actual
`Sheaf.AlgebraicGeometry.DescentDataRefinementHom` library module cleanly
(2.5 s and 1.4 s respectively). There are no diagnostic commands, implicit
variables, or file-local notation/instances. Only the assigned theorem is sorry.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q149

A second pass in this worker session compared the node with the completed
module and the Mathlib source definitions; no other agent was started, as the
assignment explicitly forbids it. The maintainer's independent delivery review
remains independent of this pass.

The three object binders really are quasi-separated schemes, and `a` and `b`
range over all maps. The opposite locally discrete domain and `Cat` codomain
supply exactly the arbitrary coherent category fibres. The singleton index
provides one object over each cover scheme, and Mathlib's descent identities
and `Hom.comm` match every diagonal, cocycle, and arrow equation. The universal
hypothesis concerns the composite `a ≫ b`, not `a` or `b` separately, and uses
actual cartesian squares of schemes. Its extra names are bound choices of the
base change, not added assumptions: canonical and arbitrary pullbacks are
uniquely isomorphic and comparisons correspond under that isomorphism. The
conclusion uses the specified restriction functor with identity base map; its
full faithfulness is precisely the unique lifting of compatible arrows. The
non-surjective refinement and empty-scheme cases remain included. No
strengthening, weakening, or unmatched clause was found.

One elaboration issue was fixed before this pass: dot notation on the inline
function predicate unfolded `ObjectProperty` too far. Explicit
`ObjectProperty.FullSubcategory` fixed the name resolution without changing
any statement. The corrected module passed its server compile.
