## Worker report

Item: lem-trf-disjoint-sheaf-partition-pullbacks. The module
`Sheaf.AlgebraicGeometry.DisjointSheafPartitionPullbacks` states
`AlgebraicGeometry.Scheme.FppfPartition.disjoint_sheaf_partition_pullbacks`.
Its proof is `sorry`. The three helpers `openObject`, `openInclusion`, and
`openRestriction` construct the canonical open subscheme objects and maps in
`Over S`; all have actual data. These helpers only bundle the existing Mathlib
open subscheme and restriction constructions in the slice, rather than introducing
another definition of schemes, sheaves, open subschemes, or partitions.

Source read: literature/stacks-project/spaces.tex, Tags 0F15 and 02WO,
`lemma-coproduct-sheaves-open-and-closed` and
`lemma-representable-sheaf-coproduct-sheaves`, including the omitted pullback
verification. The node gives the detailed arbitrary-family generalization with
a supplied partition. Its six-step argument is included in the theorem docstring.
No statement correction, new node, or dependency repair is needed.

Hypotheses and conclusions, matched to the node:

- A scheme S and the big fppf site are `{S : Scheme.{u}}` and
  `Scheme.fppfTopology.over S` on `Over S`. Its objects and arrows are precisely
  schemes over S and S-morphisms. The size convention is implemented by explicit
  universes u and u+1, with sheaf values in `Type (u + 1)`; `uliftYoneda.{u + 1}`
  lifts the representable presheaves into this same category of sets. This lift
  is the canonical equivalence of sets, not a new representability hypothesis.
- The small index set is `{I : Type w}` with w explicit and independent. H and
  G_i are bundled set sheaves `H` and `G`, and the maps are `c : ∀ i, G i ⟶ H`.
- Sectionwise injectivity is `_hinj`, quantified over every index and object V.
  Pairwise disjointness is `_hdisj`: distinct indices and equal images of two
  sections force `IsEmpty V.left`, exactly emptiness of the test scheme.
- The object T is `T : Over S`. The pieces are `U : I → T.left.Opens` with their
  canonical scheme structures. Openness is supplied by the type; `_hclosed`
  supplies closedness, `_hpairwise` supplies disjointness, and `_hcover` says
  their supremum is all of T. The sections are the dependent family `a_i` on
  `openObject T (U i)`.
- `∃ a : H.obj.obj (op T)` supplies the glued section. The first conjunct gives
  every equation c_i(a_i)=a restricted to U_i, using `openInclusion`. The second
  conjunct says every other section satisfying those same equations equals a;
  together these are precisely unique existence.
- The third conjunct quantifies every other clopen partition V, all its sections
  t, and the same image equations. It concludes `V i = U i ∧ HEq (t i) (a_i i)`
  for every i. Since all pieces use the canonical open subscheme structure,
  equality of opens is equality of open subschemes. Once that equality is
  substituted, HEq is ordinary equality in the same sheaf section set; it is
  exactly equality after identification, with no choice of identification.
- The fourth conjunct is `IsPullback` in the category of presheaves on Over S.
  Its upper map is the representable map of the specified inclusion; its left
  map is `uliftYonedaEquiv.symm (a_i i)`; its right map is
  `uliftYonedaEquiv.symm a`; and its bottom map is `(c i).hom`. Thus on a test
  object Z the comparison sends d to (d followed by inclusion, d^*a_i), with
  compatibility equation c_i(s)=b^*a. The limit property says exactly that this
  map is a bijection onto the displayed fibre set. Being a presheaf pullback
  states its naturality in Z as well as the claimed presheaf isomorphism.
  This uses the node's specified canonical maps, not arbitrary maps or an
  uncharacterized isomorphism.
- The final conjunct quantifies every `Z : Over S` and `b : Z ⟶ T`. It states
  that `b.left ⁻¹ᵁ U i` are closed, pairwise disjoint, and cover Z. Their
  openness follows from the type. The sections are explicitly
  `(G i).obj.map (openRestriction b (U i)).op (a_i i)`, and the next clause
  gives their image equations for `H.obj.map b.op a`. The final clause says any
  other clopen partition and sections with those equations are equal to these
  inverse-image pieces and sections after identification. This renders every
  base-change and uniqueness assertion, with the same labels i.

Dependency declarations used and read at their sources:

- def-pc-scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme; local-affine locally ringed spaces and their
  morphisms. Imported through the public geometry dependencies.
- def-pc-fppf-site: `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`,
  Mathlib.AlgebraicGeometry.Sites.Fpqc; flat locally finitely presented jointly
  surjective covering families. `GrothendieckTopology.over` from
  Mathlib.CategoryTheory.Sites.Over gives its recorded slice topology.
- def-weil-size-convention: its lean record is explicitly metatheoretic, with no
  declaration. The theorem binds every universe and uses the common u+1 bound.
- def-weil-pbc-sites-and-cohomology: public import
  Sheaf.CategoryTheory.SiteCoveringAxioms, with recorded declaration
  `CategoryTheory.Precoverage.IsSiteForCoverings`. As its record specifies for
  the sheaf component, the statement uses Mathlib `Sheaf` and its underlying
  functor and natural transformations; no cohomology or site axiom is restated.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`; the canonical opens and inclusions are
  `Scheme.Opens.toScheme` and `Scheme.Opens.ι` from
  Mathlib.AlgebraicGeometry.Restrict, publicly imported.
- The stated proof dependencies are included: plain import
  Mathlib.AlgebraicGeometry.Morphisms.Etale supplies
  `AlgebraicGeometry.Etale` and its open immersion instance for
  lem-weil-pbc-open-immersion-etale and def-weil-etale-morphism. The public
  Restrict/OpenImmersion imports also supply the exact Mathlib match for
  lem-weil-pbc-morphism-factors-through-open-subscheme:
  `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`, and `Scheme.Hom.resLE`.
  Read their complete signatures and universal-property docstring. The helper
  `openRestriction` uses the canonical `morphismRestrict` already present in
  that same interface and the theorem `morphismRestrict_ι`.

Edge cases checked before writing: I empty forces T empty by `_hcover`; no
nonemptiness or finite-index assumption is used. Empty pieces are valid opens
and are retained, with their unique sections guaranteed by the empty fppf cover.
T empty is allowed, including arbitrary index families of empty pieces. For a
singleton index the partition is all of T and the statement reduces to
injectivity plus the specified section. The pairwise disjointness hypothesis is
conditional only on unequal labels, so no false diagonal emptiness is imposed.
Every b is allowed, including identities, empty sources, and non-surjective
maps. Inverse-image opens and their canonical scheme restrictions implement
base change without any additional flatness or etaleness assumption on b.

Searches performed:

- msearch.py leanfinder: "A disjoint family of injective sheaf maps and a clopen
  partition with sections gives unique gluing and represents each summand
  pullback". Eight hits: topological sheaf unique gluing and disjoint products,
  pairwise gluing, and Scheme.GlueData.sheafValGluedMk_val. None states the
  summand pullbacks or partition uniqueness for these fppf sheaf morphisms.
- msearch.py loogle: `"Sheaf", "IsPullback"`. Three hits: the sheafified Yoneda
  Mayer-Vietoris square criterion and two classifier truth pullback theorems.
  None states the theorem of this node.
- msearch.py grep in AlgebraicGeometry:
  `(partition|[Cc]lopen).*(pullback|[Ss]heaf)|([Ss]heaf|pullback).*(partition|[Cc]lopen)`.
  Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf:
  `disjoint.*[Ss]heaf|[Ss]heaf.*[Pp]artition|clopen.*[Ss]heaf`.
  Hits concern etale or pro-etale sheaf products, other partition notions, and
  unrelated supports; none is the general big fppf assertion here.
- grep for the exact item id in lean/WeilConjectures returned no match.
- rg for `FppfPartition|disjoint_sheaf_partition_pullbacks` in Mathlib,
  lean/WeilConjectures and lean/Sheaf returned no declaration collision.
- Read Mathlib `uliftYonedaEquiv` (including its component formula),
  `IsPullback` (including its commutative square and limit cone), and the
  canonical scheme open restrictions to select these existing interfaces.

Validation: scompile.py compiled the sandbox and the named library module cleanly
(8.1 s and 5.7 s). The earlier helper error was fixed by explicitly unfolding the
slice structure map in its equation and marking canonical restriction
noncomputable. The only postponed theorem is the item itself; the helpers add
no axioms or postponed statements.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
