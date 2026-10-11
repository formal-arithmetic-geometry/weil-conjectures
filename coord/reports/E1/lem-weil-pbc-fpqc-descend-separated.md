## Worker report

The module `Sheaf.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange` states
`AlgebraicGeometry.isSeparated_of_flat_surjective_baseChange`. Its only proof is `sorry`.
No definition, new node, dependency module or statement correction is required.

Hypothesis and clause correspondence:
- Schemes X, S and S': `{X S S' : Scheme.{u}}`, with the universe explicitly declared.
- The morphism g:S'→S: `(g : S' ⟶ S)`.
- Flatness of g: `[Flat g]`; `Flat.iff_flat_stalkMap` identifies this with flatness on all
  stalks, as def-weil-flat-morphism requires.
- Surjectivity of g: `[Surjective g]`, surjectivity of the underlying map of points.
- Quasi-compactness of g: `[QuasiCompact g]`; `quasiCompact_iff_forall_isAffineOpen`
  gives precisely the affine-open preimage formulation in def-weil-finite-type-morphism.
  No locally-of-finite-type assumption is imposed.
- The morphism f:X→S: `(f : X ⟶ S)`.
- The fibre product X×_S S': `pullback f g`, which exists for schemes.
- Its second projection f' to S': `pullback.snd f g`, not its first projection to X.
- Separatedness of f': `[IsSeparated (pullback.snd f g)]`; Mathlib's IsSeparated
  means that its diagonal is a closed immersion, including exactly the parenthetical
  clause in the node.
- Conclusion: `IsSeparated f`, the same closed-immersion condition on the original diagonal.

Dependency declarations read and used:
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (morphisms of locally ringed spaces).
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat`, together with its stalk characterization.
- def-weil-surjective-morphism: Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap,
  `AlgebraicGeometry.Surjective`.
- def-weil-finite-type-morphism: the recorded `AlgebraicGeometry.QuasiCompact` in
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact; the node also defines finite type,
  but only its quasi-compact notion occurs in this item.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback` and `CategoryTheory.Limits.pullback.snd`.
- def-weil-proper-morphism: its recorded `AlgebraicGeometry.IsSeparated` in
  Mathlib.AlgebraicGeometry.Morphisms.Separated; neither properness nor universal
  closedness is an assumption of this statement.
All are Mathlib notions; the three direct imports supply the declarations used,
including scheme pullbacks and surjectivity through their imports.

Source checked: https://stacks.math.columbia.edu/tag/02KU, Lemma 35.23.6.
The repository has no local `literature/stacks-project/descent.tex`, so the official
Stacks page was read. The node is the descent direction for the singleton fpqc cover;
its five-step proof is transcribed in the declaration docstring with the dependency ids.

Edge cases checked before writing:
- Empty X is permitted; its diagonal is a closed immersion.
- Empty S is permitted, and any schemes admitting morphisms to it are empty.
- Empty S' over nonempty S cannot satisfy Surjective g, as required by the node.
- Identity and isomorphism covers are permitted, and the assertion becomes the usual
  invariance of separatedness under the canonical pullback isomorphism.
- Neither S nor S' is assumed affine, and f need not be finite type or quasi-compact.
- No reducedness, integrality, characteristic or nonemptiness assumption occurs.
- One arbitrary universe u is used for schemes, with no quantification over test
  schemes in an independently smaller universe.
No statement dispute or node fault was found.

Searches performed through `/home/ubuntu/weil-launcher/msearch.py` (recorded in searches.jsonl):
- leanfinder: "If the base change of a scheme morphism along a flat surjective
  quasi-compact morphism is separated, the original morphism is separated".
  Eight hits concern stability under base change, separated composition, affine maps,
  or flatness; none state the descent direction.
- loogle: "AlgebraicGeometry.IsSeparated, AlgebraicGeometry.Flat": zero hits.
- grep in Mathlib AlgebraicGeometry:
  "DescendsAlong @IsSeparated|IsSeparated.*descend|isSeparated_of.*flat|02KU": zero hits.
- leansearch: "Separatedness of scheme morphisms descends along flat surjective
  quasi-compact base change": service unavailable (Internal Server Error).
- rg in WeilConjectures and lean/Sheaf for the item id and descent theorem patterns:
  only a proof-docstring citation in IsProperOfFieldBaseChange.lean, no declaration.
- Read WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean:
  it supplies no separatedness descent declaration.
- Full proposed name `isSeparated_of_flat_surjective_baseChange` searched in
  dag/lean_names_upstream.json, Mathlib, WeilConjectures and lean/Sheaf: no hit.

Validation: the server compile and delivery dry run are run with the provided tools.
The second reader supplies the independent reading and performs delivery.

## Second reading by E1

I independently read the node, its six statement dependency nodes, their recorded
Mathlib declarations, and the delivered module. The statement checklist is:

| Node object, hypothesis, or conclusion | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary schemes X, S, S' | `{X S S' : Scheme.{u}}` | Exact; `Scheme` is a locally ringed space locally affine, and `Scheme.Hom` is a locally ringed space morphism. |
| Scheme morphism g:S'→S | `(g : S' ⟶ S)` | Exact. |
| g is flat | `[Flat g]` | Exact by `Flat.iff_flat_stalkMap`; no finite-presentation condition. |
| g is surjective on points | `[Surjective g]` | Exact: the class field is `Function.Surjective g`. |
| g is quasi-compact | `[QuasiCompact g]` | Exact by `quasiCompact_iff_forall_isAffineOpen`; no finite-type condition. |
| Scheme morphism f:X→S | `(f : X ⟶ S)` | Exact; f and g are universally quantified, so their independent binder order has no effect. |
| Fibre product X×_S S' | `pullback f g` | Exact chosen categorical fibre product; Mathlib supplies `HasPullbacks Scheme`, with no extra hypothesis. |
| f' is the second projection to S' | `pullback.snd f g` | Exact: its codomain is S', whereas `pullback.fst f g` has codomain X. |
| f' is separated, including its diagonal being a closed immersion | `[IsSeparated (pullback.snd f g)]` | Exact: `IsSeparated.isClosedImmersion_diagonal` is the defining field. |
| f is separated | `IsSeparated f` | Exact same defining condition on the original diagonal; no extra conclusion. |

Dependency signatures were opened in Mathlib `Scheme.lean`, `Morphisms/Flat.lean`,
`Morphisms/UnderlyingMap.lean`, `Morphisms/QuasiCompact.lean`,
`CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`, and
`Morphisms/Separated.lean`; the scheme-pullback instance was checked in `Pullbacks.lean`.
The finite-type dependency records QuasiCompact among its declarations, and the proper
morphism dependency records IsSeparated. Their relevant clauses are precisely the notions
used here. Neither the finite-type nor the properness clauses are imposed on f or g.

The local literature checkout contains no Stacks .tex files. I read the official Stacks
pages https://stacks.math.columbia.edu/tag/02KU and
https://stacks.math.columbia.edu/tag/03L7 and the actual upstream .tex source at
https://raw.githubusercontent.com/stacks/stacks-project/master/descent.tex
(lines 5308–5330 and 5580–5606) and `topologies.tex` (lines 2904–2930).
02KU states fpqc locality, not merely an affine theorem: its final paragraph reduces to
an affine cover to prove it. The node takes the singleton-cover descent implication.
03L7(2) applies to any target scheme: choose the quasi-compact open g⁻¹(U), whose image
is U by surjectivity. The quasi-separatedness restriction belongs only to condition (4),
which is not used. There is no standing field, finiteness, or Noetherian hypothesis.

Edge cases: empty X is allowed; empty S forces X and S' empty through their morphisms;
empty S' over nonempty S is excluded exactly by surjectivity. Identity covers are allowed.
The statement has no indexing set or integer parameter, so empty-index and n=0 issues
introduce no restriction (the finite affine subcover in the proof may be empty over the
empty open). Zero rings and every characteristic are permitted through arbitrary schemes.
Nonaffine and non-quasi-separated bases and non-finite-type f remain permitted. The
explicit arbitrary universe u covers schemes of any size in a common universe; there is
no smaller-universe test-object quantification. Every variable and universe is bound.

Independent searches (recorded by msearch.py in searches.jsonl):
- LeanFinder: "Faithfully flat descent of the closed immersion diagonal of a scheme
  morphism" returned the diagonal characterization of separatedness and related results,
  not the required descent assertion.
- Loogle: `AlgebraicGeometry.IsSeparated, AlgebraicGeometry.Surjective` returned zero hits.
- Mathlib grep: `(separated.*(fpqc|faithfully|descent)|descend.*separated|IsSeparated.*DescendsAlong)`
  in AlgebraicGeometry returned zero hits.
- LeanSearch: "A scheme morphism is separated if its pullback by an fpqc morphism is
  separated" was also attempted; see searches.jsonl for the service result.
- rg with independent separated/fpqc/faithfully/descent patterns in WeilConjectures and
  lean/Sheaf found sections about module sections and descent to a stage of an inverse
  limit, and a citation of this node in IsProperOfFieldBaseChange, not this assertion.
  The proposed full name does not occur in either tree or dag/lean_names_upstream.json.
  I also inspected the instance lists in both Mathlib and WeilConjectures FlatDescent
  modules: neither supplies separatedness descent. No duplicate notion was introduced.

The module has no definitions, hollow data, additional declarations, or proved lemmas.
Its sole proof is `sorry`. Both docstrings name the source and blueprint id. The theorem
proof docstring carries all five node steps, including the target isomorphism, cartesian
pasting, fpqc-cover recognition, descent of universal closedness, and the final immersion
with closed image. Imports provide the three independently used morphism properties.
The node's lean.statement agrees verbatim with the source signature before `:=`.
No new nodes, dependency modules, or statement corrections occur. No mismatch was found;
the Lean and node were left unchanged. Only this independent review was appended.

Validation: compilation and the delivery dry run are performed with the mandated
scompile.py and deliver2.py tools; delivery follows only after a clean compile and OK.
