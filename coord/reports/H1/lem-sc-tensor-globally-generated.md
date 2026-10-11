## Worker report

The item module is `lean/Sheaf/AlgebraicGeometry/TensorGloballyGenerated.lean`, declaring
`AlgebraicGeometry.Scheme.Modules.isInvertible_and_globallyGenerated_positiveTensorFamily`.
It states the corrected node with a `sorry` proof; nothing is proved.
The added definition module is `lean/Sheaf/AlgebraicGeometry/PositiveTensorFamily.lean`.
Both modules compiled together cleanly on the server (2.5 seconds, exit 0).

Hypothesis and clause correspondence:

- Scheme X: `(X : Scheme.{v})`, the Mathlib scheme definition.
- Quasi-compactness, restored from the source: `[CompactSpace X]`; this imposes no
  separation condition.
- A positive integer number of factors: `(n : ℕ)` and `L : Fin (n + 1) → X.Modules`.
  Lean's n is the paper's number of factors minus one, covering exactly all positive integers.
- Invertibility of every factor: `hL : ∀ i, (L i).IsInvertible`, using the scheme-specific
  notion, not `SheafOfModules.IsInvertible`.
- Global generation of every factor: `hG : ∀ i, Nonempty
  (SheafOfModules.GeneratingSections (L i))`; no finiteness is imposed on the inputs.
- The left-associated product: `positiveTensorFamily n L`, whose one-factor case is
  exactly `L 0`; subsequent factors are appended on the right with the recorded tensor.
- Invertibility of the result: the first conjunction, `(positiveTensorFamily n L).IsInvertible`.
- Global generation of the result: the second conjunction, `Nonempty
  (SheafOfModules.GeneratingSections (positiveTensorFamily n L))`.
- Existence of finite generating families of the factors: the third conjunction, `∃ σ,
  ∀ i, (σ i).IsFiniteType`. This is Mathlib's finite-index property, not finite presentation.
- For every choice of these families: `∀ σ, (∀ i, (σ i).IsFiniteType) → ...`.
- The tuple index set is `(i : Fin (n + 1)) → (σ i).I`; the selected factor sections are
  `(σ i).s (j i)`. `positiveTensorFamilySection n L` forms their left-associated pure tensor.
- Generation by precisely these sections is `Epi` of the map
  `(positiveTensorFamily n L).freeHomEquiv.symm` applied to the displayed family. This is
  exactly the epi field of `GeneratingSections`; surjectivity is local surjectivity as
  sheaves, without requiring surjectivity on sections of every individual open.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Hom`; scheme is a
  locally ringed space with local affine neighbourhoods, Hom a locally-ringed-space morphism.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, every point has an open neighbourhood
  where the module is isomorphic to the structure sheaf.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.GeneratingSections`, with fields I, s and epi;
  `.GeneratingSections.IsFiniteType`, with `Finite σ.I`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  the recorded tensor implementation `SheafOfModules.monoidalCategory` and
  `tensorObjIsoSheafification` (via the imported upstream monoidal API).
  `positiveTensorPower` is for repeated copies of one module, and cannot represent a
  family of distinct factors; no private copy of tensor product is introduced.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, corresponding to
  `def-weil-pbc-quasi-compact-scheme`.
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`:
  `tmulSection`, the pure tensor mapped into the sheafification; `tmulSection_map`, its
  compatibility with restriction. These are reused for the added family definition.

Edge cases: one factor (Lean n=0) has no unit tensor inserted and recovers its section.
The empty scheme is allowed; its zero modules are invertible and the empty generating
index sets are permitted. A finite family can be empty: the dependent product index then
is empty; on a nonempty scheme an invertible factor cannot have an empty generating
family, but this is a consequence rather than a new hypothesis. Singleton generating
families give one pure tensor. There is no field, characteristic, noetherian, separated,
affine or connectedness hypothesis. The universe is explicit and arbitrary; the index
universe is the one of the recorded `GeneratingSections` structure, covering the node's
finite families without restricting their cardinalities.

Searches (all msearch queries are logged in searches.jsonl):

- LeanFinder, `tensor product of globally generated invertible sheaves is globally generated`:
  eight generic ring Picard/module tensor and cartesian sheaf tensor hits, no exact statement.
- Loogle, `SheafOfModules.GeneratingSections, tensorObj`: no hits (unknown tensorObj).
- Mathlib grep, `GeneratingSections.*tensor|tensor.*GeneratingSections|globally generated`,
  AlgebraicGeometry: no hits.
- LeanSearch, `iterated tensor product of a finite family of sheaves of modules and their sections`:
  service unavailable, Internal Server Error; this is recorded, not treated as a negative search.
- LeanFinder, the same family query: eight presheaf/cartesian/condensed tensor results,
  no ordered nonempty module-family tensor with pure tensor section construction.
- Mathlib grep, `tensorFamily|iteratedTensor|tensorList|tensorSections`: no hits.
- Project Lean grep for tensor/global-generator combinations found only binary free-generator
  results in TensorSection.lean and tensor powers, no global generation theorem or positive
  tensor family definition. Direct grep for this item id in WeilConjectures returned no hits.
- `tools/lean_names_upstream.py show lem-sc-tensor-globally-generated`: no declaration for it.
- `rg` of lean/Sheaf found its citer's proof docstring, not a matching declaration, and the
  existing tensor-power definition. Searches for the chosen new declaration names in
  Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no conflicts.
- DAG grep and `tools/blueprint_refs.py search 'iterated tensor'`: no definition node,
  zero blueprint matches. The existing tensor-generating-sections node is a theorem about
  generation, not a definition of the iterated product or sections.

Node fault: missing quasi-compactness for the asserted existence of finite families,
corrected explicitly below. No unresolved STATEMENT-DISPUTED claim.

## New nodes

`def-sc-positive-tensor-family` defines the left-associated positive ordered tensor product
and the corresponding pure tensor global section, including tuple-indexed families.
Source: Stacks Tag 09NC, the displayed L and tau_J. The existing tensor dependency defines
binary tensor product and powers of a single module, not products of different factors;
Mathlib and project searches above found no existing family definition. Binary section
tensor is reused from `tmulSection`. Global sections in `GeneratingSections` are compatible
families on all opens (equivalent to evaluation on the top open for a scheme), so
`tensorGlobalSections` builds this compatible family with `PresheafOfModules.sectionsMk`.
The required compatibility proof is the named theorem `tensorGlobalSections_naturality`
with a natural-language proof and `sorry`, recorded among the node's declarations.
No definition has unknown data: both family recursions and the section-family values are
written in full. The only postponed piece in this definition module is a proof field.

## Statement corrected

The original node assumes an arbitrary scheme but asserts finite global generating
families exist. A counterexample is the disjoint union of P^d over a fixed field for all
d ≥ 1, with O(1) on each component. This line bundle is globally generated (sections
supported on one component give the coordinate generators). Any r global sections fail
to generate on P^d for d ≥ r: r linear forms have a nonempty common projective zero locus.
Thus no finite family generates it.

The corrected statement restores quasi-compactness from Stacks Tag 09NC, whose statement
and finite-family selection explicitly assume it. Tag 01AO itself permits arbitrary
families; retaining the node's finite-family assertion requires the 09NC hypothesis.
The source pages were read at https://stacks.math.columbia.edu/tag/09NC and
https://stacks.math.columbia.edu/tag/01AO because the literature checkout lacks the tex files.
This is an auxiliary node, not the blueprint unit's own statement.
The corrected statement also names the iterated construction and makes explicit that
finite families exist and that every such choice yields a generating tensor family.
The proof's finite-family choice now includes the quasi-compact subcover argument; its
uses and proof_deps gain the existing quasi-compact-scheme node.

Every citer (found by DAG grep, filtering stmt_deps and proof_deps):

- `lem-sc-enough-globally-generated-ample`: holds true. It assumes X quasi-compact already,
  so its tensor-product step still applies. The sibling `lem-sc-tensor-generating-sections`
  has the item in blueprint provenance only; it is not a stmt_deps/proof_deps citer.

## Second reading by H1

I independently read the corrected node, its source place (Stacks Tags 09NC and 01AO),
the dependency declarations, and both delivery modules. The statement's objects and clauses
render as follows, and each matches the corrected node:

- The scheme and quasi-compact hypothesis are `(X : Scheme.{v}) [CompactSpace X]`.
- The positive integer number of factors is represented by `n : ℕ` and
  `L : Fin (n + 1) → X.Modules`, so `n = 0` is the one-factor case.
- Invertibility and global generation are respectively `hL : ∀ i, (L i).IsInvertible`
  and `hG : ∀ i, Nonempty (SheafOfModules.GeneratingSections (L i))`.
- The left-associated product and its pure tensor sections are exactly
  `positiveTensorFamily n L` and `positiveTensorFamilySection n L`.
- The conclusion's four clauses are the conjunction of result invertibility, result global
  generation, existence of finite-type generating families for every factor, and the
  universal Epi assertion for every such choice. The displayed Epi map uses precisely the
  tuple index `(i : Fin (n + 1)) → (σ i).I` and sections `(σ i).s (j i)`.

The empty scheme, zero modules, empty generator index, singleton families, and `n = 0`
are admitted by the types; no field, characteristic, Noetherian, separated, affine, or
connectedness assumption is introduced. Universes are explicit and unrestricted. The
corrected node's added quasi-compact hypothesis is the only change required by the source's
finite-subcover argument. I found no remaining mismatch or unbound variable.

I repeated the existing-definition searches (LeanFinder/Loogle/LeanSearch queries and grep
of Mathlib, `WeilConjectures`, `lean/Sheaf`, and the DAG); they found no matching family
tensor or global-generation declaration. The new `def-sc-positive-tensor-family` node is
therefore necessary, and its four declarations are fully written (only the named
compatibility theorem has `sorry`). Both modules compile together with `scompile.py`.

Old statement, verbatim:

Let $X$ be a scheme [def-pc-scheme], let $n\ge 1$ be an integer, and let $\mathcal L_1,\ldots,\mathcal L_n$ be globally generated invertible $\mathcal O_X$-modules [def-sc-invertible-module] [def-weil-pbc-generating-sections]. Then the tensor product [def-pur-sheaf-tensor-product] $\mathcal L_1\otimes_{\mathcal O_X}\cdots\otimes_{\mathcal O_X}\mathcal L_n$ is a globally generated invertible $\mathcal O_X$-module, generated by the tensor products of finite global generating families of the factors.

Corrected statement:

Let $X$ be a quasi-compact scheme [def-pc-scheme] [def-weil-pbc-quasi-compact-scheme], let $n\ge 1$ be an integer, and let $\mathcal L_1,\ldots,\mathcal L_n$ be globally generated invertible $\mathcal O_X$-modules [def-sc-invertible-module] [def-weil-pbc-generating-sections]. Use the left-associated product and induced pure tensor sections [def-sc-positive-tensor-family]. Then the tensor product [def-pur-sheaf-tensor-product] $\mathcal L_1\otimes_{\mathcal O_X}\cdots\otimes_{\mathcal O_X}\mathcal L_n$ is a globally generated invertible $\mathcal O_X$-module, Each factor admits a finite global generating family, and for every choice of such finite generating families, their pure tensor sections generate the tensor product.
