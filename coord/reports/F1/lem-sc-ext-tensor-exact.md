## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact` states
`AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_tensorLeft_exact`, with only a sorry proof.
No definition, new node, dependency replacement, or statement correction is needed.

Hypotheses and clauses:
- A scheme X: `{X : Scheme.{u}}`, with the universe explicitly declared.
- An O_X-module P: `(P : X.Modules)`. Mathlib's `Scheme.Modules` is the category
  `SheafOfModules.{u} X.ringCatSheaf` in the module universe of the scheme.
- A cover by open sets on which P is finite free, with nonnegative integer ranks allowed to
  vary: `[P.IsFiniteLocallyFree]`. This is the existing predicate in the dependency's recorded
  LocallyFree module, whose definition is locally free local-generators data with each
  generating index finite. On the Zariski site, coversTop is precisely an open cover, and
  the generating morphisms being isomorphisms says that the restrictions are free.
  Choosing a finite-index cardinality gives each d_a in ℕ. Conversely a trivializing cover
  gives this local-generators data. This uses the varying-rank class in the same module as
  the recorded `IsFiniteLocallyFreeOfRank`, not that constant-rank class as a global hypothesis.
- The functor G ↦ P tensor G: `CategoryTheory.MonoidalCategory.tensorLeft P`.
  Its maps are identity on P tensor the given module map.
- Preservation of short exact sequences, equivalently exactness:
  `PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P)`.
  In these abelian categories an exact additive functor preserves finite limits and colimits;
  tensoring is additive because its sectionwise maps are bilinear and then sheafified.
  Conversely preservation of finite limits and colimits preserves kernels and cokernels and
  hence short exact sequences. This includes injectivity and surjectivity, not just middle
  exactness. No hypothesis on G, or on quasi-coherence of the sequence, is added.

Dependency declarations read and used:
- `def-amb-finite-locally-free-module`: recorded module
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, recorded declaration
  `SheafOfModules.IsFiniteLocallyFreeOfRank`; its sibling `SheafOfModules.IsFiniteLocallyFree`
  supplies exactly the varying-rank hypothesis the item explicitly calls for. Both complete
  definitions and docstrings were read; the general varying-rank notion already exists.
- `def-pur-sheaf-tensor-product`: imported
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`. Its recorded tensor declarations
  `SheafOfModules.monoidalCategory` and `SheafOfModules.tensorObjIsoSheafification` come from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`, whose signatures and docstrings
  were read. The scheme monoidal instance in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` is literally
  `SheafOfModules.monoidalCategory X.sheaf`; no alternative tensor is introduced.
  The recorded main declaration `positiveTensorPower` is irrelevant to this node's binary tensor.
- `def-weil-sheaf-of-modules-category` is a Mathlib leaf: its match is `SheafOfModules`, from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`; its full structure and category were read.
  Its abelian instance in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` was read too.

Source: the local blueprint and Stacks text files named by the node are absent on this machine.
The blueprint intent is available verbatim in the node's source/place, blueprint.from and proof.
Read the primary sources online: [Stacks 01C6](https://stacks.math.columbia.edu/tag/01C6)
permits varying finite local ranks, and [Stacks 05NE](https://stacks.math.columbia.edu/tag/05NE)
proves tensor exactness from flat stalks. The declaration docstring carries all three node
proof steps, including naturality, the zero rank case, and both directions of stalkwise exactness.

Edge cases checked: empty scheme (no nonempty binder); rank zero and zero tensor functor;
rank one (locally the identity); disconnected schemes with different ranks on components;
unbounded local ranks on infinitely many components; arbitrary short exact module sequences
that need not split or be quasi-coherent. No field, Noetherian, finiteness of cover, or positivity
of rank hypothesis appears. The theorem covers schemes in every universe u, with their full
standard module category X.Modules.

Searches (2026-10-11):
- msearch leansearch, `finite locally free sheaf tensor product exact functor`: service unavailable
  (Internal Server Error); no conclusion taken from that unavailable service.
- msearch leanfinder, `Tensoring a sheaf of modules by a finite locally free module preserves
  short exact sequences`: eight results, principally Module.Flat.lTensor_shortComplex_exact
  and rTensor_shortComplex_exact for ModuleCat over a single ring. None states this theorem
  for scheme module sheaves.
- msearch loogle, `tensorLeft, ShortComplex.ShortExact`: unknown identifier tensorLeft, no hits.
- msearch grep, `tensorLeft|PreservesFiniteLimits|ShortExact` in
  `Algebra/Category/ModuleCat/Sheaf`: five evaluation/forgetful finite-limit hits, none matching.
- rg in source WeilConjectures/AlgebraicGeometry and local lean/Sheaf/AlgebraicGeometry for
  `IsFiniteLocallyFree|tensorLeft|tensor.*exact|exact.*tensor`: locally free definitions,
  dual/tensor local freeness, Ext comparison and flat pullback results, no identical theorem.
- rg for `lem-sc-ext-tensor-exact` in source WeilConjectures: no hits.
- rg in source sheaf modules for `tensorLeft|PreservesFiniteLimits|ShortExact`: no hits.
- rg for the proposed full declaration's short name in dag/lean_names_upstream.json,
  Mathlib, source WeilConjectures and local lean/Sheaf: no hits.

Validation: server scompile completed in 1.9 seconds, exit code zero, no errors or warnings.
No statement dispute was found. The dependency record's constant-rank comparison is honored;
the item itself correctly uses the already available varying-rank notion.


## Second reading by F1

Independent second reader, 2026-10-11. I opened the item node, its sandbox module,
all three statement dependency nodes, and the declarations described below. Verdict:
the Lean says exactly what the node says. No mathematical mismatch, missing notion,
new definition node, dependency replacement, or statement correction was found.
The module and node record are unchanged; this section is the only delivery change.

Source reading: the blueprint markdown and local Stacks checkout are absent here.
I independently read the primary Stacks pages [01C6](https://stacks.math.columbia.edu/tag/01C6),
[05NE](https://stacks.math.columbia.edu/tag/05NE),
[01CB](https://stacks.math.columbia.edu/tag/01CB), and
[01AG](https://stacks.math.columbia.edu/tag/01AG), then downloaded the primary
`stacks/stacks-project/master/modules.tex` into the item's scratchpad and read
`section-locally-free`, `definition-locally-free`, `definition-flat`,
`lemma-flat-stalks-flat`, `lemma-stalk-tensor-product`, and `lemma-abelian`.
The surrounding source assumes only a ringed space, allows zero rings, and
separates varying finite ranks from constant rank. The stalkwise flatness proof
applies to arbitrary module sheaves. Schemes supply commutative structure rings,
so exchanging right and left tensor through symmetry imposes no extra hypothesis.

Objects, hypotheses, and conclusion, listed independently from the node:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Any scheme X | `{X : Scheme.{u}}`, with `universe u` | Exact; no base field or extra geometric property. |
| A sheaf P of O_X-modules | `(P : X.Modules)` | Exact; all module sheaves, not only quasi-coherent ones. |
| An open cover with P free of finite rank d_a on each member | `[P.IsFiniteLocallyFree]` | Exact; local ranks vary, include zero, and the cover need not be finite. |
| Tensor product as in the tensor dependency | `tensorLeft P` | Exact; its objects are `P ⊗ G`, maps are `P ◁ g`. |
| Functor on the whole O_X-module category | `tensorLeft P : X.Modules ⥤ X.Modules` | Exact; no restrictions on G or on the maps. |
| Preservation of every short exact sequence, equivalently exactness | `PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P)` | Equivalent, with neither endpoints nor middle exactness omitted. |

Dependency verification: Mathlib `AlgebraicGeometry.Scheme.Modules` is literally
`SheafOfModules.{u} X.ringCatSheaf`; its morphisms are linear presheaf maps,
and its existing Abelian, HasLimits and HasColimits instances are used.
I read `SheafOfModules`, `Hom`, and the scheme Modules category signatures.
The recorded constant-rank dependency is `SheafOfModules.IsFiniteLocallyFreeOfRank`.
I read it and its varying-rank sibling `IsFiniteLocallyFree` in the recorded
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` module.
The node explicitly compares, rather than assumes, constant rank, so that sibling
is the correct predicate here. Its field supplies `LocalGeneratorsData` whose
`coversTop` is an open cover, whose generator maps are isomorphisms, and whose
individual generator index types are finite. I also read those Mathlib structures:
`IsFiniteType` means each family is finite, not that the cover is finite.
Finite index cardinalities give precisely the d_a of the node.

For the tensor dependency I opened the landed `TensorProduct.lean` and upstream
`SheafOfModules.monoidalCategory` and `tensorObjIsoSheafification`. The scheme's
monoidal instance in `Modules.Invertible` is exactly `monoidalCategory X.sheaf`;
therefore its tensor is the sheafification of the sectionwise tensor, as required.
Mathlib's `curriedTensor` and `tensorLeft` signatures confirm the order and maps.
No new dependency modules are part of this delivery.

Conclusion equivalence: tensor maps are additive, since the underlying tensor is
bilinear and sheafification is additive. For an additive functor between abelian
categories, preserving short exact sequences preserves kernels and cokernels:
factor a map through its image and apply preservation to the resulting two short
exact sequences. Additivity already preserves finite biproducts and the zero object;
kernels and cokernels then give all finite limits and colimits. Conversely those
preservation properties give preservation of short exact sequences (Mathlib's
`ShortComplex.ShortExact.map_of_exact`, used in `Abelian.ShortExact`). Thus the
conjunction is not stronger than the node. No faithfulness is assumed or needed.

Edge cases: the empty scheme and empty trivializing cover are allowed; rank zero
and the zero module yield the zero tensor functor, which is exact. Rank one gives
locally the identity functor. Disconnected schemes permit different ranks and
infinitely many components with no global rank bound. No positivity, nonempty
index type, characteristic, domain, Noetherian, finite-cover, or splitting
hypothesis appears. All universes are bound: scheme and section modules are in u,
and local cover indexing can be shrunk to the opens universe, as the existing
`LocalGeneratorsData.shrink` does. Finite limits are invariant under equivalences
of finite diagram categories, so no finite shape is lost by their universe choice.

Independent searches, using queries different from the first reader's:

- `msearch leanfinder`: "A finite rank locally trivial module sheaf is flat and tensor
  preserves kernels and cokernels" returned eight results: finite presentation,
  finite type, quasicoherence predicates and locally constant module rank.
  None states sheaf tensor exactness.
- `msearch leansearch`: "locally free sheaf tensor preserves finite limits finite
  colimits" reported unavailable (Internal Server Error). No negative verdict
  was inferred from this unavailable service.
- `msearch loogle` with two quoted name fragments reported a parse error;
  it provides no search evidence. The successful LeanFinder search supplies
  the second search kind.
- Independent `rg` searches for flatness, tensorLeft/tensorRight, exactness,
  finite-limit preservation, and finite local freeness in Mathlib's sheaf
  modules, upstream module/sheaf directories, and project `lean/Sheaf` found
  flatness definitions, extension-by-zero flatness, free-sheaf flatness,
  internal-Hom exactness, affine section flatness, Ext comparison, and dual/tensor
  local freeness. I opened upstream `Modules.Ext` and the project's sheaf
  `Flat` definition: neither states finite-locally-free tensor exactness.
  Mathlib's tensor finite-limit results concern modules over one ring.
  Searching the proposed declaration name across Mathlib, upstream, project,
  and `dag/lean_names_upstream.json` found no existing declaration.

H5/H6/H8/H9 checks: there is no new definition or private notion, and precisely
one theorem with only `sorry` as proof. Module and declaration docstrings name
the source and blueprint id; the three numbered proof steps retain local
trivialization, the natural stalk-tensor comparison including d=0, and both
directions of stalkwise exactness. Imports supply the recorded tensor, scheme
monoidal instance, varying-rank predicate, and finite preservation notions.
All lines meet the 100-character limit. I checked the node's `lean.statement`
verbatim against the theorem signature; every variable and universe is bound.
Server validation: `scompile.py F1 lem-sc-ext-tensor-exact` with the absolute
sandbox module path compiled in 1.9 seconds, exit zero, without warnings.
