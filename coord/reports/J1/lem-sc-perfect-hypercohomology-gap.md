## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectHypercohomologyGap` states
`AlgebraicGeometry.perfect_hypercohomology_gap`, with proof `sorry` only. The node's
statement is unchanged. The extra definition supplies the missing meaning of tensor
cohomology vanishing when the second argument is an arbitrary derived object.

Hypothesis and clause correspondence:

- “X a scheme”: `(X : Scheme.{uG})`, Mathlib's `AlgebraicGeometry.Scheme`.
- “P a perfect object of D(O_X)”: `(P L : schemeDerivedCategory X)` and
  `(hP : X.IsPerfect P)`. The global and per-open `HasDerivedCategory.{wG}` binders
  are precisely the carriers required by the recorded perfect-complex definition;
  they specify the derived localization, not a restriction on schemes.
- “Tor amplitude in [u,v]”: bounds `(a b : ℤ)` and `hTor`, quantifying over EVERY
  `G : SheafOfModules.{uG} (moduleRings X.toRingedSpace)` and every `i : ℤ`.
  `i < a ∨ b < i` means outside the closed interval, and
  `schemeDerivedTensorCohomologyVanishes X P G i` is the recorded predicate for
  `H^i(P ⊗ᴸ G)=0`. In particular, no quasi-coherence restriction on G is imposed.
- “L a complex with quasi-coherent cohomology”: the same derived-object binder L
  and `(hL : schemeDerivedQCohProperty X L)`, meaning every cohomology sheaf is
  quasi-coherent. This quantifies over all unbounded derived objects.
- “For every integer j”: `(j : ℤ)`.
- “H^q(L)=0 for all q in [j-v,j-u]”: `hgap` quantifies over all `q : ℤ`, with
  `j - b ≤ q` and `q ≤ j - a`, and requires `IsZero` of
  `(DerivedCategory.homologyFunctor (SheafOfModules …) q).obj L`.
- “H^j(P ⊗ᴸ L)=0”: `schemeDerivedTensorComplexCohomologyVanishes X P L j`.
  Its definition requires actual representatives K,N, K K-flat, isomorphisms
  `Q.obj K ≅ P` and `Q.obj N ≅ L`, and `IsZero` of degree j homology of their
  total tensor. Both existential witnesses are required, so this is not vacuous.
  Tag 06YS supplies K-flat replacement, Q is essentially surjective, and Tag
  06YU identifies the tensor computed using these representatives with the
  derived tensor. No chosen monoidal structure on D(O_X) is assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (full structure signatures/docstrings read).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty` (full definitions and carrier comments read).
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`, built from
  `Scheme.IsStrictlyPerfect`, with the shared per-open module category.
- `Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`:
  `schemeDerivedTensorCohomologyVanishes`, the existing module-second-factor
  predicate; used for Tor amplitude, not copied.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`; its full signature
  and definition, and the tensor zero-preservation declarations, were read.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  the total complex of the tensor bicomplex; signature/docstring read at 45–59.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`, via KFlat:
  `SheafOfModules.monoidalCategory`; used with `X.sheaf`, as in the landed
  module-second-factor predicate. No second tensor product is invented.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, the shared cohomology-sheaf functor.

The theorem's docstring carries all three proof steps from the node: local
strictly perfect/K-flat model, bounded Q-degree filtration and the E1/E2 diagonal
vanishing calculation, finite-filtration conclusion and locality. These are
instructions for stage 3, not proofs performed during stage 2.

Edge cases checked: X empty, P zero, L zero; all have the expected vanishing.
The endpoints are included. For a=b, the hypothesis is a single cohomology degree
j-a. No assumption a≤b was added: when a>b, Tor amplitude as defined forces P
acyclic (test the unit module), so the conclusion still holds even if the gap
hypothesis is empty. Negative j and negative bounds are admitted as integers.
There is no quasi-compactness or separatedness assumption: the extracted tensor
cohomology assertion is local; those hypotheses in the surrounding 09M4 lemma
are for global Hom vanishing, not the spectral-sequence step extracted here.
Independent universe parameters cover all scheme sizes and derived hom universes.

Sources read: the node, its three statement dependencies and their declaration
sources; Stacks https://stacks.math.columbia.edu/tag/09M4, the displayed spectral
sequence in its proof and following vanishing sentence; also Tags 06YS and 06YU
for the added representative-based definition. The local literature payload was
absent, so the exact tags were read online. No statement correction or dispute.

Searches actually run via msearch.py (logged in searches.jsonl):

- LeanSearch `perfect complex derived tensor cohomology vanishing Tor amplitude gap`:
  unavailable, HTTP Internal Server Error; not counted as no match.
- LeanFinder, same query: eight generic Tor/projective and derived t-structure
  results, including `DerivedCategory.isZero_of_isLE`/`isZero_of_isGE`; none is
  the perfect tensor gap statement.
- Loogle `DerivedCategory.homologyFunctor, IsZero`: zero hits, unknown identifier
  IsZero; this does not establish absence by itself.
- Mathlib grep `derivedTensor|DerivedTensor|TorAmplitude`: zero hits.
- LeanSearch `vanishing cohomology derived tensor of two complexes of sheaves of modules K flat representatives`:
  unavailable, Internal Server Error.
- LeanFinder, the preceding query: eight results (Sheaf.H, cohomologyPresheaf,
  cohomologyPresheafFunctor, Module.Flat tensor exactness, Rep Tor vanishing);
  no predicate for two O_X-derived objects.
- Mathlib grep `derivedTensor.*[Vv]anish|[Vv]anish.*derivedTensor|mapBifunctor`:
  25 reported generic mapBifunctor hits; the total tensor declaration was read.
- rg of WeilConjectures and lean/Sheaf for derived tensors and vanishing predicates:
  found coefficient-site derived tensors, ring/module models, and the existing
  scheme predicate ONLY for a module second factor. No perfect tensor-gap lemma.
- rg by the item id in WeilConjectures and dag/lean_names_upstream.json: no hits.
- rg of dag/nodes for tensor cohomology vanishing: the existing module-second-factor
  definition and related lemmas, no definition for two derived objects.
- `tools/blueprint_refs.py search "tensor cohomology"`: zero blueprint nodes.
  `ancestor lem-sc-perfect-hypercohomology-gap`: lem-sc-finite-duality.

## New nodes

`def-pc-derived-tensor-complex-cohomology-vanishes` defines vanishing of degree-i
cohomology of E tensor-derived L for two arbitrary objects in D(O_X). It is the
representative-based extension required by this node's conclusion, using the
recorded K-flat, tensor totalization, and derived-category definitions. Source:
Stacks Tags 06YS/06YU and the tensor spectral sequence in 09M4. Searches above
found no existing defining node/declaration for two derived second factors.
The existing `def-pc-derived-tensor-cohomology-vanishes` only accepts a sheaf
module as second argument and remains the predicate used in hTor. The new
predicate is a full Prop definition with no sorry, no data choice, and no
independence-of-representatives theorem asserted. Its source, search records,
blueprint ancestor/via, and all definition dependencies are recorded in its JSON.

## Second reading by J1

I reread the node statement, its Stacks source place (Tag 09M4, the spectral-sequence
argument after “Say K^\\vee has tor amplitude in [a,b]”), and both delivered Lean files.
The object and hypothesis correspondence is:

- The scheme is `X : Scheme.{uG}`; the two derived-category instances are the global
  `HasDerivedCategory` and the per-open `∀ U : X.Opens` instance. These are exactly the
  carrier infrastructure required by the dependency declarations and add no geometric
  hypothesis.
- The perfect object is `P : schemeDerivedCategory X` with `hP : X.IsPerfect P`.
- The Tor-amplitude bounds are `(a b : ℤ)` and `hTor`; its quantifiers range over every
  `G : SheafOfModules (moduleRings X.toRingedSpace)` and every integer `i`, with the
  disjunction `i < a ∨ b < i`, exactly expressing vanishing outside `[a,b]` via the
  existing `schemeDerivedTensorCohomologyVanishes` predicate.
- `L : schemeDerivedCategory X` and `hL : schemeDerivedQCohProperty X` give an arbitrary
  derived object with quasi-coherent cohomology.
- The universal integer is `(j : ℤ)`. `hgap` quantifies every `q : ℤ` satisfying
  `j - b ≤ q` and `q ≤ j - a`, and requires `IsZero` of the degree-`q` homology sheaf.
- The conclusion is exactly
  `schemeDerivedTensorComplexCohomologyVanishes X P L j`, the delivered representative-
  based definition of vanishing of degree-`j` cohomology of the derived tensor of the two
  objects. I added this definition node to `stmt_deps`, since the conclusion uses it.

The Lean has no extra Noetherian, separated, quasi-compact, characteristic, or
finite-type assumptions, and no hypothesis was dropped. Empty schemes, zero `P` or `L`,
negative degrees and bounds, endpoint degrees, and `a = b` are admitted. If `a > b`,
the Tor-amplitude hypothesis itself forces the relevant object to be acyclic; no artificial
ordering assumption was introduced. Universes are shared between `X` and its sheaf
categories, while `wG` independently supplies the derived localization universe.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, upstream names, and DAG nodes using
LeanSearch, LeanFinder, Loogle, `rg`, and `msearch.py`. No existing declaration states the
perfect two-derived-object tensor-gap predicate. The existing
`schemeDerivedTensorCohomologyVanishes` only has a module second argument, so the new
`schemeDerivedTensorComplexCohomologyVanishes` definition is required and is not a duplicate.
The definition module compiles together with the theorem module via `scompile.py`; the
only proof placeholder is the theorem's required `sorry`.
