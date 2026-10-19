## Worker report

The module `Sheaf.AlgebraicTopology.MappingSimplexTermwiseEquivalence` states
`SSet.Enhanced.mapping_simplex_termwise_equivalence`, with its proof entirely `sorry`.
It states HTT Remark the project server and the coherent-realization consequence, using the
already constructed mapping simplex and its induced map. The source PDF was opened
and Remark the project server on printed page 180 was read: its proof is induction using left
properness of the Joyal model structure. The docstring supplies that induction,
the cylinder pushout decomposition, and the left-Quillen consequence.

Clause-by-clause correspondence:

- Small simplicial sets: `A B : SimplexChain.{u} n`, with `u` arbitrary.
  The existing abbreviation is `(Fin (n + 1))ᵒᵖ ⥤ SSet.{u}`. Thus both chains
  have exactly the required reversed transition maps, including composites.
- Maps commuting with transitions: `f : A ⟶ B` is a natural transformation.
  Its components `f.app (op i)` are simplicial maps; its naturality is exactly
  the commuting-ladder condition, without imposing extra conditions on them.
- The displayed mapping simplex: `mappingSimplex A` and `mappingSimplex B`.
  `MappingSimplexDegree A r` is the dependent sum over monotone maps from
  `Fin (r.unop.len + 1)` to `Fin (n + 1)` of the degree-r simplices in the
  last fibre. `mappingSimplexOperator` precomposes the base map and restricts
  the fibre coordinate, then applies the indicated transition. These existing
  definitions were read in full in CartesianMappingSimplexPresentation.lean.
- The specified induced map: `mappingSimplexChainMap f`. Its actual `app r`
  sends `z` to `⟨z.1, (f.app (op (z.1 (Fin.last r.unop.len)))).app r z.2⟩`.
  The definition and its named naturality theorem were read in full in
  MappingSimplexConeFibers.lean. No arbitrary simplicial map replaces this map.
- Every component a categorical equivalence: `hf` quantifies over every
  `i : Fin (n + 1)` and every quasicategory `C : SSet.{max u v}` and asserts
  `IsEquivalence` for the homotopy-category functor induced by restriction
  along the lifted component. This is exactly the testing expression in
  `SSet.exists_joyal_model_structure`, not the different core-testing encoding.
- The induced map a categorical equivalence: the first conjunct repeats
  exactly that Joyal test for `mappingSimplexChainMap f`.
- Its coherent realization a Dwyer--Kan equivalence: the second conjunct is
  `CategoryTheory.DwyerKanEquivalence` for
  `SSet.Pinched.rigidification.map (mappingSimplexChainMap f)`, with the
  source and target underlying enriched categories explicit. The existing
  `Pinched.rigidification` is the Yoneda left-Kan extension of the subset-poset
  coherent simplices, not an unspecified choice of a functor.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.JoyalModelStructure`,
  `SSet.exists_joyal_model_structure`: its hFun testing expression, with arbitrary
  enlargement `max u v`, is used literally in the hypothesis and conclusion.
- `Sheaf.CategoryTheory.CoherentNerveComparison`,
  `CategoryTheory.coherent_nerve_comparison`, `CoherentNerveComparisonStatement`,
  and `CategoryTheory.DwyerKanEquivalence`: the latter is the exact local weak
  homotopy equivalence plus equivalence on components definition. The comparison
  supplies the mathematical left-Quillen interpretation in the proof plan.
- `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`,
  `SSet.Enhanced.SimplexChain`, `MappingSimplexDegree`, `mappingSimplexOperator`,
  `mappingSimplex`: construction only; the presentation theorem is not assumed.
- `Sheaf.AlgebraicTopology.MappingSimplexConeFibers`,
  `SSet.Enhanced.mappingSimplexChainMap`: the explicit coordinate map only;
  the cone-fibre theorem is not assumed.
- `Sheaf.CategoryTheory.PinchedRigidificationResolution`,
  `SSet.Pinched.coherentSimplex` and `SSet.Pinched.rigidification`: the existing
  subset-poset colimit realization implementing the coherent-realization notion.
  Their definitions and docstrings were read.

Edge cases checked before writing: `n = 0` gives a sole fibre and its map;
empty fibres give empty dependent summands, without any Nonempty assumptions;
all fibres empty give the empty mapping simplex; no fibre or mapping simplex
is required to be a quasicategory. The base index has exactly `n + 1` vertices.
The independent universe `v` permits every larger testing universe, including
`v = 0`; the chains and both realization objects remain in the same arbitrary
small universe `u`. No excluded characteristic or coefficient ring is involved.

Searches: msearch LeanFinder for termwise categorical equivalences of mapping
simplices returned only simplex-category equivalences and standard-simplex
identities. Loogle `mappingSimplex` returned unknown identifier and zero hits.
Mathlib grep `mapping.?[Ss]implex|MappingSimplex` in AlgebraicTopology returned
zero hits. Searches of upstream WeilConjectures for the item id and mapping
simplex names returned no construction or matching theorem. Side-library rg
found exactly the construction and chain map reused above, but no termwise
invariance theorem. No upstream name collision for
`mapping_simplex_termwise_equivalence` was found. Additional definition-specific
LeanSearch, LeanFinder and grep results are preserved verbatim in the new node.

No statement correction and no STATEMENT-DISPUTED issue. The item's natural
statement is unchanged; only its Lean record and the added definition dependency
are changed. All temporary and delivered files are confined to this sandbox.

## New nodes

`def-coef-mapping-simplex-functor` records the mapping-simplex construction and its
map on natural transformations, following HTT Section 3.2.2 and Remark the project server.
It is an `existing: true` binding to `SSet.Enhanced.mappingSimplexChainMap` in
`Sheaf.AlgebraicTopology.MappingSimplexConeFibers`; its domain and codomain use
exactly the existing `mappingSimplex`. No new Lean definition or proof is added.
The three required search types and the side-library/DAG searches are recorded
in its mathlib_searches. Existing theorem nodes own the implementation helpers,
but no definition node states this shared notion separately. The stage-2 record
rule explicitly allows a new definition node to cite a declaration already
landed under another node. Its sole mathematical dependency is the existing
simplicial-set conventions node. It does not cite the presentation or cone-fibre
theorems: those later results depend on final-edge invariance, which in turn
uses this item. This keeps the mathematical prerequisite graph acyclic while
reusing the actual landed construction.

## Second reading by NI

I independently read the base node, sandbox node and complete statement module,
HTT Section 3.2.2 and Remark the project server at the node's primary PDF URL
(https://www.math.ias.edu/~lurie/papers/HTT.pdf, printed pp. 179–180), and the
recorded dependency signatures and the bodies of the constructions used here.
The source introduces arbitrary composable maps of simplicial sets; it assumes
neither fibrancy nor nonemptiness nor injectivity of the transition maps. The
next Cartesian-fibration definition does not impose hypotheses on this remark.
The coherent-realization conclusion follows from HTT Theorem the project server.

My object/hypothesis/conclusion checklist, with verdicts:

1. Finite ordinal and two chains of small simplicial sets: `{n : ℕ}` and
   `{A B : SimplexChain.{u} n}`. I opened the defining abbreviation in
   CartesianMappingSimplexPresentation.lean: it is exactly
   `(Fin (n + 1))ᵒᵖ ⥤ SSet.{u}`. The order-category arrows give all the
   composites in the required direction. PASS; no extra hypothesis.
2. The component maps and all commuting squares: `(f : A ⟶ B)`, a natural
   transformation, with components `f.app (op i)`. Naturality for every
   ordinal arrow is precisely the commuting ladder. PASS.
3. Mapping simplices with the node's degreewise coproduct: `mappingSimplex A`
   and `mappingSimplex B`. I read `MappingSimplexDegree`: its sigma type
   runs over every monotone `α : Fin (r.unop.len + 1) →o Fin (n + 1)` and
   takes the simplices of the fibre at `α (Fin.last r.unop.len)`. PASS.
4. The specified simplicial operators: the data of `mappingSimplex` use
   `mappingSimplexOperator`; its first coordinate precomposes with
   `θ.unop.toOrderHom`, and its second first restricts the original fibre
   simplex and then applies `A.map (homOfLE ...).op`. Monotonicity makes
   that transition go from the old last index to the new last index.
   PASS, including operators whose last index changes.
5. The induced map fixed by the coordinate formula: `mappingSimplexChainMap f`.
   I read its entire definition and `mappingSimplexChainMap_naturality` in
   MappingSimplexConeFibers.lean. The app preserves `z.1` and applies the
   component of `f` at its final index to `z.2`. PASS; no map is supplied
   as an unconstrained hypothesis.
6. Every component is a categorical equivalence: `hf` quantifies over
   every `i : Fin (n + 1)` and every quasicategory `C : SSet.{max u v}`;
   `MonoidalClosed.pre` restricts the internal functor simplicial set,
   `hoFunctor.map` takes its homotopy category, and `.IsEquivalence` is
   ordinary categorical equivalence. I matched this expression literally
   to `SSet.exists_joyal_model_structure` and its node's testing convention.
   PASS; it does not use the distinct core-testing definition.
7. The prescribed induced map is a categorical equivalence: the first
   conjunct uses the identical test with `mappingSimplexChainMap f`. PASS;
   every test and its quantifier order agree with the hypothesis convention.
8. Its coherent realization is Dwyer--Kan: the second conjunct applies
   `CategoryTheory.DwyerKanEquivalence` to
   `Pinched.rigidification.map (mappingSimplexChainMap f)`, with the two
   underlying enriched categories stated explicitly. I opened
   `DwyerKanEquivalence`, `PiZeroEquivalence`, and
   `PiZeroEssentiallySurjective`: these give weak homotopy equivalences
   on all enriched mapping sets and equivalence on component categories,
   exactly as the comparison dependency says. I read `coherentSimplex`
   and `rigidification` in PinchedRigidificationResolution.lean: the latter
   is the Yoneda left Kan extension of the subset-poset coherent simplices.
   PASS; this is the actual coherent realization, not chosen arbitrary data.

Edge cases: `n = 0` has one fibre and reduces to the given component map;
`n = 1` permits an arbitrary non-injective transition. A chain itself has
`n + 1` vertices, so an empty base ordinal is not a case in the node. Individual
fibres may be empty; empty sigma summands and the all-empty mapping simplex
are allowed. No `Nonempty`, quasicategory or monomorphism instance is imposed
on either chain or its mapping simplex. The empty source/target cases still
carry the genuine categorical-equivalence test. Universe `u` is arbitrary;
`v` is independent and `max u v` allows every enlargement and the original
universe at `v = 0`, following the dependency's exact signature. No field,
ring, characteristic, scheme or coefficient assumption occurs.

New-node reading (H12): I read `def-coef-mapping-simplex-functor` against the
same source construction and the existing implementation. Its full chain,
sigma, operator and induced-map formulas agree with the source. It is an
`existing: true` binding, so it adds no duplicate Lean construction. The map's
source and target are the exact existing `mappingSimplex` objects. DAG searches
find theorem nodes owning these helpers, but no prior independent definition
node for this shared construction. Its sole dependency is the recorded general
simplicial-set convention, whose statement and binding I also opened. The new
node has the required definition kind/status, source, empty proof fields,
searches, creation record, ancestry/via, chapter/unit and none audit states;
the item cites it in `stmt_deps`. There is no dependency repair module and no
statement correction, so no statement-change citer audit is applicable.

Independent searches (H4), using other language than the first worker:

- LeanFinder: "Homotopy invariance of the Grothendieck construction of a
  diagram on a finite ordinal under objectwise Joyal equivalences" returned
  truncated homotopy-category natural isomorphisms and ordinary product
  comparisons, with no matching invariance theorem.
- Loogle: `SSet.hoFunctor` returned the existing homotopy-category functor,
  its monoidal/product and ordinary nerve-adjunction interfaces; none states
  mapping-simplex invariance.
- LeanSearch: "Simplicial Grothendieck construction of a contravariant finite
  ordinal diagram, with transition after restriction at the last vertex"
  returned SimplicialNerve, simplicial objects, standard simplices and
  realization. These do not construct the last-fibre sigma object.
- I used `rg` on Mathlib/AlgebraicTopology and upstream WeilConjectures for
  `mapping.?simplex`, `mapping.?cylinder`, termwise categorical and objectwise
  Joyal language, and on the side library for those concepts and the actual
  definition names. No upstream match exists; the side library contains the
  exact reused construction and map. I opened the nearby
  `mapping_simplex_universal_equivalence` signature: it concerns a map to a
  Cartesian fibration and arbitrary base changes, not maps between chains.
  I also opened `categorical_equivalences_colimMap_of_isFiltered`: it concerns
  filtered colimits, not this finite mapping-simplex attachment construction.
- `tools/blueprint_refs.py search "mapping simplex"` returned no blueprint
  nodes, the upstream-name index has no construction/name match, and searching
  the DAG definition nodes found no already recorded mapping-simplex functor.

Mismatches found and repaired: H8, the original proof docstring omitted the
operator-composition step and the specific product/localization/gluing inputs
of the node's five-step proof. I replaced only that proof-plan text with all
five steps, including the degreewise pushout calculation, the single
cofibration leg, and the final preservation input. It also explains the
canonical identification of the existing simplex-colimit realization with
the comparison dependency's left adjoint. H9/stage-2 import rule, the four
already-stated proof dependencies other than the two public statement
imports were missing. I added ordinary imports for
JoyalHomotopyExponentials, ModelCofibrantColimitComparison,
ModelInfinityDerivedAdjunction and ModelLocalizationDetectsWeakEquivalences.
No mathematical mismatch in the theorem's signature or new definition node
was found; neither was rewritten. The signature remains verbatim equal to
`lean.statement`.

Validation: after these repairs, the sole delivered module compiled cleanly
through the prescribed `scompile.py NI lem-coef-mapping-simplex-termwise-equivalence`
wrapper, separately in sandbox and library modes (1.4 and 1.8 seconds).
There are no added definitions or proved theorems; the one theorem proof is
exactly `by sorry`. Every binder and universe is explicit, docstrings have
the source and correct blueprint tag, and every Lean line is at most 100
characters. No read-only project or upstream source was edited.

Server dry run: `deliver2.py NI lem-coef-mapping-simplex-termwise-equivalence
--no-push` printed OK: preflight and compilation pass; four intended files
staged (the theorem module, item node, existing-definition node, and report).
