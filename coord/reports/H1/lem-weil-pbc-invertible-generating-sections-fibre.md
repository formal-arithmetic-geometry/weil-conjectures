## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleGeneratingSectionsFibre` states
`AlgebraicGeometry.Scheme.Modules.invertible_generating_sections_fibre_criterion`.
It has one theorem with a `sorry` proof, no definitions and no other proved declarations.

Hypothesis and clause matching:
- An arbitrary scheme Y is `(Y : Scheme.{u})`; no finiteness, separation or base hypothesis.
- The O_Y-module is `(L : Y.Modules)`; invertibility is `[L.IsInvertible]`.
- The family s_0,...,s_n is `(n : ℕ)` and
  `(s : ULift.{u} (Fin (n + 1)) → L.sections)`. ULift changes only the index universe,
  not the n+1 indices. Compatible sections of the sheaf are exactly sections on ⊤:
  evaluation is `(s i).val (Opposite.op ⊤)` and restriction supplies the inverse.
- Generation of this given family, not existence of some family, is
  `Epi (L.freeHomEquiv.symm s)`. This is the epi field of Mathlib's
  `SheafOfModules.GeneratingSections` with these exact sections and index type.
- Y_s is the existing `nonvanishingLocus L ((s i).val (Opposite.op ⊤))`.
  Its definition is precisely germ(s) ∉ maximalIdeal • ⊤ in the stalk module.
  It expresses the node's first definition of Y_s; quotienting by maximalIdeal • ⊤
  identifies this with nonzero value in L_y ⊗ κ(y), so no chosen trivialization or
  different notion of nonvanishing is introduced.
- The first equivalence is generation ↔ `∀ y : Y, ∃ i, y ∈ nonvanishingLocus ...`.
- The second equivalence is generation ↔ `(⋃ i, nonvanishingLocus ...) = Set.univ`.
  The conjunction states both equivalences of the node with the same family.

Dependencies read and used:
- def-sc-invertible-module: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local isomorphism with the unit module.
  Imported through Ample.
- def-weil-pbc-generating-sections: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.GeneratingSections`, and its underlying `freeHomEquiv` from Sheaf.Free.
  The dependency's note specifically records the Epi formulation for a given finite family.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  `AlgebraicGeometry.Scheme.residueField`; read its definition as
  `IsLocalRing.ResidueField (Y.presheaf.stalk y)` and `Scheme.residue`.
  No redundant import is needed: the statement uses the equivalent maximal-ideal predicate.
- Added the already landed node def-weil-pbc-ample-invertible-module to stmt_deps for
  `Sheaf.AlgebraicGeometry.Ample`, `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`.
  This follows coord/STATE.md's NON-VANISHING LOCUS rule and brief-stage2 §5's permission
  to cite landed nodes. The item statement is unchanged; ampleness is not a hypothesis.

Edge cases: n=0 means one section; the theorem says it is everywhere a generator.
The zero section cannot generate on a nonempty scheme, and its nonvanishing locus is empty.
On the empty scheme, pointwise nonvanishing is vacuous, the union equals the empty universal
set, and the free-module map is epi. The node has n+1 indices, never an empty index set.
No field characteristic or scheme universe is excluded. Invertibility excludes a zero stalk
at a point, exactly as required for the one-dimensional argument.

Searches (actual queries and results are also recorded in searches.jsonl):
- msearch.py leansearch: 'global sections of an invertible module generate iff they have
  no common zero': service unavailable, Internal Server Error; no verdict.
- msearch.py leanfinder: 'global sections of a line bundle generate if and only if their
  residue fibre values are not all zero': eight hits, including structure-sheaf evaluation
  basicOpen lemmas, Tilde.exists_const and GeneratingSections.s; no full criterion.
- msearch.py loogle: 'SheafOfModules.GeneratingSections': twelve structure and field hits,
  no equivalence with a nonvanishing cover.
- msearch.py grep: 'nonvanishingLocus|generat.*fiber|generat.*stalk' in
  Mathlib/AlgebraicGeometry: no hits.
- rg of WeilConjectures for generating/nonvanishing/fibre/stalk combinations: no theorem
  stating this equivalence; occurrences concerning affine algebras or constructible sheaves.
  Search for the exact node id there had no hits.
- rg of lean/Sheaf found Ample.nonvanishingLocus, GlobalGenerationNonvanishingCover
  (only the forward implication for all global sections), and FiniteSectionsCover
  (existence of some finite cover); none is the criterion for this fixed family.
- dag/lean_names_upstream.json was checked for the locus and candidate criterion name;
  no competing declaration of the new theorem.

Sources checked online because the local literature checkout lacks modules.tex:
[Stacks 01AM](https://stacks.math.columbia.edu/tag/01AM) supplies generation by the
free-module map; [Stacks 01CY](https://stacks.math.columbia.edu/tag/01CY) supplies the
maximal-ideal nonvanishing predicate and rank-one Nakayama argument.
No disputed statement or correction was necessary. The docstring records all six proof steps.

## Second reading by H1

I independently read the item node, its six proof steps, its source, every statement
 dependency node and the actual declaration signatures. The source `.tex` is absent
 locally, so I read `modules.tex` directly from the Stacks upstream checkout
 (https://raw.githubusercontent.com/stacks/stacks-project/master/modules.tex), at
 `definition-globally-generated` (01AM) and `lemma-s-open` (01CY), including the proof.
 I also read https://stacks.math.columbia.edu/tag/0H7H, part (2). The source assumes
 local stalk rings, which schemes supply; it imposes no Noetherian, characteristic,
 compactness or separation condition. Nothing from the ampleness definition is assumed.

The node's objects, hypotheses and conclusions, matched individually:

- Arbitrary scheme Y: `(Y : Scheme.{u})`. Exact, with arbitrary bound universe `u`.
- An O_Y-module L: `(L : Y.Modules)`. Exact scheme module category.
- L invertible: `[L.IsInvertible]`, the recorded upstream scheme declaration in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`. I read `exists_isoUnit`:
  every point has an open neighbourhood with an isomorphism to the unit module.
  This is local rank one; quasi-coherence follows from this local description.
  No stronger hypothesis is present. The definition's restriction along an open
  immersion gives ordinary restriction, so it is the dependency's intended notion.
- Finite given global sections s_0,...,s_n: `(n : ℕ)` and
  `(s : ULift.{u} (Fin (n + 1)) → L.sections)`. Exact n+1 indices.
  `SheafOfModules.sections` is `M.val.sections`, and
  `PresheafOfModules.sections` is the compatible family of sections of the underlying
  presheaf. Evaluation at `Opposite.op ⊤` gives a global section; restriction from ⊤
  supplies the inverse. Thus these are arbitrary global sections, without extra data
  or restrictions. ULift is a bijective reindexing required by `free`'s index universe.
- Generation of this family: `Epi (L.freeHomEquiv.symm s)`. Exact. I read
  `SheafOfModules.GeneratingSections` (its `epi` field) and `freeHomEquiv`:
  `free I` is the coproduct of structure-sheaf units and the inverse equivalence
  maps its i-th summand by the section s_i. This is precisely sigma in the node,
  with sheaf surjectivity, rather than surjectivity on every section space.
- Y_s and the residue value: `nonvanishingLocus L ((s i).val (Opposite.op ⊤))`.
  I opened `Sheaf.AlgebraicGeometry.Ample` and checked the definition: the germ is
  outside `maximalIdeal (Y.presheaf.stalk y) • ⊤`. This is literally the node's
  first predicate, and quotient by this submodule identifies it with nonzero value
  in L_y tensor kappa(y). The recorded `Scheme.residueField` is the local stalk's
  `IsLocalRing.ResidueField`. No competing residue field or locus is introduced.
- First conclusion: the first conjunct is generation iff
  `∀ y : Y, ∃ i, y ∈ nonvanishingLocus ...`. Exact point-then-index quantifier order;
  the successful section can depend on the point.
- Second conclusion: the second conjunct is generation iff
  `(⋃ i, nonvanishingLocus ...) = Set.univ`. Exact equality of the finite union
  with Y. Both conjuncts use the same specified family; neither asserts merely
  existence of a generating family. No clause is weakened or strengthened.

Edge cases: `n = 0` is one section, with no artificial positivity hypothesis. There
 is no empty index set in the node's s_0,...,s_n. All zero sections fail both criteria
 on any nonempty scheme. The zero module cannot be invertible there because its stalk
 cannot be isomorphic to a nonzero local ring. On the empty scheme invertibility and
 the point criterion are vacuous, Set.univ is empty, and sigma is epi in the trivial
 module category, so the equivalences remain correct. Arbitrary characteristics,
 nonreduced schemes and all scheme universes are admitted; no test-object quantifier
 can become vacuous through a smaller universe.

Independent searches (different wording from the worker):

- LeanFinder: `finite sections span a locally free rank one sheaf exactly when the
  zero loci have empty intersection`. Eight hits: module free loci, localized module
  support and Tilde section submodules; none states this criterion.
- Loogle: `SheafOfModules.freeHomEquiv`. Twelve hits for the equivalence, functoriality,
  generating-section fields and presentations; none identifies generation with the
  nonvanishing cover.
- LeanSearch: `surjectivity from a finite free module sheaf to a line bundle detected
  by residues of given sections`. Service returned Internal Server Error; recorded
  as unavailable, without drawing a search verdict.
- rg in Mathlib's scheme and module-sheaf sources, the upstream project's
  AlgebraicGeometry sources, and the project's `lean/Sheaf/AlgebraicGeometry` for
  `no common zero`, `fibre_criterion`, `fiber_criterion`, `nonvanishing`, and generation
  with stalk/fibre/fiber. Mathlib contains no matching scheme criterion. Upstream
  coordinate covers concern structure-sheaf coordinates; ample-family occurrences
  concern affine nonvanishing covers. I opened the project's
  `GlobalGenerationNonvanishingCover` and `FiniteSectionsCover`: the former is only
  an implication for all sections, the latter existentially selects a finite cover
  with a compactness hypothesis. Neither states the equivalence for this fixed family.
  The proposed full declaration name also has no upstream/Mathlib/name-map collision.

No new nodes or dependency modules are delivered. The added, already landed dependency
 `def-weil-pbc-ample-invertible-module` correctly supplies the single shared locus
 definition; its module contributes no ampleness hypothesis. No `statement_change`
 exists or is needed. I found no mathematical or signature mismatch and retained the
 Lean and node record unchanged. Both imports are used, all variables and the universe
 are explicitly bound, and the source/blueprint docstrings include all six proof steps.
 The only theorem has `sorry`; there are no definitions or proved declarations.
 `lean.statement` agrees verbatim with the theorem signature.

Validation: remote single-file `scompile.py` succeeded in 2.0 seconds, exit code 0,
 with no warnings. The initial invocation from the repository used a nonexistent
 relative path; rerunning from the authorized sandbox resolved that invocation error.
 Second reading changes only this report, adding the independent verification above.
