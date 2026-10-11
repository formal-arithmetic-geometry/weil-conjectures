## Worker report

The module `Sheaf.RingTheory.PairHenselizationNoetherianCompletion` states
`RingTheory.pair_henselization_noetherian_completion`, with one `sorry` proof and no
new definitions. The source is Stacks Project, More on Algebra, Lemma 15.12.4,
[Tag 0AGV](https://stacks.math.columbia.edu/tag/0AGV). The local literature file is
absent on this machine, so the tag's full statement and proof were read online.
No statement correction or disputed statement is needed.

Hypotheses and objects, clause by clause:

- The commutative Noetherian ring `A` is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`; the ideal is `(I : Ideal A)`.
- The henselization is the vertex `c.pt.right` of a cocone over precisely the
  étale neighbourhood category used in `RingTheory.pair_henselization`, with
  `(hc : IsColimit c)`. Its objects are `Under (CommRingCat.of A)` objects whose
  `Spec.map C.hom` is étale and whose induced quotient map modulo `I` is
  bijective. This uses the dependency's existing colimit presentation rather
  than introducing a new definition or an arbitrary henselian algebra.
  The colimit assumption identifies the given ring as the henselization;
  henselianness and the quotient isomorphism follow from the dependency.
- The structure map `η` is `c.pt.hom.hom`, and `Iʰ = IAʰ` is
  `I.map c.pt.hom.hom`. Neither is an unconstrained additional object.
- The two completions are exactly `AdicCompletion I A` and
  `AdicCompletion (I.map c.pt.hom.hom) c.pt.right`.
- The canonical completion isomorphism is the existential `θ : ... ≃+* ...`.
  Its canonicity is the condition for every `n`, completion element `x`, and
  representative `a`: if `evalₐ I n x = mk (I ^ n) a`, then the target
  projection of `θ x` is `mk ((I.map η) ^ n) (η a)`. Quotient maps are
  surjective, so every projected element has such a representative. Thus the
  condition is exactly the levelwise map induced by `η`, and does not assert
  only an abstract isomorphism. Completion elements are determined by all
  their projections, which also establishes uniqueness of this map.
- The assertion that the comparison is an `A`-algebra map is encoded by the
  same coordinate condition: on the image of any `a : A` under the completion
  map, all target projections equal those of the completion of `η a`.
  Therefore `θ` intertwines the structure maps. Its inverse does too.
- `γ` is written directly as `θ.symm.toRingHom.comp
  (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))`.
  This is the prescribed completion map followed by `θ⁻¹`. The preceding
  compatibility shows `γ ∘ η` is the completion map of `A`, exactly the
  node's assertion that `γ` is an `A`-algebra map.
- Noetherianity of `Aʰ` is `IsNoetherianRing c.pt.right`.
- Flatness of `A → Aʰ` is `c.pt.hom.hom.Flat`.
- Faithful flatness of `γ` is `RingHom.FaithfullyFlat` of that exact composite.
  This predicate includes flatness. The node requires no separate conclusion
  about flatness of `A → Â`, and none is added.

Dependency declarations read and used:

- `Sheaf.RingTheory.PairHenselization`, `RingTheory.pair_henselization`:
  full signature and eight-step docstring read. The statement uses its exact
  `ObjectProperty.ι` diagram and the same notion of colimit cocone; arbitrary
  colimit cocones cover all isomorphic realizations of the henselization.
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: all ideals finitely
  generated, as documented in the source.
- `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`: compatible
  quotient sequences. `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the
  commutative ring and algebra structures, `algebraMap_apply`, and `evalₐ`.
  The signatures and docstrings of these APIs were read.
- `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`: target flat as a module via
  the specified map. Its source definition and docstring were read.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`, and
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`, `RingHom.FaithfullyFlat`: faithful
  flatness via the specified map. Their full definitions and docstrings were
  read. The final import supplies both ring-map predicates transitively.

Edge cases checked before writing:

- `I = ⊥`: the henselization is the original ring, the completion is the ring,
  and the comparison and `γ` are identities up to the colimit identification.
- `I = ⊤`: the zero algebra is terminal in the diagram, so the henselization
  and both completions are zero rings; faithful flatness between zero rings
  holds. No proper-ideal assumption is added.
- The zero base ring is allowed; no `Nontrivial`, local-ring, or domain
  hypothesis is used.
- The projection condition includes `n = 0`, whose quotient is the zero ring.
  That coordinate is automatic and introduces no extra condition on the map.
- No characteristic restriction occurs. The single `u` matches the recorded
  henselization category of `CommRingCat.{u}`; no smaller independently
  quantified universe of test algebras can make the hypothesis vacuous.

Searches for an existing statement (via `msearch.py`, also recorded in
`sandbox/searches.jsonl`):

- LeanSearch query: `The henselization of a Noetherian pair is Noetherian and
  has the same adic completion`. Service returned Internal Server Error;
  this search kind was unavailable, with no mathematical verdict inferred.
- LeanFinder query: `henselization of a Noetherian pair is Noetherian, flat
  over the original ring, with isomorphic adic completions and faithfully
  flat map to the completion`. Eight hits, including
  `AdicCompletion.flat_of_isNoetherian`,
  `Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing`,
  `Algebra.Smooth.flat_of_isNoetherianRing`,
  `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`,
  `IsAdicComplete.henselianRing`, and Hausdorff/completion tensor lemmas.
  None states the henselization result.
- Loogle query: `AdicCompletion, RingHom.Flat, RingHom.FaithfullyFlat`:
  zero hits.
- Mathlib grep via msearch, `henseliz`: zero hits. The more targeted query
  `henseliz|completion.*map|def map` in `RingTheory/AdicCompletion` returned
  completion primitives, including linear `AdicCompletion.map` and
  `liftRingHom`; no henselization theorem or ring-map completion functor.
- Direct `rg` in the upstream `WeilConjectures` for
  `henselization|Henselization` found only commentary in
  `EtaleCohomology/Purity/RealSheaves/Boundary.lean`, no declaration.
  Searching the node id there returned no match.
- Direct `rg` in `lean/Sheaf/RingTheory` for the same pattern found
  `PairHenselization`, strict-henselization modules, and other distinct
  henselization results; none states this theorem. In particular strict
  henselization with a chosen residue closure is a different object.
- `rg` in `dag/lean_names_upstream.json` for
  `henselization_noetherian_completion|henseliz|Henseliz` found no match.
  The proposed full declaration name occurs in none of these libraries.

Validation: `lcompile.py` compiled the module with exit code 0 in 2.1 seconds,
with no warnings. The natural-language proof in the theorem docstring follows
all seven recorded proof steps and names their dependencies. Final server
compilation and maintainer preflight are checked by the required delivery dry run.

## Second reading by E1

I reread the node statement and the complete theorem signature clause by clause. The objects are a commutative Noetherian ring `A`, ideal `I`, and a henselization represented by a colimit cocone `c` over the exact étale neighbourhood category from `pair_henselization`, with `hc : IsColimit c`; the vertex and map render `Aʰ` and `η`. The ideal extension is `I.map c.pt.hom.hom`. The two completion objects render `AdicCompletion I A` and `AdicCompletion (I.map c.pt.hom.hom) c.pt.right`. The existential ring equivalence `θ` renders the canonical completion comparison, and the coordinate equation for every `n`, `x`, and representative `a` renders its levelwise map. The final composite renders `γ : Aʰ → A^`. The conclusions render Noetherianity of `Aʰ`, flatness of `η`, the completion equivalence, the `A`-algebra compatibility of `γ`, and faithful flatness of `γ`.

The mismatch found was that the worker signature only encoded the coordinate condition and faithful flatness; it did not explicitly render the node's parenthetical assertion that `γ` is an `A`-algebra map. I added the exact equality
`(θ.symm.toRingHom.comp (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))).comp c.pt.hom.hom = algebraMap A (AdicCompletion I A)`.
This uses the existing structure map directly and introduces no extra `Algebra A c.pt.right` hypothesis. The node's `lean.statement` record was updated verbatim to the repaired signature.

Edge cases remain covered: `I = ⊥` and `I = ⊤`, the zero ring, `n = 0`, arbitrary characteristic, and the single universe `u`; no nontriviality, properness, localness, or independent test universe is assumed. Searches in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing theorem or duplicate notion; the dependency declarations are the recorded `pair_henselization`, `IsNoetherianRing`, `AdicCompletion`, `RingHom.Flat`, and `RingHom.FaithfullyFlat`.
