## Worker report

The module `Sheaf.RingTheory.RingPseudoCoherentLocalizationGlue` states
`DerivedCategory.ringPseudoCoherent_localization_glue`, with proof `sorry`, for both clauses
of the item. No mathematical statement has been corrected or disputed. The extra definition
module supplies precisely the two inline ring-level notions in the original node.

Hypotheses and clauses, matched individually:

- A ring A: `{A : Type u₁} [CommRing A]`. Stacks' ring convention is commutative with identity;
  localization and the tensor product in Tag 066D use this convention. No Noetherian,
  nonzero-ring, or finiteness assumption on A is imposed.
- The integer m: `(m : ℤ)`.
- A complex of A-modules: `(M : CochainComplex (ModuleCat.{max u₁ v₁} A) ℤ)`. M is arbitrary,
  and is not assumed bounded, termwise finite, free, or projective.
- A finite family f₁,...,fᵣ: `(r : ℕ) (f : Fin r → A)`; this is a reindexing starting at zero.
- Generation of the unit ideal: `hf : Ideal.span (Set.range f) = ⊤`.
- The localized complex: `(Functor.mapHomologicalComplex
  (ModuleCat.extendScalars (algebraMap A (Localization.Away (f i))))
  (ComplexShape.up ℤ)).obj M`. Mathlib defines extension of scalars by A_f ⊗_A M,
  naturally isomorphic to M ⊗_A A_f by tensor symmetry over a commutative ring, with the
  A_f action on the localized factor. The complex functor applies this functor degreewise
  to the objects and differentials. This is ordinary localization, as specified in the node.
- Viewing complexes in D(A) and D(A_f): `Q.obj M` and `Q.obj` of the preceding complex.
  The `HasDerivedCategory` instances specify chosen localizations, as the dependency's
  size convention requires; they are not mathematical restrictions. The global module
  universe `max u₁ v₁` contains the ring and arbitrary modules, and scalar extension stays
  in that universe. The two explicitly bound morphism universes `w₁`, `w₂` need not agree.
- Fixed-m hypothesis: the first implication's `∀ i : Fin r, IsRingMPseudoCoherent ... m`.
  Its conclusion is `IsRingMPseudoCoherent (Q.obj M) m`.
- Pseudo-coherent hypothesis: the second implication's `∀ i : Fin r,
  IsRingPseudoCoherent ...`. Its conclusion is `IsRingPseudoCoherent (Q.obj M)`.
  A conjunction of the two implications states both clauses independently, without
  requiring both local hypotheses at once.

The definition module `Sheaf.RingTheory.RingPseudoCoherent` renders the inline definitions:

- The finite free condition is `∀ j : ℤ, Module.Free A (E.X j) ∧ Module.Finite A (E.X j)`.
  Free and finitely generated is exactly finite free, including rank zero.
- A bounded complex is expressed by `∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero (E.X j)`.
- A derived morphism is `α : Q.obj E ⟶ C`; it is not restricted to a specified chain map.
- Isomorphisms above m are `∀ j, m < j → IsIso ((homologyFunctor ... j).map α)`.
- Surjectivity at m is `Epi ((homologyFunctor ... m).map α)`; in ModuleCat epimorphisms
  are precisely surjective linear maps (Mathlib.Algebra.Category.ModuleCat.EpiMono).
- A bounded-above representative is expressed by `∃ b : ℤ, ∀ j, b < j → IsZero (E.X j)`.
- Quasi-isomorphism to that representative is `Nonempty (Q.obj E ≅ C)` in the localization.
  Thus there is no preferred complex representative of the arbitrary derived object C.

Dependency declarations read and used: `def-weil-abstract-derived-category` is a Mathlib
leaf, with no lean record needed. Its declaration `DerivedCategory`, its localization functor
`DerivedCategory.Q`, and `HasDerivedCategory` are in
`Mathlib.Algebra.Homology.DerivedCategory.Basic`; cohomology and its factorization are
`DerivedCategory.homologyFunctor` and `homologyFunctorFactors` in
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. Full signatures and docstrings
were read. `ModuleCat.extendScalars` in `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
and `CategoryTheory.Functor.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`
were read and reused. The added dependency declarations are the two definitions above.
No dependency record was unusable, and no private version of a dependency was introduced.
The theorem docstring carries all four original proof steps and their cited node names.

Edge cases checked before writing: r=0 is permitted. Its span hypothesis forces A to be the
zero ring, over which all unital modules are zero, so both conclusions hold. The zero
complex and acyclic complexes have the rank-zero finite free model; the epi condition
onto zero is satisfied. A generator f_i=0 is allowed and localizes to the zero ring; a unit
f_i gives the original module complex by scalar extension. Arbitrary positive and negative
m and arbitrary unbounded input complexes are allowed. The boundedness witnesses do not
require a nonempty support. No characteristic is excluded. Only finitely many localization
indices are allowed, exactly as the statement requires.

Searches actually run through msearch.py (the same queries are in searches.jsonl):

- LeanSearch: `pseudo-coherent complex finite free bounded above localization gluing`:
  unavailable, HTTP Internal Server Error; this is not recorded as a negative search.
- LeanFinder: `m-pseudo-coherent object of derived category bounded finite free approximation`:
  eight hits concerning DerivedCategory.IsGE, IsLE, and representative/cohomological-support
  lemmas; none define pseudo-coherence or state this gluing theorem.
- Loogle: `"pseudo", "coherent"`: zero hits.
- Mathlib grep: `Pseudo.?Coherent|pseudo.?coherent`: zero hits.
- rg of WeilConjectures and lean/Sheaf with the same pseudo-coherence pattern: one unrelated
  prose mention of Kiehl's theorem in Cohomology/DirectImage.lean; no declaration. The item-id
  grep in WeilConjectures returned no matches. Searches for all three proposed declaration
  names in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found none.
- DAG grep of pseudo-coherent definition nodes found `def-pur-pseudo-coherent-complex`:
  this is locally on a scheme, and does not give either global finite-free ring notion.
  Other hits concern perfect closed immersions, not these definitions. Blueprint search
  `python3 tools/blueprint_refs.py search 'pseudo-coherent'`: zero blueprint matches.
  `ancestor` confirmed `lem-sc-finite-duality`. The dry run checked against the refreshed
  server DAG and required its longer ancestry chain; the new node now records that chain.

Source reading: local literature/stacks-project/more-algebra.tex is absent on this machine.
Read [Tag 066D](https://stacks.math.columbia.edu/tag/066D) and
[Section 064N](https://stacks.math.columbia.edu/tag/064N) directly from Stacks, including
Definition 064P and the fixed-m proof. Both clauses agree with the node. The node's source
place still says Lemma 15.76.4 and mentions 064Z; the stable tag is 066D (currently numbered
15.66.14), while the equivalence used in its fourth proof step is Tag 064U. This stale source
label does not affect the node statement; the module identifies the stable tags correctly.

Validation: scompile.py compiled both modules together on the server with no errors or
warnings. The first combined attempt exposed repeated universe names; distinct explicit
universe names in the sibling modules repaired it. Field-notation line breaks were also
repaired. Definitions contain no sorry; the sole theorem proof is sorry.

## New nodes

`def-pc-ring-pseudo-coherent-complex` defines m-pseudo-coherence and pseudo-coherence of
objects of D(A), verbatim in mathematical content from Stacks Definition 064P (1),(2).
Its module has both real Prop-valued definitions. It cites the existing abstract derived
category node; all module, free/finite, cohomology, epi and boundedness primitives come from
Mathlib. The source, DAG, blueprint and three search kinds listed above found no existing
ring-level notion. The scheme-local pseudo-coherence node is a different definition and
cannot supply a global finite free representative over A without an additional theorem.
Its blueprint ancestor is lem-sc-finite-duality, at the affine local-to-global pseudo-coherence
sentence; its via chain starts with the present item. The item gains only this stmt_deps entry
and its lean record. The new node carries no proof, no hollow data, and no maintainer fields.

## Second reading by C1

I independently read the node statement, its source description, the dependency declaration, and both
Lean modules. The node introduces: (1) a commutative ring `A`; (2) an integer `m`; (3) an arbitrary
complex `M : CochainComplex (ModuleCat A) ℤ`; (4) a natural number `r` and a family
`f : Fin r → A`; (5) the unit-ideal hypothesis `Ideal.span (Set.range f) = ⊤`; (6) the localized
complexes `M^\bullet_{f_i}`; and (7) their derived-category images. Its conclusion has exactly two
independent implications: all local objects are `m`-pseudo-coherent implies the global object is
`m`-pseudo-coherent, and all local objects are pseudo-coherent implies the global object is
pseudo-coherent.

The Lean rendering is exact item by item. `A`, `CommRing A`, and the chosen derived-category
instances occur in the theorem binders. `m`, `M`, `r`, `f`, and `hf` occur with the same
quantification and no extra finiteness, Noetherian, nonzero, characteristic, boundedness, or
projectivity hypotheses. The local complex is rendered by
`Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A
(Localization.Away (f i)))) (ComplexShape.up ℤ)`, which is the Mathlib extension-of-scalars
localization (canonically the tensor localization in the node's notation). The two conclusion
clauses use `IsRingMPseudoCoherent` and `IsRingPseudoCoherent` over the local and global derived
categories in the same implication order. The dependency module defines precisely the node's
bounded finite-free approximation and bounded-above finite-free representative notions; its
`Module.Free` plus `Module.Finite` fields include rank-zero modules and its localization
isomorphism is represented by `Nonempty (Q.obj E ≅ C)`.

I found no statement mismatch and made no Lean or node changes. The only editorial issue observed
is that the node's source field retains the historical `064Z` wording while the worker report and
module identify the current proof route through Tags 066D/064U; this does not alter the requested
statement, so it is left unchanged. The theorem docstring supplies all four proof steps and the
blueprint id, and the definition docstrings cite Tag 064P and the blueprint id. No definition is
hollow; the only `sorry` is the statement theorem proof.

Edge cases checked: `r = 0` is admitted (then the span hypothesis forces the zero ring), zero and
acyclic complexes are allowed, `f i = 0` and unit generators are allowed, arbitrary positive or
negative `m` is allowed, unbounded input complexes are allowed, boundedness witnesses may have
empty support, and no characteristic or universe case is excluded. The explicit universes permit
independent chosen derived-category localizations.

Searches were rechecked from the worker's recorded searches: LeanSearch was unavailable; LeanFinder
returned only generic derived-category support results; Loogle and Mathlib grep found no
pseudo-coherence declaration; grep of `WeilConjectures`, `lean/Sheaf`, and the upstream-name index
found no matching declaration. DAG search found only the unrelated scheme-local
`def-pur-pseudo-coherent-complex`, so the added ring-level definition node is required. Both modules
compile together with `scompile.py` without errors or warnings.

## Fix by reviewer R-pcg0900

The delivery predates the landing of def-pc-ring-m-pseudo-coherent (`DerivedCategory.IsMPseudoCoherent`,
module `Sheaf.RingTheory.MPseudoCoherent`, landed 06:56 UTC with lem-pc-ring-m-pseudo-coherent-vanishing-base)
and defined the same notion a second time as `DerivedCategory.IsRingMPseudoCoherent` (H12/H4: a second
definition of a landed notion). Fixed: `IsRingMPseudoCoherent` removed; the new node
def-pc-ring-pseudo-coherent-complex now defines only pseudo-coherence (Stacks 064P (2)), as
`DerivedCategory.IsPseudoCoherent` (renamed alongside `IsMPseudoCoherent`; bounded above written
`E.IsStrictlyLE b` as in the landed module); its statement and title drop the m-pseudo-coherent clause.
The item's module imports `Sheaf.RingTheory.MPseudoCoherent` and states the first clause with
`IsMPseudoCoherent m (...)`. Statement otherwise unchanged; both fixed modules compile.
