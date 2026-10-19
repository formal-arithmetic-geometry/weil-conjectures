## Worker report

Recovery note: the retained sandbox contained only .brief2–.brief5 and .check,
with no worker report, node copy, Lean module, or previous NB review section.
The previous BLOCKED result accurately described that missing handoff. This
resume reconstructs the missing delivery rather than treating missing files as
an external tool failure. No prior author's Lean statement was available to
compare. The separate stage-1 Q80 report remains available in the read-only
repository and was consulted for the source location, not used as Lean evidence.

The module `lean/Sheaf/CategoryTheory/SimplexJoinAttachment.lean` states
`SSet.Enhanced.quasicategory_simplex_join_attachment`. Its helper definitions
belong to this node: `simplexAttachmentComplex`, `simplexAttachmentSlice`, and
`SimplexJoinAttachment`. No new node, dependency repair, or statement correction
is needed. The original statement, statement dependencies, and proof are retained.

Source read: Lurie, Higher Algebra, September 18, 2017, Lemma the project server and its
whole proof, printed pp. 332–333 (PDF indices 331–332), at
https://www.math.ias.edu/~lurie/papers/HA.pdf. It is a standalone lemma about an
infinity category and a full subcategory, not an operadic statement with ambient
operad hypotheses. There is no Stacks source for this assertion. The source's
condition (*) permits constant maps to the interval, hence empty blocks. The
source asserts a trivial cofibration in the Joyal model structure; the two Lean
properties are precisely mono and the recorded functor-category equivalence test.

Objects and hypotheses:

- Small quasicategory V: `(V : SSet.{u}) [Quasicategory V]`.
- Full subcategory U: the recorded `fullSubcomplex V P`, with arbitrary vertex
  predicate `P : V _⦋0⦌ → Prop`. This parametrizes every full simplicial subset.
- Arbitrary dimension and simplex: `r : ℕ`, `σ : Δ[r] ⟶ V`.
- Nondegeneracy: `SSet.yonedaEquiv σ ∈ V.nonDegenerate r`.
- No vertex in U: `∀ x : Δ[r] _⦋0⦌, ¬ P (σ.app _ x)`.

Conclusions and constructions:

- X is `simplexAttachmentSlice U σ`, the preimage of U under the recorded
  `joinSliceProjection σ`. This is the strict pullback U ×_V V_/σ, including its
  entire initial simplex, not just a condition on its vertices.
- K is `simplexAttachmentComplex U σ`; K_partial is
  `simplexAttachmentComplex U ((boundary r).ι ≫ σ)`. Both include the pure U
  and pure final-factor images, as well as the supremum of mixed block images.
  Mixed generators are maps Δ[a] ⋆ Δ[b] → V whose initial restriction lands in U
  and whose final restriction factors through the specified tail map. Since
  Δ[a] ⋆ Δ[b] is the standard simplex on the concatenated ordinal, these are
  exactly the source's generators. Supremum means the generated subcomplex,
  without assuming the generating predicate is already closed under operators.
- In `SimplexJoinAttachment`, e is fixed by its pure initial face, pure final
  face, and its restriction to Δ[a] ⋆ Δ[r] for EVERY a-simplex of X. This fixes
  every mixed simplex and thus the whole evaluation map, including empty X.
- i is the inclusion K_partial → K, fixed by its equation after ambient inclusion.
  b and w are exactly the boundary evaluation and its commuting square. The
  comparison is `pushout.desc i e w`. This uses the actual categorical pushout.
  Existentially presenting the maps with these determining equations introduces
  no arbitrary-map hypothesis, choice of comparison, or alternate construction.
- The comparison is `Mono` and restriction of functor simplicial sets induces an
  equivalence after `hoFunctor` for every test quasicategory in `max u v`, exactly
  the categorical-equivalence interface in `JoyalModelStructure`.
- The second conjunct states the same construction in V.op for the reversed
  simplex `(stdSimplex.opIso ⦋r⦌).inv ≫ SSet.opFunctor.map σ`. This is the full
  terminal-block assertion under the existing opposite equivalence: its slice is
  the opposite of V_σ/ ×_V U, and reversing the ordered join gives Δ[r] ⋆ X.
  Opposite preserves the displayed pushout and monomorphisms. Reversing the test
  functor categories and their ordinary homotopy categories preserves the Joyal
  equivalence test. There is no independent [Quasicategory V.op] assumption.

Dependencies opened and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`,
  and the actual Mathlib quasicategory convention imported there.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: the right/left cone aliases use
  the same `orderedJoinFunctor`, not a different join. Opened its definitions.
- `Sheaf.AlgebraicTopology.PushoutJoinSaturation`: `joinAugmentation` and
  `orderedJoinFunctor`, whose terminal degree -1 factors retain pure simplices.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `JoinSliceSimplex`, `joinSlice`,
  `joinSliceProjection`, `orderedJoinInl`, and `orderedJoinInr`. Opened the stored
  base, extension, both operator restriction equations, and theorem signature.
  Its first clause says every extension over σ has exactly one stored simplex.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`: `exists_joyal_model_structure`,
  with the explicit larger-universe restriction/hoFunctor test copied here.
- Proof imports: `RelativeConeEquivalence`, `JoinPreservesCategoricalEquivalences`,
  Mathlib `SimplicialSet.Degenerate`, and `MorphismProperty.LiftingProperty`.
  The proof-only node `lem-coef-initial-poset-slice-restriction` has no Lean module
  yet, so no imaginary import was added. Its full DAG statement was read.

Searches, made through msearch.py in this resumed session (raw results are in
searches.jsonl):

1. LeanFinder: `Join slice of nondegenerate simplex full simplicial subset trivial
   cofibration attachment`: eight hits, ordinary Quillen boundary/horn classes,
   nondegenerate-generation lemmas, and subcomplex inclusion. Opened the Quillen
   source and `Degenerate.lean`: none is the Joyal join-slice comparison.
2. LeanSearch: `quasicategory full subcategory join simplex pushout equivalence`:
   eight hits, QCat, Quasicategory, StrictSegal.quasicategory', ordinary category
   full-subcategory equivalence and set pushout relations. Opened Quasicategory's
   exact horn-filler signature; no attachment comparison.
3. Loogle: `"SSet", "attachment"`: zero hits, successful query.
4. grep: `join.*attachment|simplex.*attachment|joinSlice`: zero Mathlib hits.
   Additional direct rg searches of Mathlib's AlgebraicTopology, source
   WeilConjectures/, and repository lean/Sheaf/ used `join.*slice`, `slice.*join`,
   `simplex.*attachment`, `3[.]1[.]2[.]5`, and the proposed declaration names.
   They find the recorded joins, slices, vertex coslices and elementary
   simplex-boundary gluing, but no statement of this node. In particular
   `SSet.glue_simplex` has a different ordinary cell-attachment hypothesis and
   no Joyal conclusion. Its signature was opened. No exact existing declaration
   was found, so `existing: false` is appropriate.

All helper definitions have actual data or explicit Prop formulas. The only
postponed theorem is this node's theorem, with the complete nine-step proof in
its docstring. There are no additional sorry declarations, private notions,
file-local notation/instances, or unbound universe variables. Compilation uses
only the authorized scompile.py wrapper.

## Second reading by NB

The retained work had no NB reading section to preserve. This section records
the source-first recovery and a fresh clause-by-clause check of the reconstructed
module. It does not claim to review an unavailable first worker's Lean text.

Statement checklist (objects, assumptions, and every conclusion):

1. V: `(V : SSet.{u}) [Quasicategory V]` — PASS, arbitrary small quasicategory.
2. U full in V: `fullSubcomplex V P` — PASS, exactly the dependency's notion;
   no extra fullness instance or chosen embedding is assumed.
3. r and σ: `(r : ℕ) (σ : Δ[r] ⟶ V)` — PASS, includes zero dimension.
4. σ nondegenerate: `hσ : yonedaEquiv σ ∈ V.nonDegenerate r` — PASS, the
   actual Mathlib complement of degenerates, not a mono or embedded-boundary
   condition. Opened nonDegenerate and the decomposition declarations.
5. Vertices disjoint from U: `hdisjoint` quantifies every vertex of Δ[r] — PASS,
   exactly absence from P, not disjointness from some smaller selected set.
6. X: `U.preimage (joinSliceProjection σ)` — PASS. Opened the dependency's
   `JoinSliceSimplex` fields to verify that membership restricts the whole source
   face. The resulting subcomplex is canonically the stated strict pullback.
7. K and K_partial: the two `simplexAttachmentComplex` terms — PASS. Checked
   pure initial/final blocks separately, then mixed maps with their exact
   restriction equations. Their image suprema generate all faces and
   degeneracies, matching the source's generated subsets. In particular the
   boundary term uses the map ∂Δ[r] → V, retaining its image identifications.
8. Natural comparison: e's two pure-factor equations and all slice-simplex
   evaluation equations, i's inclusion equation, and w — PASS. Every join
   simplex belongs to a pure factor or is obtained by restricting the extension
   of one slice simplex along a final simplex label. These equations determine
   e uniquely. The ambient inclusions are mono, so they also determine i and b.
   Thus `pushout.desc i e w` is precisely the canonical evaluation comparison,
   not existence of some convenient equivalence between the displayed objects.
9. Monomorphism: `Mono (pushout.desc i e w)` — PASS. This is degreewise
   injectivity in the presheaf category, as required by the Joyal dependency.
10. Categorical equivalence: the hoFunctor/pre/ulift test for every
    `C : SSet.{max u v}` — PASS. Compared verbatim with the Joyal theorem's
    weak-equivalence clause; using `IsFunctorEquivalence` directly on K and the
    pushout would have needed quasicategory hypotheses not present in the node.
11. Terminal-block assertion: the second conjunct in V.op with the reversed
    standard simplex — PASS. Opened `stdSimplex.opIso` to check .inv has direction
    Δ[r] → Δ[r].op. The existing SSet.opFunctor is an actual equivalence, and
    reversal exchanges incoming and outgoing join slices and the two block
    orders. The second conjunct therefore states the specified opposite
    comparison. It does not silently require a separately supplied instance
    for V.op or replace the outgoing slice with a vertex slice.
12. Quantifier order and universes — PASS. Inputs u, V, P, r, σ precede the two
    assumptions and both conclusions; e/i/b are output maps fixed by equations.
    v is unrestricted and occurs only as a larger test universe, exactly as in
    the dependency. No equality of universes or finite-cardinality assumption.

Edge cases: r=0 has empty boundary, K_partial=U, and X⋆empty=X. This makes the
pushout U ⨿_X (X⋆Δ[0]), not a coproduct unless X is empty. If X is empty, the
separate pure-final equation still fixes e on Δ[r]; no empty-factor summand
is dropped. U empty forces X empty but retains the simplex with its actual
boundary identifications. Empty V has no input σ, consistent with the node.
A nonidentity loop in the nerve of a group tests a nonembedded boundary: the
boundary range in K_partial identifies its endpoint images, while no Mono σ
is assumed. All constructions are in an arbitrary u and all categorical tests
in max u v. Zero objects and characteristic have no application to this purely
simplicial assertion; no ring or nonempty index set appears.

Searches independently checked against actual source signatures: LeanFinder's
Quillen model class describes every horn, not Joyal equivalence; Loogle gave no
match; direct project rg searches exposed existing full-subcomplex, ordered-join
and join-slice constructions, all reused. No new definition nodes or dependency
modules were added, so H12/H13 introduce no additional artifacts to audit.

Mismatches/repairs: the handoff itself lacked all required artifacts, so the
module, node lean record, and report were reconstructed. In compilation, Lean's
iSup notation required separate `(a : ℕ) (b : ℕ)` binders; the initial grouped
binder was corrected. No mathematical statement change, dropped edge case,
extra hypothesis, or duplicate definition was found in the final reading.
The opposite assertion is explicitly represented by the second conjunct.

Validation: scompile.py NB lem-coef-quasicategory-simplex-join-attachment
lean/Sheaf/CategoryTheory/SimplexJoinAttachment.lean passed for both its sandbox
and library compile (1.3 s and 1.4 s), with no errors or warnings. Checked by eye
that `autoImplicit false` binds every variable and universe, that all lines are
at most 100 characters, and that the node's lean.statement is extracted verbatim
from the declaration. The only theorem proof is `by sorry` as stage 2 requires.
