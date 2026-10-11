## Worker report

The module states `geometricallyRegular_of_directed_subfields`. It uses the landed
`Algebra.IsGeometricallyRegular` definition from `Sheaf.RingTheory.GRing`; the conclusion
is geometric regularity of the Noetherian `k`-algebra `A` over `k`.

The Lean binders render the node as follows. `(k : Type u) [Field k]` is the base field;
`I` with `[Nonempty I]` and `K : I → Subfield k` is the nonempty family of subfields.
`hdir` says each pair of subfields is contained in a common member, and `hUnion` says
every element of `k` belongs to some member, i.e. their union is `k`. `A` is a commutative
`k`-algebra, `hA : IsNoetherianRing A` is the Noetherian hypothesis, and `hgeom` gives
`Algebra.IsGeometricallyRegular (K i) A` for every index. The conclusion is
`Algebra.IsGeometricallyRegular k A`.

Dependency used: `Sheaf.RingTheory.GRing`, declaration `Algebra.IsGeometricallyRegular`.
The Mathlib dependency `IsNoetherianRing` is used through the landed G-ring declaration
and directly in the theorem hypothesis. `def-pc-field-extension` is a conceptual leaf;
subfields are represented by Mathlib's `Subfield k`, whose subtype carries the field
structure and scalar algebra instance used by `Algebra.IsGeometricallyRegular`.

Edge cases checked: `Nonempty I` permits a singleton index family; `hUnion` permits the
family member itself to be `⊤`; no finiteness, characteristic, or nonzero restriction is
added, and `A` may be the zero ring only when its supplied commutative-ring instance allows
it. The universe of `A` is `Type (max u v)`, so finite extensions quantified by the
geometric-regularity definition are not excluded.

Searches for an existing declaration: `msearch.py F1 lem-weil-pbc-geometrically-regular-over-subfields
leanfinder "geometric regularity over a directed union of subfields"` found no match;
`msearch.py ... loogle "geometricallyRegular_of_directed_subfields"` found no match;
`rg -n -i 'geometrically.?regular.*subfield|directed.*subfield'` in Mathlib and
`WeilConjectures/` found no matching theorem. The existing notion
`Algebra.IsGeometricallyRegular` was reused from `Sheaf.RingTheory.GRing` rather than
redefined.

No `STATEMENT-DISPUTED` issue.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. Every node hypothesis has a direct binder:
field `k`, nonempty directed family `K`, union condition `hUnion`, Noetherian algebra
`A`, and geometric regularity over each `K i`. The single conclusion is exactly the
node's geometric regularity over `k`; no clause or edge case is omitted.

## Second reading by F1

I independently opened the sandbox node and module, all three statement-dependency nodes,
`lean/Sheaf/RingTheory/GRing.lean`, and the recorded Mathlib declarations. I read Stacks
Algebra Lemma 07QG and Definition 0382 / Lemma 0381 in the local source mirror
`/home/ubuntu/c1-stacks-review/algebra.tex`, lines 47104–47220; the mirror's `tags/tags`
confirms those labels. The repository's `literature/stacks-project` source is not present
on this machine. The source imposes no characteristic, finite-type, or nontriviality
hypothesis on A. Its geometric-regularity definition assumes Noetherianity. The typo
in its base-change identity is already explicitly corrected in the node's source record.

Node statement inventory and final Lean matching (H3):

- Object: arbitrary field k. `(k : Type u) [Field k]` gives exactly that field; PASS.
- Object: nonempty family of subfields of k indexed by I. `(I : Type v) [Nonempty I]`
  and `(K : I → Subfield k)` give genuine subfields of this same field; PASS.
- Hypothesis: directed by containment, each pair lies in one member.
  `hdir : ∀ i j : I, ∃ l : I, K i ≤ K l ∧ K j ≤ K l` is exactly the union-containment
  condition, with no order or finite-size assumption on I; PASS.
- Hypothesis: the family has union k. `hUnion : ∀ x : k, ∃ i : I, x ∈ K i` is exactly
  coverage; the reverse inclusion is inherent in `Subfield k`; PASS.
- Object: a commutative k-algebra A. `(A : Type w) [CommRing A] [Algebra k A]`;
  PASS after removing the original unnecessary `Type (max u v)` restriction.
- Hypothesis: A is Noetherian. `hA : IsNoetherianRing A`; PASS. The dependency's
  `IsNoetherianRing` is `IsNoetherian A A`, and `isNoetherianRing_iff_ideal_fg` confirms
  that every ideal is finitely generated. The same condition also occurs inside hgeom;
  naming hA does not strengthen the node's explicit assumption.
- Scalar restriction: A over each K i is via K i → k → A. Mathlib's
  `Algebra.ofSubsemiring` in `Algebra/Algebra/Basic.lean:101` has ring homomorphism
  `(algebraMap k A).comp (Subsemiring.subtype (.ofClass (K i)))`, with inherited scalar action.
  `Subfield.toAlgebra` and `algebraMap_ofSubfield` give the subtype inclusion into k.
  No arbitrary algebra instance over K i is assumed; PASS. This also realizes the
  field-extension dependency's `[Field K] [Field L] [Algebra K L]` convention.
- Hypothesis: geometric regularity over every K i.
  `hgeom : ∀ i : I, Algebra.IsGeometricallyRegular (K i) A`; PASS. I read the landed
  definition: Noetherian A and regularity of `TensorProduct (K i) k' A` for all finite
  purely inseparable extensions k'. This is the node's definition dependency, not
  geometric reducedness or smoothness.
- Single conclusion: geometric regularity over k.
  `Algebra.IsGeometricallyRegular k A`; PASS, using the same dependency definition.
  No conclusion clause is omitted or added; quantifiers have the node's order.

Edge cases: empty I is excluded by the node itself; singleton I and K i = ⊤ are allowed.
The zero algebra is allowed because `[CommRing A]` and `[Algebra k A]` impose no
`Nontrivial A` or faithful scalar action. No schemes or integer n occur in this node.
All characteristics are covered, including characteristic zero where finite purely
inseparable extensions are trivial. The proof's empty list of coefficients is covered
by `Nonempty I`. Universes u, v, w are now independent and explicitly declared.
The reused definition tests extensions in `Type (max u w)` both for k and for K i,
which contains representatives of every finite extension and is not a smaller,
independent universe making the hypothesis vacuous.

Independent duplicate searches (H4), using different phrasing from the first worker:

- `msearch.py ... leansearch "regularity of a Noetherian algebra descends from each field
  in a filtered union of base fields"`: service unavailable (Internal Server Error),
  recorded as unavailable; no mathematical verdict inferred from this failure.
- `msearch.py ... leanfinder "A Noetherian algebra is geometrically regular over a field
  that is a filtered union of smaller fields if it is geometrically regular over each
  smaller field"`: eight results, involving geometric reducedness, finite generation,
  and smoothness; none states this regularity theorem.
- `msearch.py ... grep "geometrically.?regular|regular.*(subfields|union.*fields)"`:
  no Mathlib hits. The same rg search in `WeilConjectures/` and repository `lean/Sheaf`
  found no source theorem and only GRing's definitions and unrelated project statements
  about completion/formal fibres. The existing GRing notion is reused, not redefined.

There are no new definition nodes or dependency modules in this delivery; the existing
three dependencies suffice. No statement correction or citer verdict needs review.
The node's mathematical statement and proof remain unchanged.

Faults and repairs: H8, the original theorem docstring contained no natural-language
proof; added all five node steps with their dependency IDs and the Stacks typo note.
H9, the original module lacked the standard license/authorship header; added it and
moved the universe command after the module docstring. H3, the algebra's universe was
unnecessarily tied to the base and index universes; replaced it with independent w.
Updated `lean.statement` verbatim from the final signature. No hollow definition or
private predicate was introduced, and the sole theorem remains proved by `sorry`.

Validation: the repaired module compiled cleanly with the prescribed `scompile.py`
(single file on the server); all variables/universes are bound, and lines are at most
100 characters. The delivery dry run and final delivery are performed after this report.
