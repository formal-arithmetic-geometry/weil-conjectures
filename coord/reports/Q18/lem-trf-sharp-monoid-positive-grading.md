## Worker report

The repair supplies `lean/Sheaf/TraceFormula/SharpMonoidPositiveGrading.lean` and a
complete `lean` record for `exists_strictlyPositiveIntegralGrading`. The theorem has
`sorry` as its only proof, as required for stage 2. It introduces no definitions.
The node is copied from the current shared repository and changes only in `lean`.

Hypothesis and conclusion correspondence:

- The free abelian group is `(G : Type u) [AddCommGroup G] [Module.Free ℤ G]`.
  The canonical integer module structure comes from the additive commutative group.
  The explicit finite-rank witness is `(r : ℕ) (e : Module.Basis (Fin r) ℤ G)`.
  This is exactly a finite basis of the recorded free-module notion. Any finite basis
  can be indexed by `Fin r`; no basis is fixed in advance or restricted by the theorem.
- The additive submonoid is `(P : AddSubmonoid G)`. Its finite generation is
  `(hP : P.FG)`, Mathlib's existence of a finite set whose additive closure equals `P`.
- The condition `P ∩ (-P) = {0}` is expressed as
  `(hsharp : ∀ p : G, p ∈ P → -p ∈ P → p = 0)`.
  The other containment is automatic because zero and its negative belong to `P`.
- The group homomorphism is the existential witness `w : G →+ ℤ`. An additive monoid
  homomorphism between groups is a group homomorphism: it preserves negatives too.
- Strict positivity is precisely
  `∀ p : G, p ∈ P → p ≠ 0 → 0 < w p`.
- Its natural-valued additive restriction is `wP : P →+ ℕ`, and
  `∀ p : P, (wP p : ℤ) = w p` identifies it with the restriction of this same `w`.
  Thus the second map is not an unrelated grading.
- There is no positive-rank, nontrivial-group, nonzero-monoid, saturation or spanning
  hypothesis. In particular, `r = 0` and `P = ⊥` are included.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Module.Free` from
  `Mathlib.LinearAlgebra.FreeModule.Basic`. Its full signature and docstring were read:
  freeness means a nonempty type of bases with an arbitrary index type. The explicit
  `Module.Basis (Fin r) ℤ G` supplies the finite basis required by this item.
- `Module.Basis`, from `Mathlib.LinearAlgebra.Basis.Defs`, was read as the structure
  with `repr : G ≃ₗ[ℤ] (Fin r →₀ ℤ)`, exactly the finite integer-coordinate description.
- `AddSubmonoid.FG`, from `Mathlib.GroupTheory.Finiteness`, is the additive version of
  the finite generating-set closure definition. These two Mathlib imports suffice
  for the signature; no project notion is copied.

The module docstring distinguishes the source's sharp-monoid discussion from the
agent-supplied lattice lemma. I read ILO VIII 3.1.1, 3.1.10 and Remark 3.1.29
(printed pp. 98–99, 103). The remark discusses subdivisions/desingularization;
it does not assert this positive-functional theorem. The theorem docstring contains
all four steps of the current DAG proof: rational cone and sharpness; sum of the
finite half-space forms from `lem-trf-rational-cone-dual-finite`; clearing denominators
on the finite lattice basis; and the natural-valued restriction. That proof dependency
has no recorded Lean declaration on the current base, so no module import is available
for it; it remains a proof dependency, rather than an extra assumption of the theorem.

Searches actually made for this item:

- LeanFinder via `msearch.py`, query “strictly positive integral additive functional on
  a finitely generated sharp additive submonoid of a finite rank free abelian group”:
  eight unrelated results concerning positive regulators, bounds and heights; no match.
- Loogle via `msearch.py`, query `AddSubmonoid.FG Module.Free AddMonoidHom`: the service
  returned a query-elaboration error, so that search was unavailable, not evidence of
  absence.
- Mathlib grep via `msearch.py`, query
  `positive.*grading|strictlyPositive|AddSubmonoid.FG`: the displayed matches concern
  `IsStrictlyPositive` in `Algebra/Algebra/StrictPositivity`, not this theorem.
- LeanSearch via `msearch.py`, query “A finitely generated sharp submonoid of a finite
  rank free abelian group admits a strictly positive integral additive homomorphism”:
  eight hits including `AddSubmonoid.FG`, its map theorem, finite generating maps,
  and `Module.Finite.addMonoidHom`; none states the positive functional assertion.
- Direct `rg` searches in the pinned Mathlib, `WeilConjectures/`, `lean/Sheaf/` and
  `dag/lean_names_upstream.json` found no declaration with the proposed name or a
  positive-grading theorem. The upstream node-id grep found no attachment either.

Edge cases checked mathematically against the signature: rank zero (the empty basis),
`P = {0}` inside a group of any finite rank, `P = ℕ` in `ℤ`, a monoid in a proper
subspace such as `ℕ(1,0)` in `ℤ²`, and a nonsaturated monoid such as the one generated
by `2,3` in `ℤ`. They all remain included. If both a nonzero element and its negative
belong to `P`, `hsharp` fails, as it should. No `STATEMENT-DISPUTED` finding or statement
correction is needed.

## Second reading by Q18

This is a separate checking pass by the same dispatched worker, not an independent
second agent; the brief prohibits spawning agents and assigns independent review to
the maintainer. I reopened the final node and Lean file together. The finite-basis
binder supplies finite rank explicitly, including the empty basis. The existing
`Module.Free` notion is used. `P.FG` means monoid generation, not generation as a group
or an integer module. The sharpness predicate has exactly the two membership premises
needed for `P ∩ (-P)`. The two existential maps have the correct domains and codomains;
the cast equality makes the natural map the restriction of the integer homomorphism.
The positivity clause excludes zero and includes every other element of `P`.
All variables and the universe are explicit; `autoImplicit` is disabled. No `let`
binders, local instances, private notions or proof data occur in the statement.

I also rechecked the four proof paragraphs against the current node: denominator
clearing uses a common positive denominator and the injective lattice embedding;
nonnegative half-space forms sum to a strictly positive form by pointedness; the
finite basis clears all lattice denominators; the final restriction includes zero.
The module and node signature agree verbatim. No mathematical mismatch was found.

## Returned delivery repaired

The returned head `497a16e70864` was a stage-1 packet with no Lean module or binding.
This repair adds the actual statement module and complete record, explicit finite
rank, and both required report headings.

The old packet cited `lem-trf-positive-functional-pointed-rational-cone`. The current
reviewed base explicitly removed that unnecessary child and replaced it with the
existing `lem-trf-rational-cone-dual-finite`; see the current item's `split_report`.
This delivery follows that reviewed node, without resurrecting an absent child or
changing the current statement or proof. The proof docstring includes the elementary
argument that sums the half-space forms. There are no new nodes or dependency modules.

## Compilation evidence

The final command was:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q18 lem-trf-sharp-monoid-positive-grading lean/Sheaf/TraceFormula/SharpMonoidPositiveGrading.lean
```

It exited 0 with no errors or warnings. The final sandbox check took 1.3 seconds and
the library-module check took 6.6 seconds, both under the unchanged 60-second limit.
The signature in `lean.statement` was extracted directly from the final file and checked
for exact equality with real newlines. The node delta was checked to be `lean` only;
the maximum Lean line length is 96 characters. The record's date is from `date -u +%F`.
