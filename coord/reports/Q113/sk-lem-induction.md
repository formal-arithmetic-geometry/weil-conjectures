## Worker report

Q113, stage 2, 2026-10-17. Reuse the existing statement
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt` from
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction`, lines 68–72.
Read its full signature, ambient binders, docstring, and proof, and independently
read the published source with `scompile.py --source` (identical declaration).
No new module, definition, theorem, or proof is delivered. Only the item's `lean`
record changes; its statement, split, dependencies and audit remain unchanged.

The source read is `main-20261015/blueprint/sec-smooth-base-change/sk-lem-induction/`
`_section.md` and `sk-lem-induction.proof.md`. The statement there agrees with the
node. The five-step DAG proof additionally makes the affine-base reduction
explicit using `sk-lem-failure-field`, transports the geometric and lower-degree
hypotheses, applies `sk-lem-universal-datum`, contradicts `sk-thm-vanishing`, and
closes the universal quantifier. This stage does not certify those proofs.

Hypothesis and conclusion correspondence:

| Node clause | Existing Lean rendering |
| --- | --- |
| Schemes X and S and morphism f | Ambient `{X S : Scheme.{u}} {p : X ⟶ S}` |
| f affine | `[IsAffineHom p]` |
| f smooth of relative dimension one | `[SmoothOfRelativeDimension 1 p]` |
| X affine | `[IsAffine X]` |
| A commutative ring Λ | Ambient `{Λ : Type (u + 1)} [CommRing Λ]` |
| n invertible on S | `(n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))` |
| nΛ = 0 | `(hΛ : (n : Λ) = 0)` |
| Integer q ≥ 1 | `{q : ℤ} (hq : 1 ≤ q)` |
| Every integer q' < q satisfies BC universally | `∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q'` |
| BC in degree q holds universally | `Etale.UniversalBaseChangeProperty Λ p q` |

The source calls n an integer; the upstream API uses a natural-number annihilator.
This changes no cases: replace an integer n by its absolute value. Its image in
any ring is the image of n or its negative, so being a unit and vanishing in Λ
are both preserved. Conversely a natural number is an integer with exactly the
same casts. No positivity assumption is added, including at n = 0. Moreover,
nΛ = 0 is equivalent to n·1 = 0 for a unital ring, which is exactly the cast
equality `hΛ`. No restriction to cyclic or finite coefficient rings occurs.

Dependency declarations read and used:

- `sk-def-bc`: `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`,
  `AlgebraicGeometry.Etale.BaseChangeProperty`,
  `AlgebraicGeometry.Etale.baseChangeHomologyMap`, and
  `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`. Read the entire module,
  including the derived-map implementation and its interpretation in the
  docstring. The fixed-base property quantifies over all qcqs g, all Cartesian
  squares and all Λ-module sheaves; its map is homology of the canonical derived
  exchange on sheaves placed in degree zero. The universal property additionally
  quantifies over every preliminary Cartesian base change. Thus `hprev` and the
  conclusion are the universal, single-degree properties in the node.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom`, lines 45–48 and its docstring. Its field says
  the inverse image of every affine open is affine, precisely the node's notion.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, lines 58–65, and
  `AlgebraicGeometry.SmoothOfRelativeDimension`, lines 127–146, with docstrings.
  The latter uses standard smooth charts of relative dimension one and implies
  Smooth. This is the recorded dependency's interface; no private definition
  is introduced and no separate smoothness assumption is missing.

Edge cases checked: q = 1 retains all q' < 1, including negative degrees and zero;
q = 0 and negative q are outside the stated hq hypothesis. n = 0 is retained:
0 can be a unit on an empty base with zero global-section ring, so no `0 < n`
may be silently added. Negative integer annihilators are covered by absolute
value as explained above. The zero coefficient ring and the empty source or
base are retained; relative dimension is tested at points and imposes no
nonemptiness condition. The coefficient universe is u+1, exactly the convention
of the recorded small-étale module-sheaf dependency; u is arbitrary and schemes
and coefficients can be lifted into this common convention. Every q' is an
integer, rather than silently restricting the lower-degree hypothesis to naturals.

Searches actually run for this worker:

- `msearch.py ... leanfinder`: "induction step universal etale cohomological
  base change affine smooth relative curve lower degrees". Eight results,
  including `AlgebraicGeometry.IsSmoothOfRelativeDimension` and smooth/étale
  algebra permanence; none states the cohomological induction step.
- `msearch.py ... loogle`: `"baseChange", "cohomology"`. Zero hits.
- `msearch.py ... grep`: `UniversalBaseChangeProperty|baseChangeHomologyMap|higherDirectImage`,
  subdirectory `AlgebraicGeometry`. Zero Mathlib hits.
- `rg` of the upstream project for the node id and
  `UniversalBaseChangeProperty.of_forall_lt`: found the declaration at Induction
  line 68 and its references in that module and Theorem. Read the matching
  signature and docstring, rather than inferring agreement from its name.
- `rg` of `lean/Sheaf` for the same strings: found
  `Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction`. Read it in full: it
  belongs to `sbc-lem-rel-dim-one-induction` and specializes coefficients to
  `ULift (ZMod n)`, adds positivity, takes a natural q, and has a cumulative
  hypothesis and conjunction conclusion. It is not the arbitrary-ring statement
  of this item and cannot replace the upstream declaration selected here.
- Searched `dag/lean_names_upstream.json` and `coord/repair-notes` for the item
  and selected name; no repair note or additional binding was returned.
  Raw search receipts are retained in this sandbox's `searches.jsonl`.

The inherited Q55 route note concerns a stage-1 packet and an impermissible
stage-1 ATTACH asserting a sorry-free proof. Its named retained packet directory
is absent on this machine; only Q55/ATTACH.md remains. The prescribed
`deliver.py Q55 sk-lem-induction --no-push .` was attempted. This delivery follows
the actual Q113 stage-2 brief: §1 explicitly requires reuse of an exact existing
statement, without requiring that its proof be closed. This is not a stage-1
ATTACH. The audit recording eleven reachable sorry declarations is unchanged;
no proof completion is claimed. No mathematical statement fault was found.

Validation: a scratch file imports the existing module, checks the declaration
with all implicit parameters exposed, and prints its axioms through the mandated
`scompile.py` wrapper. `deliver2.py --no-push` also generates an existing-name
probe and runs current server preflight. Results are recorded below after the run.

The scratch check compiled cleanly against both sandbox and library in 6.2 s
and 6.1 s. Its full type matches the table above. `#print axioms` reported
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, confirming that this
is statement reuse with outstanding proofs, not a certified stage-1 completion.

## Second reading by Q113

Independent second reading, 2026-10-17. I opened the node copy, its blueprint
statement and proof, the enclosing chapter, and the existing Induction module
including its ambient binders, docstring and proof. I also obtained that module
through `scompile.py --source`; the published signature agrees with the local
source. The source is the blueprint's arbitrary-ring induction step, not a
separate tagged Stacks lemma. I read Stacks `etale-cohomology.tex`, Remark
`remark-base-change-holds` (0F02), the statement of
`theorem-smooth-base-change`, and its second proof (0EYU): the induction starts
at degree zero, reduces to affine smooth relative curves, and contradicts the
universal counterexample datum with generic-fibre vanishing. The source assumes
no Noetherian, separated, field-base or coefficient-finiteness condition here.
Stacks uses cyclic coefficients; this item's explicit arbitrary-ring version
is the blueprint statement, which agrees with the recorded theorem.

My object/hypothesis/conclusion checklist, with verdicts:

| Node item | Lean rendering, read in its ambient context | Verdict |
| --- | --- | --- |
| Schemes X and S | `{X S : Scheme.{u}}` | Same objects; arbitrary universe u. |
| Morphism f : X → S | `{p : X ⟶ S}` | Only a binder renaming. |
| f affine | `[IsAffineHom p]` | Exact dependency predicate. |
| f smooth of relative dimension one | `[SmoothOfRelativeDimension 1 p]` | Exact recorded predicate; implies Smooth. |
| X affine | `[IsAffine X]` | Present; no assumption that S is affine. |
| Commutative coefficient ring Λ | `{Λ : Type (u + 1)} [CommRing Λ]` | Arbitrary commutative unital ring, including zero. |
| Integer annihilator n | `(n : ℕ)` | Equivalent parameterization here by absolute value, as detailed below. |
| n invertible on S | `(hn : IsUnit (n : Γ(S, ⊤)))` | Global inverse, equivalent to invertibility on S. |
| nΛ = 0 | `(hΛ : (n : Λ) = 0)` | Exact: evaluate annihilation at 1; conversely multiply by any element. |
| Integer q ≥ 1 | `{q : ℤ} (hq : 1 ≤ q)` | Same range. |
| Universal BC in every integer q' < q | `(hprev : ∀ q' < q, Etale.UniversalBaseChangeProperty Λ p q')` | Every lower degree, every preliminary base change. |
| Universal BC in degree q | `Etale.UniversalBaseChangeProperty Λ p q` | Same single-degree conclusion, without an added conjunct. |

For the n binder, the conclusion and hprev do not depend on n. For an integer
annihilator z, its absolute value has image either z or -z in every ring, so
both being a unit on S and being zero in Λ are preserved. Conversely every
natural annihilator is an integer annihilator. This includes z = 0 and imposes
no positivity condition. Thus the existing theorem covers exactly the cases
of the node; no new wrapper or statement correction is needed.

I opened all three statement dependencies and their recorded interfaces.
`pqf-def-affine-morphism` has the Mathlib match `IsAffineHom`, whose field is
`∀ U, IsAffineOpen U → IsAffineOpen (p ⁻¹ᵁ U)`, exactly the node's affine-open
condition. For `def-sbc-smooth-morphisms`, Mathlib's `Smooth` is affine-locally
smooth on rings, and `SmoothOfRelativeDimension` uses standard-smooth charts
of the given relative dimension; the recorded 02H6/02G1/02G2 comparison gives
the source's smoothness and constant fibre dimension. I read both signatures
and the implication `SmoothOfRelativeDimension.smooth`.

For `sk-def-bc`, I read the whole upstream Defs module. `BaseChangeProperty`
quantifies over arbitrary qcqs g, every Cartesian square and every sheaf of
Λ-modules. `UniversalBaseChangeProperty` first quantifies over arbitrary
`a : S' ⟶ S`, a Cartesian base change p', and then invokes that fixed-base
property. Neither preliminary maps nor p are required qcqs by the predicate.
The degree map is homology of the derived exchange applied to F in degree
zero, exactly as this dependency explicitly defines it. I also read
`MorphismDefs`' unit insertion, pullback-square comparison, counit contraction
and their composite `Etale.baseChange`; the map is canonical, not an arbitrary
chosen arrow. All these definitions have real data. There are no new nodes or
dependency modules in this delivery and no item repair note is present.

Edge cases: q = 1 includes degree zero and all negative q'; q = 0 and negative
q are deliberately outside hq, just as in the source. The empty source and
empty base are allowed; the relative-dimension condition is pointwise and has
no nonemptiness premise. In particular n = 0 is retained on the empty base,
whose global ring is zero. The zero coefficient ring is retained. There is no
characteristic restriction other than the stated unit and annihilation
conditions. No index set occurs in this statement. The universe convention is
that of the recorded small-etale dependency, with Scheme.{u}, arbitrary u,
and ModuleCat.{u+1} over Λ : Type (u+1); the theorem adds no universe equation
or smallness premise. No unbound variable or extra instance appears in the
fully explicit compiler output.

Independent searches used different wording from the worker:

- `msearch.py ... leansearch` with "Smooth curve torsion sheaf base change
  isomorphism from smaller cohomology degrees": eight algebraic base-change,
  differential and smoothness-permanence hits, no cohomological induction.
- `msearch.py ... loogle` with `"baseChange", "degree"`: zero hits.
- `msearch.py ... grep` with `cohomolog.*induct|induct.*cohomolog`: three hits,
  all group-cohomology induction, a different statement.
- Direct `rg` on Mathlib/AlgebraicGeometry for `induct|smaller|lower.degree`
  found geometric/algebraic induction uses, no matching induction step.
- Direct `rg` on upstream WeilConjectures and this project's lean/Sheaf for
  `of_forall_lt|sk-lem-induction|forall_le_of_forall_le_sub_one` found the
  existing Induction theorem and its consumers. I read the apparent side
  match `RelativeDimensionOneInduction.lean`: it is the cumulative cyclic
  coefficient sibling, with positive n and natural q, not this statement.
- The upstream-name index and repair-note search produced no competing
  binding or repair note for this item. Search receipts are in searches.jsonl.

No mismatch was found, and no mathematical statement, dependency, source
module or proof was changed. Existing reuse is required by H4; H5/H6/H8/H9
introduce no new obligations on source code in this packet because there is
no delivered Lean module. The existing docstring identifies sk-lem-induction,
Stacks Section 59.88, the universal lower-degree input and the contradiction
between the counterexample and vanishing lanes. The complete five-step DAG
proof remains in the node, including affine preparation, transport of the
hypotheses, the universal datum, the vanishing contradiction and the final
universal conclusion. No proof completion is claimed: `sorryAx` remains
reachable from the reused theorem.

Validation: an exact string comparison confirms lean.statement is verbatim
the declaration signature before `:=`; comparing the sandbox node with the
read-only base confirms that only lean changes. I reran the prescribed
scompile.py on scratchpad/CheckExisting.lean: both sandbox and library probes
compiled cleanly (4.9 s and 4.7 s), printed the fully explicit intended type,
and reported the three standard axioms plus sorryAx. No sibling Lean modules
are delivered. Delivery preflight and final result follow below.

Second-reader delivery validation: `deliver2.py Q113 sk-lem-induction
--no-push` printed `OK (dry run)` for commit 543b92d1b8: server preflight and
compilation passed, with only the node and report staged. The final delivery
uses the same statement record and includes this validation note.
