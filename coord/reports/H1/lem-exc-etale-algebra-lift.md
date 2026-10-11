## Worker report

The module `Sheaf.RingTheory.EtaleAlgebraLift` states the two parts of
`lem-exc-etale-algebra-lift`; both proofs are `sorry`, and no new definitions are needed.
The node copy changes only `lean`.

Hypotheses and clauses:

- The arbitrary commutative ring and ideal are `{A : Type u} [CommRing A] (I : Ideal A)`.
  No nilpotence, properness, nonzero-ring, field, characteristic or Noetherian assumption
  is imposed.
- The specified quotient algebra is `{B : Type v} [CommRing B] [Algebra (A ⧸ I) B]`.
  Its specified square Jacobian presentation is `P : SquareJacobianPresentation
  (A ⧸ I) B (Fin m)`; the chosen coefficientwise lifts are
  `L : SquareJacobianPresentation.CoefficientLift I P`. These are exactly the data of
  `def-exc-etale-algebra-lift`, including its `map_relation` constraint.
- “The algebra ... is étale of finite presentation over A” becomes
  `Etale A L.LiftRing ∧ FinitePresentation A L.LiftRing`, using the algebra structure
  of the actual polynomial quotient, not an arbitrary structure on another carrier.
- The extended ideal `IBᶫⁱᶠᵗ` is `I.map (algebraMap A L.LiftRing)`.
  The specified reduction is an isomorphism precisely when there exists a ring equivalence
  `e : (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B` whose composite with the
  quotient map equals `L.reduction` at every `x : L.LiftRing`. The equality fixes the map,
  rather than merely asserting an unrelated isomorphism of the two rings. It also fixes
  its scalar compatibility: the existing reduction sends each scalar to
  `algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a)`. Thus the equivalence is the specified
  `A/I`-algebra isomorphism; there is no loss from spelling it with a ring equivalence
  and the commuting equation rather than introducing a second quotient-algebra structure.
- “Hence every étale finite-presentation A/I-algebra has such a lift” is the second theorem,
  `Algebra.exists_etale_coefficientLift`, for arbitrary `B : Type v` with
  `[Etale (A ⧸ I) B]`. Mathlib's `Etale` already includes `FinitePresentation`, so this
  binder includes exactly both conditions, without a redundant hypothesis. Its conclusion
  supplies `m`, `P`, `L`, and the same étaleness, finite presentation and specified reduction
  equivalence as the first theorem. Finite indexing by `Fin m` covers every finite
  presentation after reindexing and does not restrict the statement.

Dependency declarations used:

- `Sheaf.RingTheory.JacobianPresentationLift`:
  `Algebra.SquareJacobianPresentation.CoefficientLift`,
  `Algebra.SquareJacobianPresentation.CoefficientLift.LiftRing`,
  `Algebra.SquareJacobianPresentation.CoefficientLift.reduction`.
  Read the full module, including the explicit generators of `liftIdeal`, the determinant,
  the coefficientwise reduction constraint, and the inverse-Jacobian image of `t`.
- `def-weil-pbc-scheme-conventions` is a convention-only record, with no declaration or
  module of its own. This item concerns rings; as the standing stage-2 convention permits,
  `Algebra.Etale` is used directly. No scheme notions or private duplicates are introduced.
- `Mathlib.RingTheory.Etale.Basic`: `Algebra.Etale`, whose field
  `finitePresentation : FinitePresentation R A` was read. `Ideal.map`, `Ideal.Quotient.mk`
  and `RingEquiv` are Mathlib's existing notions. The proof-only Jacobian criterion was
  read in `WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree` and is named
  in the proof docstrings; it is not imported because the statements do not use it.

Source and proof: opened https://stacks.math.columbia.edu/tag/04D1 (Lemma 10.143.10).
It allows an arbitrary ideal and uses exactly coefficient lifts and adjoining the inverse
Jacobian. The blueprint markdown and local Stacks checkout are absent on this machine;
the node's full statement and three proof steps were read, together with the primary
Stacks source. The docstrings give each step: determinant `Δ²`, invertibility via `tΔ=1`,
Jacobian criterion, reduction and elimination of `t`, and existence of a presentation and
coefficient lifts. No statement correction or disputed clause was found.

Edge cases checked: `m = 0` is allowed (empty determinant equals one, and the added relation
is `t - 1`); `I = ⊥`, `I = ⊤`, and zero rings are all permitted; neither a nontrivial ring
nor a proper ideal is assumed. All characteristics are covered. `A : Type u` and
`B : Type v` have explicitly bound independent universes, and the constructed lift lives
in `Type u`, as the dependency defines it. The quotient equivalence may relate carriers
in different universes, so no universe or smallness restriction is placed on `B`.

Searches for existing statements (2026-10-11):

- `msearch.py leanfinder`, query “An etale finitely presented algebra over a quotient A/I
  lifts to an etale A algebra with reduction isomorphism”: eight hits, including
  `Algebra.Etale.finitePresentation`, `StandardEtalePair.lift`, and square-zero lifting
  for `StandardEtalePair`; none states this arbitrary square-Jacobian construction.
- `msearch.py loogle`, query `Algebra.Etale, Ideal.Quotient, Function.Bijective`: zero hits,
  unknown identifier `Ideal.Quotient`.
- `msearch.py grep`, query `etale.*lift|lift.*etale` in `RingTheory`: seven hits, all
  unrelated or standard-étale/formal-lifting APIs.
- `msearch.py leansearch`, query “Etale algebras lift along arbitrary quotient maps with
  the specified reduction isomorphism”: service unavailable, Internal Server Error; no verdict.
- Direct `rg` in the project's `lean/Sheaf/RingTheory` and source's
  `WeilConjectures/Mathlib/RingTheory` for quotient/lift/étale patterns: no identical
  statement. The source `WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale` does
  lift *standard* étale algebras, a more restrictive hypothesis and a different construction;
  its full relevant statement and docstring were read. It does not realize this node.
- Direct `rg` for `lem-exc-etale-algebra-lift` in `WeilConjectures`: no hits.
  Direct `rg` for the proposed declaration names in Mathlib, `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collisions before writing.

Validation: `scompile.py H1 lem-exc-etale-algebra-lift` compiled the 76-line module on the
server in 1.7 seconds, exit code 0, with no warnings or errors. The dry run follows.

## Second reading by H1

I independently read the item node, its three proof steps, the Lean file, both statement
 dependency records, and the complete JacobianPresentationLift module. I also read the
SquareJacobianPresentation source declaration and its inherited Presentation and
SubmersivePresentation fields, Mathlib's Etale class, and the square-Jacobian criterion.
The local literature checkout contains no Stacks TeX. I therefore read the primary source
at https://stacks.math.columbia.edu/tag/04D1 and fetched the actual algebra.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex, reading
lemma-lift-etale and its proof. Its assumptions are an arbitrary commutative ring, an
arbitrary ideal, and an etale quotient algebra; neither nilpotence nor properness nor
Noetherianness is required. The construction is exactly the node's construction.

Object/hypothesis/conclusion checklist (each verdict is PASS):

1. Base ring A: `{A : Type u} [CommRing A]`. This is the source's arbitrary ring;
   no field, domain, characteristic, finiteness or nontriviality hypothesis is added.
2. Ideal I in A: `(I : Ideal A)`. No nilpotence, properness or maximality hypothesis.
3. Specified quotient algebra B-bar: `{B : Type v} [CommRing B]
   [Algebra (A ⧸ I) B]`. Its scalar action is the specified A/I-algebra action.
4. Specified finite square presentation: `{m : ℕ}` and
   `P : SquareJacobianPresentation (A ⧸ I) B (Fin m)`. The inherited generators are
   surjective, the relations span their kernel, the variable/relation pairing is the
   identity, and the full Jacobian image is a unit. Thus this is the specified quotient
   presentation, not just a list of equations. Fin m expresses every finite list.
5. Chosen coefficient lifts: `L : SquareJacobianPresentation.CoefficientLift I P`.
   I read its `relation` and `map_relation` fields: coefficient reduction recovers exactly
   the specified relations, imposing no condition beyond the node's choice of lifts.
6. Constructed lift: `L.LiftRing`, the dependency's actual polynomial quotient over A,
   with variables `Option (Fin m)` (none is t), ideal generated by the lifted relations
   and `t * Delta - 1`, and Delta the lifted partial-derivative determinant. The inherited
   quotient algebra structure is the required A-action. No private lift is introduced.
7. Etaleness and finite presentation over A: `Etale A L.LiftRing ∧
   FinitePresentation A L.LiftRing`. Both clauses are present for every chosen L.
8. Extended ideal: `I.map (algebraMap A L.LiftRing)` is precisely I times the lift.
9. Specified reduction is an isomorphism: the existential `e :
   (L.LiftRing ⧸ I.map (algebraMap A L.LiftRing)) ≃+* B` followed by
   `∀ x, e (Ideal.Quotient.mk ... x) = L.reduction x` fixes the reduction on every
   quotient representative. It is not merely an unrelated isomorphism. Unfolding
   polynomialReduction shows each scalar a goes to
   `algebraMap (A ⧸ I) B (Ideal.Quotient.mk I a)`; hence the commuting equation forces
   e to commute with the canonical A/I-action. The RingEquiv formulation is exactly
   the specified A/I-algebra isomorphism and adds no stronger conclusion.
10. Every etale finite-presentation quotient algebra has such a lift: the second theorem
    binds arbitrary `(B : Type v)` with `[Etale (A ⧸ I) B]`, then existentially supplies
    m, P, L, and the preceding three conclusion clauses in that order. Etale's
    `finitePresentation` field supplies precisely the source's finiteness condition.
    Existence of P and L is justified by the node's final proof step and the source's
    construction; the conclusion does not demand a predetermined presentation.
11. Convention dependency: def-weil-pbc-scheme-conventions explicitly defines no notion
    of its own. No scheme is introduced by this ring statement; Mathlib's Etale and
    FinitePresentation express the affine ring properties directly.

Edge cases: m = 0 is allowed, the determinant of the empty matrix is 1, and the extra
relation becomes t - 1. I = bottom and I = top are allowed. With I = top, B is necessarily
a zero ring as an A/I-algebra, but the lift need not be zero; the statement does not
incorrectly impose that. The zero base ring and zero quotient algebra are covered
(SubmersivePresentation even provides zero-ring presentations). No nonempty indexing,
nontriviality, positive m, or characteristic condition occurs. Independent universes
u and v cover arbitrary base and target carriers; LiftRing lives in Type u and a
cross-universe RingEquiv is allowed. No test-object universe makes a hypothesis vacuous.
All variables and universes in both statements are explicitly bound.

Independent searches, using different wording from the worker:

- LeanFinder via msearch: "An etale algebra over a residue quotient admits an etale
  algebra over the original ring whose base change is the given algebra". Eight hits:
  residue-field factorization, IsEtaleAt.comp, standard-etale ring instances,
  RingHom.Etale.toAlgebra, etale_algebraMap, and Etale.comp; no exact lifting statement.
- Loogle via msearch: `"Etale", "quotient"`. Six hits: separability of field quotients,
  square-zero standard-etale HasMap lifting, and four standard-etale polynomial/localized
  quotient equivalences. None handles arbitrary square presentations and ideals.
- LeanSearch via msearch: "An etale algebra over a quotient ring can be lifted to an
  etale algebra over the ring without nilpotence of the ideal". The service returned
  Internal Server Error; this is recorded as unavailable, with no search verdict.
- Direct rg over Mathlib's Etale sources, source WeilConjectures/Mathlib/RingTheory,
  and project lean/Sheaf/RingTheory for `etale.*quotient|quotient.*etale|lift.*etale|
  etale.*lift`, and the two proposed declaration names across the full project/source
  and dag/lean_names_upstream.json. No identical statement or name collision.
  I opened IsStandardEtale.exists_algEquiv_quotient_tensor and its surrounding source:
  it assumes IsStandardEtale, a monic univariate presentation, and constructs a
  tensor-product lift; it does not replace either statement of this node. Project
  henselian root/factorization lifts also have different hypotheses and conclusions.

No new definition node or dependency module is delivered; the existing dependency is
usable exactly as recorded. No statement correction was made, so correction/citer
checks do not apply. The statements carry all three natural-language proof steps:
Delta squared and the Jacobian criterion, reduction and elimination of t, then choosing
presentations and coefficient lifts. Both theorem proofs remain sorry. There is no new
definition, hollow data, file-local notation, local instance, or private notion. The
module uses both imports, follows the namespace/header/source/blueprint conventions,
and the node's lean.statement matches the main signature verbatim after whitespace
normalization. I found no mismatch and changed no Lean or node field; the only addition
is this independently written second-reading report. Compilation and delivery preflight
are run after this reading.
