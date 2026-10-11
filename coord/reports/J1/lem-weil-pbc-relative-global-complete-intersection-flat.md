## Worker report

The module `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionFlat` states
`Algebra.flat_of_isRelativeGlobalCompleteIntersection_quotient`, with `sorry` as its
only proof. No definitions, new nodes, or dependency modules are added.

Clause-by-clause correspondence:
- The commutative ring R is `(R : Type u) [CommRing R]`.
- The nonnegative integers n,c are `(n c : ℕ)`; zero is allowed for either.
- The c polynomials in n variables are
  `relations : Fin c → MvPolynomial (Fin n) R`.
- S is exactly `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations)`.
  It is written out in the statement to avoid opaque statement-level `let` binders.
- The relative-global-complete-intersection hypothesis is `h`, using the dependency's
  `Algebra.IsRelativeGlobalCompleteIntersection` on the canonical map R → S. This is
  the recorded ring-map notion: existence of a polynomial presentation with all
  nonempty fibres of the expected dimension, including the guard c ≤ n. The theorem
  does not require the witness to be the displayed presentation; flatness is an
  intrinsic property of the quotient algebra. The displayed presentation with the
  fibre-dimension condition yields this hypothesis using itself as the witness.
- The conclusion that R → S is flat is `RingHom.Flat (algebraMap R S)`.
  `RingHom.Flat` installs the algebra structure induced by that same map and asserts
  `Module.Flat R S`; there is no arbitrary algebra structure or additional hypothesis.

Dependency declarations read in full and used:
- `Sheaf.Paper.RelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection` (definition node
  `def-weil-pbc-relative-global-complete-intersection`).
- `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`, matched by the Mathlib leaf
  `def-weil-pbc-flat-ring-map` (its signature, docstring, and definition were read).

Source checked: local `literature/stacks-project/algebra.tex` is absent on this machine;
opened https://stacks.math.columbia.edu/tag/00SW instead. Its statement says a relative
 global complete intersection is flat; its proof invokes part (2) of 00SV. The module
 docstring includes both DAG proof steps, the quotient-localization isomorphism, the
 flat-over-localization bridge, and the local flatness criterion. The isomorphism in
 the recorded predicate allows transport if its witness uses another presentation.

Edge cases: c=0 allows the empty relation family (polynomial ring); n=0 gives no
variables; n=c=0 includes the coefficient ring. R and S may be zero rings: no
`Nontrivial` hypothesis is imposed. A presentation with c>n may describe zero S;
the recorded predicate requires c≤n only on nonempty fibres, so this case remains
allowed. No Noetherian, field, smoothness, or characteristic hypothesis is imposed.
The quotient has the same universe as R, as any finite polynomial quotient does.

Searches (msearch.py group J1, this item):
- leanfinder: "Relative global complete intersection polynomial quotient with every
  nonempty fibre dimension n minus c is flat". Eight hits, for standard smoothness,
  smooth presentations, and `Algebra.Smooth.flat`; no exact match because smoothness
  adds a Jacobian/smoothness hypothesis.
- loogle: "RingHom.Flat, Algebra.IsRelativeGlobalCompleteIntersection". Zero hits;
  the latter is not known to the Mathlib search service.
- grep Mathlib RingTheory: "CompleteIntersection|complete.intersection|syntomic".
  Only a docstring at Extension/Presentation/Basic.lean:103; no theorem.
- rg of the same concepts in source `WeilConjectures/` and project `lean/Sheaf/`:
  no source hits; project hits include the recorded definition, field-only complete
  intersections, and equation-count flatness which cites this very node in its proof.
  None states this result.
- grep of this item's id in source `WeilConjectures/`: no hits.

No statement correction or disputed mathematical assertion. Server compilation and
preflight dry run are recorded below when complete. The independent second reader
will review the presentation interpretation as well as each binder and the conclusion.

Validation: `scompile.py` compiled the 45-line module cleanly in 1.5 seconds, exit 0.
`deliver2.py --no-push` printed OK: compilation and preflight passed except for the
independent second-reading section, which the tool explicitly reserves for the next
reader. Nothing was pushed.

## Second reading by J1

I opened the item node, both statement-dependency nodes, their recorded modules,
Mathlib's RingHom.Flat and Ideal.Fiber declarations, and both delivery modules.
The local Stacks checkout is absent. I read the source algebra.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
labels definition-relative-global-complete-intersection and
lemma-relative-global-complete-intersection, together with Tags 00SP, 00SW and
00SV. There is no standing Noetherian, field, characteristic or nonzero-ring
hypothesis here: 00SV explicitly passes from Noetherian rings to general rings.

Objects, hypotheses and conclusion, in the order of the node:

1. A commutative ring R: `(R : Type u) [CommRing R]`. Exact; arbitrary u,
   with no Nontrivial or Noetherian instance.
2. Nonnegative integers n and c: `(n c : ℕ)`. Exact, including zero.
3. The c ordered polynomials in n variables:
   `(relations : Fin c → MvPolynomial (Fin n) R)`. Exact; finite indices
   merely replace the source's one-based numbering by zero-based numbering.
4. The quotient S by these equations:
   `MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations)` in the conclusion.
   Exact canonical quotient, with its canonical R-algebra structure. There is no
   additional freely chosen algebra structure and no statement-level let binder.
5. THIS presentation is a relative global complete intersection:
   `(h : IsRelativeGlobalCompleteIntersectionPresentation n c relations)`.
   Exact after repair. The dependency's new predicate unfolds to
   `∀ (p : Ideal R) (_hp : p.IsPrime), ... Nontrivial (p.Fiber S) →
   c ≤ n ∧ topologicalKrullDim (PrimeSpectrum (p.Fiber S)) = (n - c : ℕ)`.
   It uses Mathlib's actual residue-field tensor fibre and spectrum dimension.
   The named prime proof installs exactly the instance needed to form that fibre;
   every prime is quantified, with no choice of a restricted family. The guard
   c ≤ n under the nonempty-fibre implication encodes signed subtraction rather
   than accepting negative expected dimensions as zero.
6. The canonical map R → S is flat:
   `RingHom.Flat (algebraMap R (...))`. Exact, by the recorded flat-ring-map
   dependency: its definition installs the algebra from that very ring homomorphism
   and asserts Module.Flat, without a different map or an extra assumption.

The mismatch was substantive even though the first theorem was mathematically true.
The original h used `IsRelativeGlobalCompleteIntersection (algebraMap R S)`,
which existentially chooses potentially DIFFERENT n,c,relations. For example,
over a nonzero field the presentation k[x]/(x,x) yields k, whose map is intrinsically
complete intersection, but its displayed counts n=1,c=2 cannot satisfy the expected
fibre dimension. The source's specified-presentation convention and the definition
node's first clause require those displayed counts and equations. I changed only
that hypothesis, its import, its recorded Lean signature, and the proof docstring's
sentence allowing transport from another presentation. The node's mathematical
statement, proof and dependencies were already right and remain untouched.

The recorded definition module was insufficient for the specified-presentation
clause. Under brief-stage2 §1(B), I added its dependency module, described below,
and changed only that dependency node's lean record. Its note explains precisely
why the old record could not express this clause. No new DAG notion is introduced.
The imported intrinsic predicate still supplies the definition node's ring-map
clause, and its new presentation predicate supplies the node's first clause.

Edge cases: c=0 gives an empty family and the zero ideal, allowing a polynomial
ring; n=0 gives the coefficient ring modulo the displayed constants; n=c=0 gives
R itself. Empty fibres impose no dimension condition. The zero quotient and zero
base are included; c>n is allowed when the quotient is zero. If a quotient is
nonzero it has a prime whose contraction gives a nonzero residue-field fibre,
so the c≤n guard does not drop any legitimate negative-count case. No restriction
on characteristic is present. The quotient and its residue-field fibres live in
u; no independently small test universe occurs. Universes and variables are bound.
A redundant equation is a useful nonempty-fibre test of the repaired hypothesis.

Independent searches, using different queries from the worker:
- msearch leanfinder: "Flat algebra quotient polynomial equations fibre Krull
  dimension expected dimension": standard smoothness results with extra Jacobian
  conditions, no theorem for this node.
- msearch leanfinder: "Polynomial presentation all nonzero residue field fibres
  have Krull dimension generators minus relations": presentations, smoothness,
  and polynomial Krull dimension results; no specified-presentation predicate.
- msearch loogle: `"CompleteIntersection"`: zero hits.
- msearch leansearch: "Relative complete intersection presentation polynomial
  quotient fibre dimension flat ring homomorphism": service unavailable with
  Internal Server Error; recorded in searches.jsonl, not evidence of absence.
- msearch grep: `syntomic|complete.?intersection` in Mathlib/RingTheory:
  only the Presentation.dimension docstring, no declaration.
- Independent rg over WeilConjectures and lean/Sheaf using syntomic,
  complete-intersection, fibre/flat/dimension and declaration-name patterns:
  no source theorem; the project's field-only predicates are special cases.
  EquationCountFibreDimensionFlat invokes this item and is a local-neighbourhood
  theorem, not a duplicate. EquationCountLocalizeRelativeGlobalCompleteIntersection
  explicitly distinguishes the intrinsic predicate from its inline presentation
  condition; I opened its full signature. That inline conjunct is not a named
  definition and confirms the missing presentation clause. No named presentation
  predicate or exact flatness statement already exists. I also searched the
  upstream name index for the added name and intrinsic name.

H5/H6/H8/H9: the new definition has explicit Prop data and no sorry. The sole
new theorem has only `sorry` as proof. Both module and declaration docstrings
name their source and blueprint id. The statement's two proof paragraphs follow
both DAG steps: 00SV(2) at i=c and quotient localization, then flatness over R_p
and the local map criterion. There is no invented proof or private replacement
of a recorded notion, and no new node or statement correction to review.
Line widths and namespaces follow the contract. The node's lean.statement was
updated verbatim from the repaired signature.

Validation: scompile.py compiled both modules together in dependency order,
exit 0, in 1.6 seconds, with no warnings. No library build was run.

## Dependency modules

`def-weil-pbc-relative-global-complete-intersection`:
`Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation` defines
`Algebra.IsRelativeGlobalCompleteIntersectionPresentation`. It states exactly
this definition node's condition on specified n,c,relations, using the same
Mathlib fibre, spectrum and dimension as the existing intrinsic predicate.
Its import preserves `Algebra.IsRelativeGlobalCompleteIntersection` and avoids
redefining the ring-map notion. The searches above found no named predicate
for the presentation clause. Source 00SP, including its final specified-presentation
convention, supplies this clause; no dependency-node statement or other field
was changed. There are no proof holes in this definition module.
