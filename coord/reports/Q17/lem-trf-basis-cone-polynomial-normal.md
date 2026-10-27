## Worker report

The module `Sheaf.RingTheory.BasisConePolynomialNormal` states
`AddMonoidAlgebra.basisCone_polynomial_normal`. Its only theorem has proof `sorry`.
All seven item helper definitions have real data. It directly imports
`Sheaf.RingTheory.BasisConeAlgebra` and cites its definition-node owner,
`def-trf-basis-cone-algebra`, replacing the rejected theorem citation.
There is no statement correction: all mathematical clauses remain unchanged.

Maintenance commit `a85f586188cfc56b545512b9a62b8bd85c786972` on `sheaf-dag`
has installed the shared definition extraction and the corresponding
localization-module and ownership repair. The three shared definitions retain
exactly their signatures, bodies and public names; the localization theorem
and its proof-plan docstring are unchanged. The localization node now also
cites the definition node as its actual statement dependency.

The active worker packet contains only this item's node and Lean module,
plus this report. The four shared node/module files now belong to the base;
the sandbox keeps their previous copies under adjacent `.maint-Q17-basis-cone-1792853631.bak`
backups. The historical extraction/search/compile notes below describe the
repair that maintenance installed. The prescribed delivery wrapper rebased
the reduced packet onto the updated base. No localization theorem was added
as an unused statement/proof dependency. See
`coord/changes/Q17-basis-cone-definition-ownership.md`.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- The field is `{k : Type u} [Field k]`, using def-weil-field's Mathlib match.
- The arbitrary additive abelian group is `{G : Type v} [AddCommGroup G]`.
  Independent universes `u v` do not restrict either carrier.
- The finite integral basis is `{r : ℕ}` and
  `b : Module.Basis (Fin r) ℤ G`. `Module.Basis.repr` is precisely the unique
  integral-coordinate isomorphism. The usual integer module on an additive
  commutative group is inferred; no extra module hypothesis is imposed.
- `H` is the existing `AddMonoidAlgebra.basisCone b`, the additive-submonoid
  closure of the basis vectors. This is exactly the set of finite nonnegative
  combinations. `basisConeExponent b a` constructs their sum with its membership
  proof from `AddSubmonoid.sum_mem` and `AddSubmonoid.nsmul_mem`.
- `k[T]` uses Mathlib `AddMonoidAlgebra k T`, whose `coeff : T →₀ k`
  gives the direct sum and whose multiplication is convolution.
- The node explicitly regards `C` as a subalgebra of `k[G]`. Accordingly,
  `basisConeSupportedAlgebra b` is the range of the existing extension-by-zero
  algebra homomorphism `basisConeInclusion b`. The theorem's first clause
  identifies this range with precisely the coefficient lists vanishing outside
  `basisCone b`: `∀ g, g ∉ basisCone b → f.coeff g = 0`.
- `basisConePolynomialRing k 0` is literally `k`, and its successor is literally
  `Polynomial (basisConePolynomialRing k n)`. This is the requested one-variable
  tower, not a replacement by a multivariate ring. `CommAlgCat` merely bundles
  its canonical ring and coefficient-algebra structures to permit recursive
  construction; the carriers are those exact polynomial rings.
- `basisConePolynomialVariable k r i` gives the variables: at each successor
  the last variable is `Polynomial.X`, with previous variables embedded by
  `Polynomial.C` using `Fin.lastCases`.
- `basisConePolynomialEval` recursively uses `Algebra.ofId` at zero and
  `Polynomial.aevalTower` at successors. `basisConePolynomialEvaluation b`
  evaluates those variables at the basis monomials, inside the specified C.
- The existential `φ : Bᵣ ≃ₐ[k] C`, together with
  `φ.toAlgHom = basisConePolynomialEvaluation b`, states that this actual
  evaluation homomorphism is an algebra isomorphism. Fixing k and k-linearity
  are supplied by `≃ₐ[k]`; the next clause records each variable's image.
- For every `a : Fin r → ℕ` and `c : k`, the inverse clause says
  `φ.symm (basisConeSupportedMonomial b (basisConeExponent b a) c) =
  c • ∏ i, basisConePolynomialVariable k r i ^ a i`.
  Thus it includes the node's inverse formula at `c = 1`, and expresses its
  k-linear extension on all scaled basis vectors. Its extension to finite sums
  is already part of the algebra-equivalence structure.
- The last four conjuncts are `IsDomain Bᵣ`, `IsIntegrallyClosed Bᵣ`,
  `IsDomain C`, `IsIntegrallyClosed C`, exactly the recorded normal-domain
  rendering of def-weil-pbc-normal-ring.
- No positivity hypothesis on r is imposed. At r = 0, the recursive tower is k,
  the tuple and product are empty, and an empty integral basis forces G and H
  to be zero. The inverse expression is `c • 1`, the requested identification
  of the constant monomial with c. Equality C = k in the prose is the canonical
  algebra identification, since C is concretely a subtype of the group algebra.

Declarations and signatures read in the dependency sources:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, class extending
  `CommRing` and `DivisionRing` (lines 168–180).
- def-weil-polynomial-ring: `Polynomial`, Mathlib.Algebra.Polynomial.Basic,
  structure with `toFinsupp : AddMonoidAlgebra R ℕ` (lines 65–77).
- def-weil-pbc-normal-ring: `IsIntegrallyClosed`,
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed, the abbreviation for
  integral closedness in `FractionRing R` (lines 60–74). Its domain rendering
  is the mandated conjunction with `IsDomain`.
- New definition dependency: `basisCone`, `basisConeVariable`,
  `basisConeInclusion`, now in Sheaf.RingTheory.BasisConeAlgebra. Their complete
  signatures and bodies are unchanged from the returned head's imported module.
  The new definition node owns these definitions explicitly. It depends only on
  def-weil-field; it does not depend on either theorem, so there is no cycle.
- Repaired dependency module: Sheaf.RingTheory.BasisConeGroupLocalization keeps
  `basisConeDenominators`, `basisConeDenominator`, and
  `basisCone_group_localization`. Its theorem signature and proof docstring are
  unchanged. It publicly imports BasisConeAlgebra, preserving the public API for
  all existing consumers. Its node changes only in `lean`, as directed by the
  return under §1(B); the node's statement and dependency fields are untouched.
- Proof import: Mathlib.RingTheory.Polynomial.IsIntegral, the Stacks 030A
  instance `instIsIntegrallyClosedPolynomialOfIsDomain` at lines 179–181,
  as recorded by lem-weil-pbc-polynomial-ring-normal-domain.
- Other constructions: `Module.Basis` (LinearAlgebra.Basis.Defs:85–97),
  `Polynomial.aevalTower` (Algebra.Polynomial.AlgebraMap:540–565),
  `CommAlgCat` and `CommAlgCat.of` (Algebra.Category.CommAlgCat.Basic:27–60),
  `AlgHom.rangeRestrict` (Algebra.Algebra.Subalgebra.Basic:587 onward).

The source was read with `pdftotext -f 110 -l 111` on the ILO PDF, giving
printed pp.104–105: the identification of k[P^gp] with k[Z^n] and the conclusion
that an integral basis freely generates the positive monoid. The explicit
polynomial identification here follows the node's honestly agent-written
five-step proof. Read Stacks algebra.tex, lemma-polynomial-domain-normal,
lines 8130–8150, for the normality step. The module docstring carries the
five-step proof, including the finite-support convolution calculation,
inverse formula, polynomial-normality induction, and fraction-field argument.

Edge cases checked mathematically: r = 0 as above; r = 1 with G = ℤ and either
choice of integral generator; r = 2 with a nonstandard basis (1,1),(0,1),
whose nonnegative sums are (a,a+b); arbitrary positive characteristic;
zero coefficients and the zero polynomial; empty products; and negative
coordinates in G, whose coefficients must vanish in C. The trivial ring is
correctly excluded by Field. No bound or characteristic condition was added.

Searches actually run using the prescribed msearch wrapper:

- leanfinder: “The monoid algebra of the positive cone of a finite integral
  basis is isomorphic to an iterated polynomial ring, with inverse on
  monomials, and is a normal domain.” Eight hits included integral-closure
  automorphism finiteness, class-group finiteness, NumberField.integralBasis
  and related facts; no exact match.
- loogle: `AddMonoidAlgebra, MvPolynomial`. Twelve hits, chiefly
  MvPolynomial support/scalar formulas and empty/sum equivalences; no exact
  match for the concrete cone, literal tower, evaluation/inverse and normality.
- grep: `IteratedPolynomial|iteratedPolynomial|finSuccEquiv|toFinsuppIsoAlg`
  in Algebra. Eighteen hits include `MvPolynomial.finSuccEquiv` and
  `Polynomial.toFinsuppIsoAlg`; these are ingredients, not the statement.
- leansearch: “An iterated polynomial ring over a field is isomorphic to the
  monoid algebra on the positive cone of an integral basis.” Eight hits include
  `MvPolynomial.sumRingEquiv`, `MvPolynomial.sumAlgEquiv`,
  `Polynomial.toFinsuppIsoAlg`, AddMonoidAlgebra.ring, and
  MonoidAlgebra.symm_commAlgEquiv; no exact statement.
- Direct rg searches of lean/WeilConjectures and lean/Sheaf for basisCone,
  basis_cone, iteratedPolynomial, IteratedPolynomial and positiveCone found
  the existing BasisConeGroupLocalization definitions, which are reused.
  `grep -rn` for this item id in lean/WeilConjectures found no attachment.
  A final rg for every proposed declaration name in Mathlib/Algebra,
  lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no
  collisions. No unavailable service result was treated as a negative match.

Original-head compilation: scompile.py compiled both its sandbox probe and the actual module
against the live server library cleanly, in 1.5 seconds each. The first attempt
exposed the need to carry recursive polynomial typeclass data, repaired by the
literal CommAlgCat tower; it also caught the current AddMonoidAlgebra.coeff API
and a required noncomputable marker. No statement was weakened in that repair.

## Second reading by Q17

Re-read the final node and module clause by clause in a separate pass. The
basis is over ℤ rather than k; the cone is the closure of the chosen basis,
not an arbitrary monoid; C is a concrete subalgebra of k[G]; and the first
conjunct pins it down by support. The polynomial tower appends its variable
at Fin.last, so the Fin.castSucc old-coordinate evaluation matches
Fin.lastCases in the variable definition. The algebra equivalence is tied to
the constructed evaluation, not an arbitrary existence assertion. The inverse
formula includes every nonnegative tuple and every coefficient, with linearity
and multiplicativity supplied by the equivalence. Normality is asserted on
both exact carriers. No rank-zero, field-characteristic or universe restriction
was introduced. The proof-only Stacks instance is a plain import, and the
statement imports are public in module mode. This is the worker's second
pass; independent maintainer review remains required by the dispatch brief.


## Repair of return 5263e2f46f2

H2 was the sole return point. L found that the item cited a theorem node only
for definitions living in its module, with no definition node owning them.
This repair creates `def-trf-basis-cone-algebra` with its own module and gives
it ownership of `basisCone`, `basisConeVariable`, `basisConeInclusion`. The
three declaration names, signatures and bodies are preserved; only their
module ownership and blueprint docstring tags change. The group-localization
module removes its copies and publicly imports the definition module.
The polynomial-normality module now imports the definition module directly;
its theorem and all helper bodies remain exactly as at the returned head.

The item node was rebased by reading the current shared main node and carrying
over only its Lean record plus the added definition dependency. Thus the
rejected theorem citation is absent. The group-localization dependency node
was copied from current main and changes only `lean` (including an explanation
of the ownership repair in `lean.note`). The report records the changed
ownership rather than claiming that citing the theorem for definitions is
acceptable. Comparison uses file reads; all compilation and delivery bookkeeping
uses the authorized wrappers.

## New nodes

`def-trf-basis-cone-algebra` defines the nonnegative cone of an integral basis,
the basis monomials in its additive monoid algebra, and the coefficientwise
inclusion into the group algebra. Source: ILO VIII 3.2.12, printed pp.104–105,
re-read using pdftotext, and the explicit positive-basis specialization in the
DAG. This is an ownership extraction of existing definitions, as requested by
the maintainer, with no parallel copy. `basisCone` uses additive-submonoid
closure of the chosen ℤ-basis; `basisConeVariable` is the coefficient-one
single monomial at each basis vector, with its closure-membership proof;
`basisConeInclusion` is `mapDomainAlgHom k k (basisCone b).subtype`. Thus each
clause of the new node has actual data and it introduces no postponed theorem.
Field, group, finite basis and independent carrier universes are as in the
item. At rank zero the family is empty and the cone is the zero monoid;
positive characteristic, arbitrary rank, and nonstandard bases remain included.

Searches actually run for this extraction and recorded in its mathlib_searches:
LeanSearch for “Define the nonnegative cone generated by an integral basis,
its monoid algebra, the basis monomials, and its inclusion into the group
algebra.” returned MonoidAlgebra, symmetricAlgebra basis, ordered group/ring
cones, powerBasisAux, representation basis, AddMonoidAlgebra.of' and module
freeness. LeanFinder for “The additive submonoid generated by a finite integer
basis and the inclusion of its monoid algebra into the group algebra.” returned
finite-adjoin/support facts, integer-cast facts, NumberField integral-basis
span and AddMonoidAlgebra.of'. The prescribed Mathlib grep
`basisCone|basis_cone|mapDomainAlgHom` in Algebra/MonoidAlgebra found five
mapDomainAlgHom ingredient occurrences. The general Mathlib constructor is
used directly in the extracted inclusion. Direct rg of dag/nodes,
lean/WeilConjectures and lean/Sheaf found the current definitions only in the
group-localization module, and no definition-node owner. blueprint_refs search
“basis cone” returned zero matches, and ancestor identifies
lem-trf-local-term-locality, used in blueprint.from. The search logs, including
actual names and digests, are embedded verbatim in the new node's records.

## Dependency modules

`lem-trf-basis-cone-group-localization`: its former `lean.declarations` mixed
three shared definitions with the theorem and its two denominator helpers.
This was unusable as the definition-node dependency the consumer needed (H2).
The module now publicly imports BasisConeAlgebra and retains the denominator
helpers and localization theorem unchanged, including its entire signature,
all clauses, sorry proof and six-step natural-language proof docstring.
The replacement `lean.declarations` lists only these three retained declarations.
The module still states exactly the dependency node's localization assertion;
its node has no mathematical statement or dependency-field changes.

Repair second pass: checked the three moved declaration bodies against the
current original module, checked the remaining localization theorem text and
helpers unchanged, and checked the item statement byte-for-byte against the
returned version except for its public import. Only one module now declares
each shared definition. Independent maintainer review is still the independent
second reading; no other agent was started.

Repair validation: scompile.py compiled all three modules separately in dependency
order, with no errors or non-sorry warnings. The shared definition module was
checked as a private overlay, a preliminary library module, and a sandbox module;
both consumer modules then compiled in sandbox and library mode. A long slot
wait was included in the wrapper's elapsed time for the definition module;
the subsequent individual compiles completed in 2.9–7.2 seconds. The direct
comparison confirmed all three extracted declaration bodies unchanged, both
denominator definitions unchanged, the full localization theorem and its
proof docstring unchanged, and exactly `lean` changed on the dependency node.


## Historical delivery-tool refusal (resolved by maintenance)

The prescribed dry run repeatedly compiles all three modules successfully, but
then rejects the requested §1(B) repair of BasisConeGroupLocalization because
its node is outside this item's statement/proof prerequisite closure. That
classification excludes its lean.file ownership, producing the fatal error:
“no node of the delivery has it as lean.file”. The independent return explicitly
requires this module repair. Adding the localization theorem as an unused
statement or proof dependency would misrepresent the mathematics; no such
addition is retained. The maintainer must permit this explicitly requested
ownership extraction in preflight. Launcher and project tools were not edited,
and no failed packet was pushed.


The refusal above is historical. Maintenance installed the shared extraction
on the base, so the item no longer needs to modify the unrelated localization
node in its delivery. The normal dry run must now be checked against the
updated base before delivery. No launcher, preflight, review or landing tool
was edited. The remaining theorem retains its usual independent review.

## Final validation

The reduced packet passed `deliver2.py Q17 lem-trf-basis-cone-polynomial-normal
--no-push`: server compilation and preflight both succeeded, staging exactly
the item module, item node and this report. The ownership extraction is supplied
by maintenance commit `a85f586188cfc56b545512b9a62b8bd85c786972` in the base.
