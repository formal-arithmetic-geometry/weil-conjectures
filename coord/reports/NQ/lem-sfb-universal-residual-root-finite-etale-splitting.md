## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalResidualRootSplitting` states the entire
node as `AlgebraicGeometry.UniversalResidualRoot.finiteEtale_splitting`, with proof
`sorry`. All four helper constructions have real data. They give the extended ideal,
the residual quotient, its root ideal, and the disjoint union over a finite set.
There are no postponed helper theorems and no new notions requiring definition nodes.
The existing root quotient is reused; its polynomial coordinates are written inline as
`Ideal.Quotient.mk _ (MvPolynomial.X i)`, without an additional coordinate definition.

Hypothesis and clause correspondence:

- A nonempty connected affine scheme is `(S : Scheme.{u}) [IsAffine S]
  [ConnectedSpace S]`. ConnectedSpace includes nonemptiness.
- The geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)`.
- The pointed-cover limit is the dependency's actual
  `Scheme.UniversalCover.cover s`. The identification
  `eT : Spec (.of R) ≅ Scheme.UniversalCover.cover s` presents its coordinate
  ring R without choosing a new limit. The dependency's cofinality clause identifies
  this with every small cofinal pointed system in the node. No new fundamental
  group model or extra Galois-action hypothesis is needed here.
- Arbitrary commutative rings are `(R H : Type u) [CommRing R] [CommRing H]`.
  The common compatible size convention is the one used by the pointed-limit node;
  the theorem is universe polymorphic. Finite-set indices are in this same universe,
  with `ULift.{u} (Fin m)` in the existence assertions.
- The parameter tuple, including the empty tuple, is `(r : ℕ) (t : Fin r → H)`;
  J is `Ideal.span (Set.range t)`. Henselianity is precisely
  `[HenselianRing H (Ideal.span (Set.range t))]`, the recorded dependency convention.
  The fixed residue identification is `eR : (H ⧸ Ideal.span (Set.range t)) ≃+* R`.
- A positive integer exponent is `(n : ℕ) (hn : 0 < n)`; this parametrizes exactly
  the positive integers, with no prime-to-characteristic restriction.
- H_n is the existing `Algebra.pthRootAlgebra n r H t`. Its definition accepts every
  natural exponent despite its name. It is literally the multivariate quotient
  H[X_i]/(X_i^n-t_i). The inline expression `Ideal.Quotient.mk _ (MvPolynomial.X i)` is the
  class of X_i.
- `extendedIdeal t n` is J mapped along the algebra map H → H_n, and
  `residual t n` is literally H_n modulo that ideal. `rootIdeal t n` is the span
  of the quotient images of those polynomial variables.
- The first universal quantifier ranges over ALL objects of
  `(@IsFinite ⊓ @Etale).Over ⊤ (Spec (.of R))`. Its splitting is an isomorphism
  in `Over (Spec R)` with `copies (Spec R) (ULift (Fin m))`. There is no requirement
  that E be presented as a pullback of a scheme over S.
- The displayed monomial basis is an existential
  `Module.Basis (Fin r → Fin n) H (pthRootAlgebra n r H t)`, together with the
  exact formula `b a = ∏ i, (Ideal.Quotient.mk _ (MvPolynomial.X i)) ^ (a i).val`.
  This is finite freeness with precisely the asserted basis and rank n^r.
- The next two conjuncts are `HenselianRing H_n (extendedIdeal t n)` and
  `HenselianRing C_n (rootIdeal t n)`. The following equality is exactly
  `rootIdeal t n ^ (r * (n - 1) + 1) = ⊥`.
- `eC : residual t n ≃+* pthRootAlgebra n r R (fun _ ↦ 0)` gives the asserted
  truncated polynomial presentation of C_n. Its formulas prescribe the coefficient
  map via eR and the image of each variable, making this the specified presentation.
- `eD : (residual t n ⧸ rootIdeal t n) ≃+* R` gives C_n/K_n = R; its coefficient
  formula fixes the identification to eR. Roots are already killed in its source.
  Thus eD is determined by this formula, not an unconstrained comparison map.
- The second finite-cover quantifier gives the splitting of every finite étale
  E over Spec H_n, as an isomorphism over that very base.
- Finally A is ANY `Type u` with `[Finite A]`, including the empty set. `αR` is any
  specified isomorphism after the successive base changes H_n → C_n → R. The first
  `∃! αC` lifts it over C_n; the subsequent universal quantifier covers every αC
  reducing to αR and gives `∃! αH` reducing to αC. Both equalities use
  `(Over.pullback ...).mapIso`. Equality of isomorphisms includes the hom and inverse,
  so this explicitly retains lifting of the inverse as well.
  The trivial object after base change is written as the base change of `copies`
  upstairs. The canonical pullback/coproduct isomorphism identifies it with copies
  of the new base; likewise the nested pullback is canonically E ×_(H_n) R.
  This avoids any arbitrary identification of two chosen pullbacks. It is the same
  collection of all specified residual splittings.

Dependencies used:

- `lem-sfb-pointed-finite-etale-limit-cover`: public import
  `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`; the recorded
  `PointedLimitCechCoordinates` / `nonempty_pointedLimitCechCoordinates` package
  supplies cofinality, connectedness and finite-stage splitting. Its actual
  `cover`, `diagram`, `proj` are in the public upstream import
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction`.
  I read the full declaration and docstring of the package and the cover construction.
- `def-weil-pbc-henselian-terminology`: public import
  `WeilConjectures.Mathlib.RingTheory.Henselian`, using the recorded `HenselianRing`
  (Mathlib's Jacobson-radical and simple-root form, equivalent to the node's
  finite-algebra idempotent form). Its declaration and the upstream terminology
  docstring were read; no strict henselianity or locality is assumed.
- `def-weil-pbc-finite-etale-category`: the recorded Mathlib specialization
  `MorphismProperty.Over` of `@IsFinite ⊓ @Etale`, with morphism property ⊤.
  Its full signature and docstring and `MorphismProperty.Over.pullback` were read.
  The isomorphisms may be written in ordinary Over since the inclusion is full.
- `def-sfb-parameter-root-algebra` is the landed definition node owning
  `Algebra.pthRootAlgebra`, recorded existing:true in
  `WeilConjectures.RingTheory.PthRootAlgebraLocal`. It defines precisely the
  simultaneous polynomial quotient over arbitrary commutative rings and exponents.
  The old theorem-only dependencies `lem-weil-pbc-pth-root-algebra-local` and
  `lem-sfb-henselian-parameter-root-regularity` have been removed. The latter's
  module import has also been removed: each coordinate now appears inline as the
  quotient image of `MvPolynomial.X i`. Neither theorem conclusion is used.
- Every recorded non-Mathlib proof dependency is imported privately, including
  finite-data descent, descent of finiteness, the clopen graph, integral henselian
  extension, full faithfulness, open subgroups and the fibre equivalence. The
  Mathlib proof dependencies are available through the explicit private proof
  imports or the public statement imports. The theorem docstring gives all six
  proof steps and names the corresponding nodes.

Sources read: local Stacks `pione.tex`, lemma-gabber (09ZS), and
`more-algebra.tex`, lemma-integral-over-henselian-pair (09XK); the supplied node's
six-step agent assembly, with its descent, graph and nilpotent-root details.
The requested CompactObject example has been withdrawn to an empty module; its
node now records the upstream declaration. The delivery follows the current
module-mode and docstring conventions directly.

Edge cases checked before writing: r=0 gives the empty-product basis {1}, K=0,
and exponent r(n-1)+1=1; n=1 gives evaluation at the parameters and K=0; A empty
is admitted by `[Finite A]`, without `[Nonempty A]`, and the empty coproduct is
retained. Neither H nor R nor H_n is assumed Noetherian or local. No exponent is
assumed invertible and no primitive roots of unity are required. The zero-ring
case is not accidentally asserted as a universal-cover presentation: Spec R must
be the nonempty connected pointed limit, so the original hypotheses themselves
exclude it. Nilpotents and nonlocal henselian pairs remain allowed.

Searches (2026-10-22):

- msearch LeanFinder: "Finite etale covers of a henselian ring with simply connected
  residue split uniquely over nilpotent parameter root algebras". Eight hits were
  standard-étale square-zero lifting, local Hensel results and field decomposition;
  none states this result.
- msearch LeanSearch: "Every finite etale cover over a henselian pair with universal
  finite etale residue cover is a finite disjoint union of copies of the base".
  Eight hits, including étale field product decompositions and Scheme.Etale; no match.
- msearch Loogle: `HenselianRing, MvPolynomial, Ideal.Quotient` returned no match;
  `HenselianRing` returned its definition and local/complete instances. None gives
  universal-residue root splitting.
- msearch grep: `MvPolynomial.*(X|Quotient)|span.*range` in RingTheory/Polynomial
  found the ordinary quotient and universal factorization APIs, not this theorem.
- rg of `rootAlgebra|RootAlgebra|[Kk]ummer.*[Aa]lgebra|[Rr]oot.*[Qq]uotient`
  in the upstream and Sheaf sources located `pthRootAlgebra` and the two existing
  coordinate interfaces. Targeted rg `rootAlgebra|parameterRoot|ParameterRoot|rootStage|RootStage`
  in their RingTheory and AlgebraicGeometry trees found the reusable coordinate.
- rg for this item's exact id in upstream found no declaration. DAG searches for
  `root algebra`, `root algebras`, and root presentations found the existing root
  nodes above. `tools/blueprint_refs.py search 'parameter root'` returned no blueprint
  title match. There is no second root quotient in this delivery.

No statement correction, dependency repair, or STATEMENT-DISPUTED finding was needed.
Validation: scompile.py compiled the entire module in both sandbox and real module
modes without errors or warnings. The first probe caught the finite index universe;
using ULift for Fin m repaired it while retaining empty sets and arbitrary finite sets.

## Second reading by NQ

This is the dispatcher's worker self-audit, not a claim of independent review;
the brief reserves independent review for the maintainer and forbids spawning agents.
I reread the node and final file together. The first cover quantifier is over R,
not just covers descending from S. The basis uses all r coordinates and bounded
exponents, including the unique empty exponent vector. Both henselian pairs and
the precise nilpotence exponent occur separately. eC fixes both coefficients and
generators; eD fixes coefficients. The actual canonical quotient maps appear in
every pullback. The two unique-lift clauses are separate: uniqueness over C_n is
not weakened by also requiring an H_n lift. The second clause applies to every
αC reducing to the specified αR. Because these are Over isomorphisms rather than
unconstrained scheme maps, they are over the correct bases and include inverses.
The only mismatch found during elaboration was the universe of Fin m; it was
repaired by the finite equivalent ULift. No mathematical hypothesis was added.


## Returned-delivery repair (2026-10-22)

Repaired H2 from the independent review of immutable head `33e516416fa8`.
Compared the saved packet with the current shared node: only `lean` and
`stmt_deps` differ. The saved packet's initial dry run passed at `5603ffe00ba`,
but the mathematical dependency correction from the return still applied.
The statement now cites the landed `def-sfb-parameter-root-algebra` in place
of the pth-root locality theorem. Removed the henselian-parameter-root theorem
from `stmt_deps` and its module from the imports, and expanded all four coordinate
occurrences to the definition body `Ideal.Quotient.mk _ (MvPolynomial.X i)`.
The root quotient, the basis, both comparison maps, and both unique-lift clauses
are mathematically unchanged. There is no new definition or dependency module.
The node's natural-language statement, proof and proof dependencies are unchanged.
The `lean.statement` field has been regenerated verbatim from the repaired file.

Repair self-reading: opened the landed definition node and its full upstream
abbreviation, and the removed coordinate's definition. Its body is exactly the
inline term now used. Reviewed the theorem and `rootIdeal` after expansion: the
basis coordinates lie in H_n, their residual images generate K_n, and eC still
sends them to the polynomial classes over R. All original hypotheses and
conclusions, including r=0, n=1 and A empty, remain as audited above.

Repair validation: scompile.py compiled the repaired module cleanly in sandbox
mode (7.6 s) and library mode (8.1 s). A local record self-check verified that
only `lean` and `stmt_deps` differ from the shared node, all four coordinate
occurrences are expanded, the signature record is verbatim, and the sole
postponed proof remains the main theorem.

Final preflight caught a signature-record formatting mismatch: the gate records
the signature before `:=`, with whitespace normalized. Removed the assignment
marker and normalized whitespace in `lean.statement`; the Lean file is unchanged.
