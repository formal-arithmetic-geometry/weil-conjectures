## Worker report

The delivery states `isUniversallyJapanese_of_forall_isN1` in
`Sheaf.RingTheory.UniversallyJapaneseN1Criterion`. Its sole proof is `sorry`;
no definitions or proved lemmas are added. The node changes only in `lean`.

Source checked: [Stacks Tag 0351](https://stacks.math.columbia.edu/tag/0351),
Lemma 10.162.3, including its complete proof. The referenced local TeX file is
absent on this machine; the published tag supplies the exact source. The source
and the node agree, so no statement correction or dispute is needed.

Hypothesis and conclusion correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`. No Noetherian,
  domain, nonzero, or excellence assumption is imposed on R.
- Every ring homomorphism R → S: the universal binder
  `∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S]` ranges over all
  algebra structures, hence all unital ring homomorphisms. Injectivity is not
  assumed. The domain condition is exactly `[IsDomain S]`.
- Finite type: `[Algebra.FiniteType R S]`, the recorded declaration of
  `def-weil-pbc-finite-type-algebra`.
- Every such S is N-1: `IsN1 S (FractionRing S)`, the recorded definition
  of finiteness of the integral closure in the fraction field.
- R is universally Japanese: `IsUniversallyJapanese R`, whose existing
  definition expands to the identical universal binders over finite type domain
  R-algebras followed by `IsN2 S (FractionRing S)`. This renders the node's
  explanatory conclusion that every such S is N-2 as well.

Dependencies read in full and reused:

- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, generated as an algebra.
- `Sheaf.RingTheory.JapaneseDomain`: `IsN1`, `IsN2`. The former is
  `Module.Finite S (integralClosure S K)`; the latter quantifies over finite
  field extensions with the compatible composite S-algebra structure.
- `Sheaf.RingTheory.NagataRing`: `IsUniversallyJapanese`, whose signature and
  full body were read alongside `IsNagataRing` and their docstrings.

The statement dependencies are public imports. The stated proof dependencies
are plain imports: `Algebra`, `Polynomial`, `Module.Finite`, `integralClosure`,
`Localization.AtPrime`, `Module.Finite.trans`, `Algebra.IsIntegral.of_finite`,
`RingHom.IsIntegral.trans`, and `Polynomial.exists_finite_coefficient_model`
from their recorded modules. The coefficient-model theorem's entire source,
signature and proof docstring were read. The declaration docstring records all
four DAG proof steps, including the residue-field identification at (X), the
finite coefficient model, finite-module transitivity, and equality of the two
integral closures by transitivity of integrality.

Edge cases checked:

- The zero base ring is allowed; it has no unital domain algebra, so both the
  hypothesis and the defining conclusion are vacuous, consistently.
- R may have nilpotents or zero divisors, and maps R → S may have kernel.
- S a field and the degree-one field extension L = Frac(S) are included;
  there is no positive-degree, characteristic, separability or normality restriction.
- Finite type includes zero algebra generators. No auxiliary finite family is
  required nonempty.
- The test-algebra universe is R's own universe u, exactly as in the existing
  `IsUniversallyJapanese` interface. It is not an independently smaller universe.
  A finitely generated R-algebra has cardinality at most max(|R|, ℵ₀) and therefore
  has a model in this universe; finite field extensions likewise have a model
  in their fraction field's universe. The chosen fraction field loses no cases.
- Every variable and universe is explicitly bound. No file-local notation,
  private definition or local instance is introduced.

Searches performed before writing (2026-10-16):

- `msearch.py ... leanfinder "A ring is universally Japanese if every finite type
  domain algebra has finite normalization N-1"`: eight hits, including
  `Algebra.QuasiFinite`, Jacobson finite-type results, and smooth descent;
  none state this criterion.
- `msearch.py ... loogle "IsUniversallyJapanese, IsN1"`: zero hits,
  unknown identifier `IsUniversallyJapanese` in the Mathlib search index.
- `msearch.py ... grep "Japanese|Nagata|IsN1|IsN2" RingTheory`: one hit,
  the unrelated Nagata proof of Noether normalization.
- `rg` on the upstream `WeilConjectures` source for `IsUniversallyJapanese`,
  `IsN1`, and the ordinary-language phrase, and the required item-id grep:
  no declaration or matching criterion.
- `rg` on `lean/Sheaf` for the names and the criterion: existing definitions
  `JapaneseDomain` and `NagataRing` are reused. `QuasiExcellentNagata` cites
  this node only in its proof docstring; it does not already declare it.
- The proposed name `isUniversallyJapanese_of_forall_isN1` was searched in
  Mathlib, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no match.

No new nodes, dependency repairs, statement faults, or omitted proof-dependency
imports are needed. Validation uses the prescribed `scompile.py` wrapper and
`deliver2.py Q42 lem-exc-universally-japanese-n1-criterion --no-push`. The dry-run
transcript is retained as `dry-run.log` in this sandbox; the second reader delivers.

## Second reading by Q42

I independently opened the sandbox node and its Lean module, all three statement
dependency nodes and their actual declarations, the proof-dependency records, and
`Polynomial.exists_finite_coefficient_model` with its full signature and docstring.
The source is Stacks Algebra, Tag 0351, `lemma-check-universally-japanese`.
Because the local Stacks checkout is absent, I read both the published tag
<https://stacks.math.columbia.edu/tag/0351> and the actual upstream `algebra.tex`
at <https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex>,
including its Conventions section. Rings there are commutative with identity;
the zero ring is included. The lemma has no additional standing hypothesis.

The node's objects, hypotheses, and conclusion, matched individually:

1. A commutative ring R: `(R : Type u) [CommRing R]`. Exact. In particular R is
   neither assumed a domain nor assumed Noetherian or nontrivial.
2. Every homomorphism R to S: `∀ (S : Type u) [CommRing S] ... [Algebra R S]`.
   Exact. For commutative rings an algebra structure supplies the ring map, and
   every unital ring map supplies such an algebra via `RingHom.toAlgebra`.
   There is no injectivity requirement. The map varies inside the universal
   quantifier, after S, as required.
3. S is an integral domain: `[IsDomain S]` inside that quantifier. Exact, including
   the nonzero-ring requirement on S inherent in the source's domain convention.
4. The map is finite type: `[Algebra.FiniteType R S]`. Exact: I read the recorded
   Mathlib declaration, whose data are finite generation of the top subalgebra.
   It imposes no finite-module, finite-presentation or separability assumption.
5. Every such S is N-1: the hypothesis concludes `IsN1 S (FractionRing S)`.
   Exact: the dependency `Sheaf.RingTheory.JapaneseDomain` defines this as
   `Module.Finite S (integralClosure S (FractionRing S))`. Its fraction-field
   and algebra instances are canonical, not extra hypotheses on S.
6. R is universally Japanese: `IsUniversallyJapanese R`. Exact: I opened
   `Sheaf.RingTheory.NagataRing`; its body quantifies over every finite type
   domain R-algebra S and concludes `IsN2 S (FractionRing S)`.
7. The explanatory conclusion says each such S is N-2. Exact by that same
   definition. `IsN2` in `JapaneseDomain` quantifies over finite-dimensional
   field extensions L with the compatible composite S-algebra structure, and
   asserts `Module.Finite S (integralClosure S L)`. Thus the finite-extension
   clause and its scalar compatibility are retained; the conclusion is not
   merely N-1 or the Noetherian Nagata predicate.

Universe and edge-case reading: the theorem is polymorphic in explicitly bound
`u`, and S has the same universe as R, exactly as the reused universal Japanese
predicate. This does not quantify in an independently smaller universe. Any
finite type algebra is a quotient of a polynomial algebra in finitely many
variables and has an isomorphic model in R's universe. A fraction field is
likewise small in the ring's universe, and a finite field extension has a model
there by a finite basis. All conditions involved are invariant under these
isomorphisms. Hence this convention excludes no mathematical case. The zero
base ring has no unital domain algebra, so both sides are vacuous, correctly.
Zero divisors and nilpotents in R and kernels of R to S are allowed. Fields S,
identity field extensions, finite and infinite fields, inseparable extensions,
and every characteristic are covered. Finite type with zero generators is
included; no nonempty index family is imposed. Schemes, empty schemes, and an
external numerical n do not occur in this statement. Every variable and
universe is bound; no hidden local notation or instance appears.

Independent searches, 2026-10-16 (using different wording from the first reader):

- LeanFinder via `msearch.py`: “finite normalization for all finitely generated
  domain algebras implies integral closure finite in every finite field
  extension”. Eight results, including `IsIntegralClosure.finite` and normal
  closure finiteness. Those require different hypotheses (for example a
  Noetherian integrally closed base or separability) and do not state the
  universally Japanese criterion.
- Loogle via `msearch.py`, valid query `"Japanese"`: no hits. An earlier
  two-string query failed to parse and was not counted as a successful search.
- LeanSearch via `msearch.py`: “every finite type domain algebra is N-1 implies
  universally Japanese”. Service unavailable (Internal Server Error); no
  mathematical verdict is inferred from this unavailable search.
- The Mathlib grep service searched
  `normalization.*finite|finite.*normalization|universallyJapanese|universally_japanese`
  in RingTheory; its only result was an unrelated valuation comment.
- Direct `rg` in Mathlib RingTheory, upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`, using universal-Japanese
  spellings, normalization/finiteness phrases and `forall` with `IsN1`, found
  no existing criterion. The project's Japanese/Nagata definitions are the
  exact dependencies already reused. `QuasiExcellentNagata` is a consumer,
  not a duplicate of this criterion. The proposed declaration name and the
  item's blueprint id were also checked against the project/upstream sources.

Proof/interface reading: `Polynomial.exists_finite_coefficient_model` requires
precisely a nonzero prime r of S[X] contracting to zero and a finite extension
of its residue field, and returns the finite subalgebra, fraction-field
structure and compatible algebra equivalence used in the docstring. For
r = (X), the evaluation-at-zero formulas identify that residue field with
`FractionRing S`, including when S is a field. I also read the actual
`Module.Finite.trans`, `Algebra.IsIntegral.of_finite` and
`RingHom.IsIntegral.trans` signatures: they give the finite-module and integral
transitivity steps recorded in the node. All statement dependencies are public
imports, and every recorded stated proof dependency has its module imported.
The declaration docstring follows each of the four node proof steps, including
the residue-field identification, finite coefficient model, finite R-algebra
generators, finite-module transitivity and the two closure inclusions.

No new nodes or dependency modules are present or required. There is no
`statement_change`, and no correction or citer audit is needed. The module
contains exactly one theorem with whole proof `sorry` and no new definitions;
there is no hollow definition or proved stage-2 assertion. Source/blueprint
docstrings, namespace conventions and 100-character lines are correct. I
compared `lean.statement` mechanically with the exact theorem signature in the
file: they agree verbatim. The node differs from the shared base only in
`lean`. I found no mismatch and left the correct Lean module and node unchanged;
the only second-reading change is this report section.

Second-reader validation: the prescribed `scompile.py Q42 lem-exc-universally-japanese-n1-criterion lean/Sheaf/RingTheory/UniversallyJapaneseN1Criterion.lean` completed with exit code 0 for both the sandbox check and the library module, with no errors or warnings. No other Lean file belongs to this delivery.
