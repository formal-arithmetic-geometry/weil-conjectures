## Worker report

The module `lean/Sheaf/RingTheory/FieldAlgebraStrictHenselizationExcellent.lean`
states `isExcellent_localizationAtPrime_strictHenselization`.  It uses
`Algebra.FiniteType k B` for “finitely generated commutative `k`-algebra”,
`Localization.AtPrime p` for `L = B_p`, the residue-field algebra and
`IsSepClosure` classes for the chosen separable closure `K`, and
`Algebra.IsStrictHenselization (Localization.AtPrime p) K C` for the strict
henselization `C`.

The Lean statement renders every hypothesis as follows:

* `(k : Type u) [Field k]` is the field `k`.
* `(B : Type v) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]` is the
  finitely generated commutative `k`-algebra `B`.
* `(p : Ideal B) [p.IsPrime]` is the chosen prime ideal.
* Every occurrence of `Localization.AtPrime p` is the ring `L = B_p`.
* `(K C : Type v) [Field K]`, the residue-field `Algebra` and `IsSepClosure`
  instances, and the `Algebra` and `IsScalarTower` instances from the
  localization to `K` render “choose a separable closure `K` of the residue
  field”.
* `[CommRing C] [Algebra (Localization.AtPrime p) C]` and
  `hC : Algebra.IsStrictHenselization (Localization.AtPrime p) K C` render
  “`C` is a strict henselization relative to `K`”.

The conclusion is the conjunction
`IsExcellent (Localization.AtPrime p) ∧ IsExcellent C`, followed by
`∀ I : Ideal C, IsExcellent (C ⧸ I)` for every quotient, followed by
`IsNoetherianRing C` and
`IsNoetherianRing (C ⧸ nilradical C)`.  Here `nilradical C` is the ideal of
nilpotent elements and is the node's `sqrt (0)`.

The statement docstring records the seven proof steps from the node: excellence
of fields and finite-type localization; Noetherianity of the localization and
strict henselization; the pointed-etale filtered-colimit and finite-presentation
argument for ind-etaleness; ind-etale stability to weak etaleness; excellence
ascent along the weakly etale map; finite-type permanence for all quotients;
and Noetherianity of the nilradical quotient.

Dependencies used by the module:

* `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
* `Sheaf.RingTheory.IsStrictHenselization`: `Algebra.IsStrictHenselization`.
* `Sheaf.RingTheory.GRing`: `IsGRing` and the G-ring notions used by
  `IsExcellent`.
* `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` and its chain predicates.
* `Sheaf.RingTheory.StrictHenselizationNoetherian`:
  `Algebra.isNoetherianRing_iff_isStrictHenselization` (a stated proof
  dependency).
* `Sheaf.RingTheory.PointedEtaleSmallFiltered`:
  `Algebra.pointedEtale_small_filtered` (a stated proof dependency).
* `Sheaf.RingTheory.IndPrincipalZariski`: the recorded principal-localization
  companion `Algebra.IsIndPrincipalZariski`; the ind-etale notion itself is the
  imported `Algebra.IndEtale` declaration.
* `Sheaf.RingTheory.IndEtaleStability`:
  `RingHom.indEtale_principalZariski_stability` (a stated proof dependency).

Edge cases checked: `p` is arbitrary prime (including minimal or maximal
primes); no characteristic or perfectness hypothesis is introduced; `I` is
arbitrary, including `⊥` and `⊤`; `nilradical C` is an allowed ideal; and the
universe parameters `u` and `v` allow the base field and algebra to have
different universes while the localization, residue field, strict
henselization, and their quotients share the required universe.

Searches made:

* `msearch.py ... leanfinder "strict henselization of an excellent local ring
  is excellent and quotients are excellent"`: returned only generic
  henselian/local-ring declarations; no excellence theorem.
* `msearch.py ... loogle "IsExcellent, ExcellentRing, strict henselization
  excellent"`: zero hits; `IsExcellent` is unknown to Mathlib.
* `msearch.py ... grep "excellent|excellence|strict.*hensel" Mathlib/RingTheory`:
  zero hits.
* `rg` over `WeilConjectures/` and shared `lean/Sheaf/` found no existing
  theorem with this statement; the only excellence declarations are the
  dependency module `Sheaf.RingTheory.ExcellentRing` and its uses.
* The node's recorded LeanFinder, Loogle, LeanSearch, and grep searches were
  also reviewed; they report no Mathlib or upstream match.

No statement correction, dependency module, new node, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by NK

I read the node and the Lean file independently, together with all five
statement-dependency node records and their actual definitions. The signature
states exactly the node's assertion. The following is the object, hypothesis,
and conclusion checklist (H3):

1. Field `k`: `(k : Type u) [Field k]`. Exact; neither characteristic nor
   perfectness is assumed.
2. Finitely generated commutative `k`-algebra `B`:
   `(B : Type v) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]`.
   Exact: Mathlib's `Algebra.FiniteType.out` is finite generation of the top
   subalgebra, not module finiteness or finite presentation.
3. Prime ideal `p` of `B`: `(p : Ideal B) [p.IsPrime]`. Exact; no maximality
   or nonzero condition is imposed.
4. Localization `L = B_p`: every occurrence of `Localization.AtPrime p`.
   Exact: I opened `Mathlib.RingTheory.Localization.AtPrime.Basic` and checked
   its definition as `Localization p.primeCompl`, the declaration recorded by
   `def-weil-pbc-localization-at-prime`. Locality is supplied by its instance,
   not an additional assumption on `B`.
5. Chosen separable closure `K` of the residue field of `L`:
   `(K : Type v) [Field K]`,
   `[Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K]`, and
   the corresponding `IsSepClosure` instance. Exact: I read Mathlib's
   `IsSepClosure` fields `sep_closed` and `separable` (separability implies
   algebraicity). This allows the identity closure of a separably closed
   residue field and does not replace a separable closure by an algebraic
   closure in positive characteristic.
6. Compatible map `L → K`: `[Algebra (Localization.AtPrime p) K]` and
   `[IsScalarTower (Localization.AtPrime p)
   (IsLocalRing.ResidueField (Localization.AtPrime p)) K]`.
   Exact: these say that the map factors through the residue map as required
   by the chosen-residue-closure construction; they are not extra geometric
   assumptions.
7. Strict henselization `C` relative to this `K`:
   `(C : Type v) [CommRing C] [Algebra (Localization.AtPrime p) C]` and
   `hC : Algebra.IsStrictHenselization (Localization.AtPrime p) K C`.
   Exact: I opened `Sheaf.RingTheory.IsStrictHenselization`. It is the
   existence of a universal cocone on the full pointed-etale subcategory of
   `Over (CommAlgCat.of L K)` with an `L`-algebra isomorphism to `C`.
   The objects, arrows commuting with the map to `K`, and structural map
   agree with `def-sc-ring-strict-henselization`; no arbitrary strictly
   henselian extension is substituted. No local, Noetherian, or excellence
   instance on `C` is assumed.
8. Excellence of `L` and `C`:
   `IsExcellent (Localization.AtPrime p) ∧ IsExcellent C`. Exact.
9. Excellence of every quotient: `(∀ I : Ideal C, IsExcellent (C ⧸ I))`.
   Exact universal quantifier after the fixed `C`; no properness or finite
   generation of the ideal is required.
10. Noetherianity of `C`: `IsNoetherianRing C`. Exact conclusion, not a
    hypothesis.
11. Noetherianity of the reduction:
    `IsNoetherianRing (C ⧸ nilradical C)`. Exact: Mathlib defines `nilradical C`
    as the radical of the zero ideal, with membership precisely nilpotence.
12. Meaning of excellent: the shared declaration `IsExcellent` in
    `Sheaf.RingTheory.ExcellentRing`, not a new predicate. I opened its full
    definition and `Sheaf.RingTheory.GRing`: it includes Noetherianity,
    regular local completion maps, openness of the regular locus of every
    finite-type algebra, and universal catenarity. Its chain predicates
    record prime endpoints, strict inclusions, absence of insertable primes,
    a finite upper bound on chain lengths, and equal saturated-chain lengths.
    The regularity predicate is Mathlib's `IsRegularLocalRing` from the
    recorded dependency. These are the notions in the node and Stacks 07QT.

Source reading: the source files are absent from the shared literature
checkout; I read the actual available copies at
`/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`
`sec-smooth-purity/sk-prop-a1-kummer/thm-exc-curve-open-dimension-general.md`,
and `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`.
The blueprint's second proof paragraph asserts excellence and Noetherianity
of the strict local ring and passage to its reduction. In `more-algebra.tex`
I read `definition-excellent` (07QT), `lemma-finite-type-over-excellent`
(07QU), `proposition-ubiquity-excellent` (07QW), and
`lemma-henselization-noetherian` (06LJ). None adds perfectness, a characteristic
restriction, or a finite residue-extension hypothesis. The section's opening
paragraph introduces the three standard excellence conditions and adds no
standing hypothesis. In `algebra.tex` I read
`lemma-strict-henselization-different` (04GW), including the category of
pointed etale algebras, morphisms, filteredness, and colimit. The node's
excellence proof uses Greco separately, as its source record already explains;
07QT/07QU/07QW alone do not assert strict-henselization permanence.

Edge cases: all characteristics, including imperfect fields; arbitrary primes
(minimal, maximal, or zero when prime); `I = ⊥` and `I = ⊤`, the latter giving
the zero ring, whose spectrum and regular-locus conditions are empty; and
possibly zero nilradical. A zero `B` has no prime ideal and hence introduces
no omitted case. No index type, degree, or positive-dimension restriction is
in the signature. `u` and `v` are separately bound; `k` need not share `B`'s
universe. The common arbitrary universe `v` for `L`, its residue closure,
and `C` is exactly the convention explicitly stated by the recorded strict
henselization dependency. There is no unbound universe or implicit variable,
and no independent small universe of test algebras making the predicates
vacuous.

H4 searches repeated with different wording:

- `leanfinder`: "Excellence and Noetherianity of strict henselizations of
  localizations of finite type field algebras" returned eight generic
  Noetherian/localization/henselian/quasi-finite declarations; none mentions
  excellence or states this assertion.
- `loogle`: `"IsExcellent"` returned no hits.
- `grep`: `catenary|[Ee]xcellen|quasi.?excellent` returned only an incidental
  "excellent paper" comment in `Mathlib/Algebra/Lie/InvariantForm.lean`.
- `leansearch`: "A strict henselization of a local ring essentially of finite
  type over a field and every quotient are excellent" was unavailable
  (Internal Server Error); this is not counted as a negative search.
- Direct `rg` over pinned Mathlib, the slopmaster2 `WeilConjectures` tree,
  and shared `lean/Sheaf` for declaration names involving excellence or
  catenarity, and for excellence together with strict henselization, found
  only the shared excellence definitions, the different quasi-excellent
  Nagata theorem, and references to this still-unwritten node. There is no
  matching theorem to record with `existing: true`. The upstream-name index
  has no occurrence of this item.

I also opened the actual available proof-dependency declarations:
`Algebra.isNoetherianRing_iff_isStrictHenselization`,
`Algebra.pointedEtale_small_filtered`,
`RingHom.indEtale_principalZariski_stability`, the imported upstream
`Algebra.IndEtale` filtered-colimit class, and the Mathlib
`Algebra.Etale.finitePresentation` match. They apply to the same local ring,
residue closure, and pointed category used here. The three excellence proof
nodes without Lean records are not falsely claimed as imported declarations.
No new node or dependency module is delivered, so H12/H13 add no further files.

Mismatch repaired (H8): the original docstring compressed away the node's
small-skeleton cocone comparison and did not explicitly cite the source of
weakly-etale excellence ascent. I expanded the numbered proof plan to follow
all seven node steps, including cocone transport and extension, arbitrary
quotient ideals, and the nilradical argument, and cited Greco Theorem 5.3(iv)
with Remark 5.2. The theorem signature and natural statement were already
correct and are unchanged. The node's `lean.statement` was checked verbatim
against the file. There are no hollow definitions, private copies, additional
proved lemmas, or proofs other than the named theorem's `sorry`.

Validation: the repaired module compiled cleanly via the required `scompile.py`
wrapper, both as the sandbox probe (4.4 seconds) and at its actual library
module path (8.0 seconds), with no errors or warnings. The verbatim signature
comparison and 100-character Lean line-width check also passed.
