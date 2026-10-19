## Worker report

The module `Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent` states
`Algebra.exists_nonempty_open_regular_of_separable_fractionRing`, with `sorry` as its
entire proof. It states the unchanged node, Stacks 07PB (`lemma-J-0-goes-up`), with J-0
expanded using 07P7 (`definition-J`). I read those source passages and the full six-step
DAG proof. The declaration docstring carries all six steps and their dependencies.
No definition, hypothesis, or conclusion has been replaced or added.

The previous attempt confused the node's accepted stage-1 split with a stage-2 Lean
statement. Its accepted split remains intact. There was no `lean` record and no module
in the sandbox; this delivery supplies them and changes only `lean` in the node copy.

Hypotheses and conclusion, clause by clause:

- Commutative rings R and S: `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  Both universes are explicitly declared and independent, with `autoImplicit false`.
- R is Noetherian: `[IsNoetherianRing R]`. No Noetherian hypothesis on S is added.
- Both rings are nonzero integral domains: `[IsDomain R] [IsDomain S]`. These include
  nontriviality as well as absence of zero divisors, as required by the node.
- The map R to S is `[Algebra R S]`, whose structure map is `algebraMap R S`.
  This allows every commutative ring map via its associated algebra structure.
- The map is injective: `hinj : Function.Injective (algebraMap R S)`.
- The map is of finite type: `[FiniteType R S]` in namespace `Algebra`, i.e.
  the dependency's `Algebra.FiniteType R S`. Zero algebra generators are allowed.
- The fraction fields K and F are the actual quotient constructions `FractionRing R`
  and `FractionRing S`. Thus no separate fraction-field choices or extra hypotheses
  on them occur. `IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj`
  is Mathlib's canonical extension of the given injection to fraction fields.
  Its docstring explicitly gives the map r/s to image(r)/image(s).
- Separability is `hsep : @IsSeparableExtension (FractionRing R) (FractionRing S) _ _
  (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra`.
  This uses exactly `Algebra.IsSeparableExtension` from the recorded dependency,
  including transcendental separable extensions, not merely algebraic separability.
  The explicit algebra argument ties it to the induced embedding, not an arbitrary one.
- The base regular open is `hregular : ∃ U : Set (PrimeSpectrum R), IsOpen U ∧
  U.Nonempty ∧ ∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal)`.
  `PrimeSpectrum R` with its Zariski topology is the underlying space of the recorded
  `AlgebraicGeometry.Spec (CommRingCat.of R)` definition. The three conjuncts separately
  assert openness, nonemptiness, and regularity at every prime belonging to U.
- The conclusion is `∃ V : Set (PrimeSpectrum S), IsOpen V ∧ V.Nonempty ∧
  ∀ q ∈ V, IsRegularLocalRing (Localization.AtPrime q.asIdeal)`. It has precisely the
  same three requirements on the target. It does not assert openness of the entire
  regular locus, regularity outside V, or regularity of S globally.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with its docstring and
  `isNoetherianRing_iff_ideal_fg` (every ideal is finitely generated).
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, finite algebra generation.
- `Sheaf.FieldTheory.SeparableExtension`: both `Algebra.IsSeparablyGenerated` and
  `Algebra.IsSeparableExtension`; the statement uses the latter, as the node requires.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`; the
  underlying `PrimeSpectrum` and topology are used directly, as in the already landed
  residue-field criterion that cites this item.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` is localization
  at the complement of the prime, with its existing local-ring structure.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, which includes
  Noetherianity and locality and the maximal-ideal dimension equality. `IsRegularRing`
  was also read to verify the proof's intermediate regularity assertion.
- Additional canonical construction: `Mathlib.RingTheory.Localization.FractionRing`,
  `FractionRing` and `IsFractionRing.map`. These already give the fraction fields and
  induced map described inline in the node, so no additional notion/node is needed.

Statement imports are public. The already stated proof dependencies are ordinary imports:
`Mathlib.RingTheory.Localization.Submodule` (`IsLocalization.isNoetherianRing`),
`Mathlib.AlgebraicGeometry.OpenImmersion`
(`AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway`), and
`Sheaf.RingTheory.RegularRingSmoothAscent` (`Algebra.isRegularRing_of_smooth`). I opened
these declarations. The other proof dependencies are already statement imports except
`lem-exc-generic-smooth-domain`, which currently has no Lean record and is therefore not
imported; it is not needed to type this stage-2 statement. Its mathematical role is
explicit in step 4 of the docstring and the unchanged DAG proof.

Edge cases checked before writing:

- Identity maps, including R=S a field, are allowed; no positive transcendence degree,
  nonempty generating set, strict field extension, or special characteristic is assumed.
- For R=S a singular Noetherian domain, only the assumed regular open is asserted;
  the conclusion does not incorrectly require global regularity.
- R=k and S=k[x] allows a transcendental, separably generated fraction-field extension.
  Using `Algebra.IsSeparable` instead would incorrectly exclude that case.
- A nontrivial purely inseparable finite extension of an imperfect field does not
  satisfy `hsep`. No perfectness hypothesis is silently assumed.
- The empty open does not witness either existential because `Set.Nonempty` is explicit.
  Zero rings are excluded exactly by the node's domain hypotheses.
- No finiteness or equality of the ring universes is imposed. Canonical fraction fields
  stay in the respective ring universes and cover these data without extra size assumptions.

Searches for an existing statement (all remote searches used `msearch.py Q37
lem-exc-j0-separable-finite-type-ascent`, with records in `searches.jsonl`):

- LeanFinder query: "For an injective finite type map of Noetherian integral domains
  with separable fraction fields, existence of a nonempty open regular locus ascends
  from the source to the target". Eight hits, including Noether normalization,
  finitely generated subalgebra towers, integral local maps, Zariski's main property,
  and geometric reducedness descent; none asserts a nonempty regular open ascends.
- Loogle query: `IsRegularLocalRing, IsOpen`. Zero hits.
- Mathlib grep query: `J.?0|j.?0|nonempty.*regular|regular.*[Oo]pen`, restricted to
  `RingTheory`. Twelve unrelated hits (ideal variables named J0 and a sigma-to-pi map).
- LeanSearch query: "A nonempty regular open subset ascends along an injective finite
  type map of Noetherian integral domains with separable fraction fields". Eight hits
  concern integral schemes, open immersions, localization injectivity, or separable
  topological spaces. Their signatures do not give the item.
- `rg` of the upstream `WeilConjectures` tree and the project's `lean/Sheaf` for
  J-0/J0, regular-locus, nonempty-regular-open, and separable-finite-type combinations;
  `grep -rn` of the upstream tree for this item's id. No exact upstream statement;
  the project has `isOpen_regularLocus_of_residueField_finite_models`, whose proof
  cites this missing ascent result, and separate smooth-regularity results. Neither
  states the present claim. Broader J0 searches also matched unrelated local variables.
- Exact-name searches of upstream sources, project sources, and
  `dag/lean_names_upstream.json` for
  `exists_nonempty_open_regular_of_separable_fractionRing` and
  `NonemptyRegularOpenSeparableAscent` found no existing declaration/module.

No statement dispute, statement correction, new node, or dependency repair is required.
Validation: `scompile.py Q37 lem-exc-j0-separable-finite-type-ascent` compiled this
module successfully with no errors or warnings, both in the sandbox probe and as its
library module. The required `deliver2.py --no-push` preflight follows.


## Second reading by Q37

I independently opened the sandbox node and its Lean file, the six statement-dependency
records and their source declarations, and the Stacks source. The local shared clone
has no Stacks `.tex` files, so I read the launcher's literature checkout instead:
`more-algebra.tex`, lines 11575-11691 (the regular locus, definition-J, and
lemma-J-0-goes-up), and `algebra.tex`, definition-separable-field-extension,
lemma-smooth-at-generic-point, and lemma-regular-goes-up. The source's ambient ring
convention is commutative with identity. The singular-locus section assumes Noetherianity;
it is explicit for R here and follows for S from finite type. There is no ambient
perfectness, characteristic, dimension, or algebraic-extension assumption.

My object/hypothesis/conclusion checklist, with the node and signature open:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary commutative rings R and S | `(R : Type u) (S : Type v) [CommRing R] [CommRing S]` | Exact; u and v are separately bound. |
| R is Noetherian | `[IsNoetherianRing R]` | Exact; the dependency is `IsNoetherian R R`, equivalently every ideal is finitely generated. No independent Noetherian assumption on S is added. |
| R and S are nonzero integral domains | `[IsDomain R] [IsDomain S]` | Exact; these classes include nontriviality and the domain zero-product condition. |
| A ring map R to S | `[Algebra R S]`, map `algebraMap R S` | Exact; every unital map of commutative rings supplies this algebra structure. |
| The map is injective | `(hinj : Function.Injective (algebraMap R S))` | Exact; this same map induces the fraction-field algebra below. |
| The map is finite type | `[FiniteType R S]` inside namespace `Algebra` | Exact; the dependency's `Algebra.FiniteType` is finite generation of the top subalgebra, equivalent to the node's polynomial-surjection formulation. |
| K and F are the fraction fields of these domains | `FractionRing R`, `FractionRing S` | Exact canonical quotient constructions; the field instances follow from the respective domain hypotheses. No unrelated field choices occur. |
| The extension is induced by the given injection | `(IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra` | Exact; I read the map's definition and its fraction formula in Mathlib, not just its name. |
| F/K is separable in the node's sense | `hsep : @IsSeparableExtension (FractionRing R) (FractionRing S) _ _ ...` | Exact; I opened `Sheaf.FieldTheory.SeparableExtension`. It quantifies over intermediate fields finitely generated as fields, requiring a transcendence basis with separable algebraic remainder. This is Tag 030O, including transcendental extensions. The explicit algebra parameter is the induced map above. |
| Spec R and its Zariski topology | `PrimeSpectrum R` with its existing topology | Exact; `AlgebraicGeometry.Spec` has this underlying carrier and topology (`Spec_carrier` and the spectrum construction). No scheme structure is asserted or needed beyond its underlying topological space here. |
| A nonempty open U in Spec R | `hregular : ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧ ...` | Exact; all three existential/open/nonempty requirements appear. U is used only to assume existence, just as in the node. |
| Every local ring R_p for p in U is regular local | `∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal)` | Exact; I read both dependency definitions. Localization is at the prime complement; regular local includes locality, Noetherianity, and maximal-ideal generator number equal to Krull dimension. |
| There exists a nonempty open V in Spec S | `∃ V : Set (PrimeSpectrum S), IsOpen V ∧ V.Nonempty ∧ ...` | Exact; no condition on the whole regular locus or on all of S is substituted. |
| Every local ring S_q for q in V is regular local | `∀ q ∈ V, IsRegularLocalRing (Localization.AtPrime q.asIdeal)` | Exact; precisely the final clause and the same quantifier order as the node. |

I also read the source declarations of the recorded proof imports:
`IsLocalization.isNoetherianRing`,
`Scheme.isOpenImmersion_SpecMap_localizationAway`, and
`Algebra.isRegularRing_of_smooth`. Their signatures provide the indicated localization
and smooth-ascent inputs. The generic-smoothness node still has no recorded Lean module
in the shared snapshot, and it is a proof dependency only; the current statement needs
no missing notion or helper. There are no new nodes or dependency modules in this
delivery. There is no `statement_change`, and no correction or citer audit is needed.

Edge cases checked independently:

- The zero ring and an empty affine spectrum are excluded exactly by the node's domain
  hypotheses. An empty open cannot witness either side because `U.Nonempty` and
  `V.Nonempty` are explicit.
- A finite type presentation may have zero generators; identity maps and field-to-field
  algebraic separable maps are allowed. An empty transcendence basis is permitted by the
  actual separability definition. There is no independent index-set restriction.
- The extension k to Frac(k[x]) is covered: `hsep` does not demand algebraicity. A finite
  nontrivial purely inseparable extension of an imperfect field is excluded by the
  separability hypothesis, as it should be. Both characteristic zero and positive
  characteristic are unrestricted.
- A singular domain with a regular nonempty open is allowed; neither base nor target is
  assumed globally regular. The target conclusion does not assert the whole regular
  locus is open (J-1).
- Both ring universes are arbitrary and independent. Intermediate fields are subobjects
  of the actual target fraction field, rather than test objects in a smaller universe.
  Thus no subextension is lost and no extra universe equality is needed.

Independent duplicate searches, with different search terms from the worker:

- LeanFinder via `msearch.py`: "An inclusion of finitely generated domains with separable
  function field extension preserves the existence of a dense open of nonsingular
  points". Eight signatures returned: rational/partial-map dense domains, dominant
  normalization, function fields, and a Weierstrass coordinate-ring domain instance.
  None states regular-open ascent.
- Loogle via `msearch.py`: `IsRegularLocalRing, FractionRing`. Zero hits.
- LeanSearch via `msearch.py`: "A finitely generated extension of domains with separable
  quotient fields carries a nonempty regular Zariski open when the base has a nonempty
  regular open". Eight results concern separable closures, algebraic separability,
  formally unramified fields, or transcendence bases over perfect fields. Their returned
  signatures do not state this theorem.
- I ran `rg` on Mathlib, the upstream `WeilConjectures` tree, and `lean/Sheaf`, using
  regular-locus, J-0, regular/separable, nonempty/regular, and nonsingular combinations.
  A broad nonsingular/JZero search found elliptic-curve and zero-map material; narrowing
  to regular-locus/nonempty-regular/J-0 found no duplicate. I opened upstream
  `AlgebraicGeometry/Regular.lean` and project `RingTheory/JTwoResidueFieldCriterion.lean`:
  the former concerns regular schemes, smooth maps and curves, and the latter cites this
  result in its proof but states the different J-2 finite-model criterion. The excellent
  ring and quasi-excellent material defines stronger properties or uses them, rather
  than stating the present ascent. Exact declaration/module-name searches in upstream,
  project sources, and `dag/lean_names_upstream.json` returned no collision.

H5/H6/H8/H9 checks: this file has no new definition and only one theorem, whose entire
proof is `sorry`. Its module/declaration docstrings give the source and blueprint id;
I matched each of the six proof steps against the node, including both localization
identifications and the final nonempty principal open. All lines are at most 100
characters. The namespace, imports, and explicit `universe u v`/`autoImplicit false`
follow the contract. I compared `lean.statement` with the literal text from `theorem`
through the conclusion before `:= by`; they are verbatim equal.

Mismatches found: none. Changes: appended this independent second-reading report only;
the Lean module, signature, node statement, dependencies, and metadata are preserved.

Second-reader validation: the required `scompile.py Q37
lem-exc-j0-separable-finite-type-ascent
lean/Sheaf/RingTheory/NonemptyRegularOpenSeparableAscent.lean` succeeded for both the
sandbox probe and the library module (16.8 s and 11.9 s), with no errors or warnings.
