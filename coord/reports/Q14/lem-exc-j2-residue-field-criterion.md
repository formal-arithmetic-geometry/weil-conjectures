## Worker report

The module `Sheaf.RingTheory.JTwoResidueFieldCriterion` states
`isOpen_regularLocus_of_residueField_finite_models`, with its sole proof `sorry`.
No definitions, helper statements, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`.

Source read: Stacks Project Tag [07PC](https://stacks.math.columbia.edu/tag/07PC),
`lemma-J-2`, implication (4) to (1), and Tag
[07P7](https://stacks.math.columbia.edu/tag/07P7), `definition-J`, all three clauses.
The literature checkout does not contain `more-algebra.tex`, so the official tag pages
were read. The finite domain model in 07PC is represented by its embedded image in its
specified fraction field, exactly as the node requests. The docstring carries all seven
proof steps, including the node's correction that the fraction field of the composite
ring is the compositum `KL`, which need not equal `K'`.

Hypothesis and conclusion audit:

- A Noetherian commutative ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- Every prime ideal is quantified as `(p : Ideal R) [p.IsPrime]` in `hmodels`.
- The specified residue field is `p.ResidueField`; its actual definition is the residue
  field of `Localization.AtPrime p`.
- A field extension is `(L : Type (max u v)) [Field L] [Algebra p.ResidueField L]`.
  Its finiteness and pure inseparability are `[Module.Finite p.ResidueField L]` and
  `[IsPurelyInseparable p.ResidueField L]`. This includes identity extensions and
  characteristic zero, without a positive-characteristic restriction.
- The stipulated composite map `R → p.ResidueField → L` is expressed by `[Algebra R L]`
  and `[IsScalarTower R p.ResidueField L]`. These are compatible algebra structures,
  not an arbitrary additional map: the scalar tower says their algebra maps compose.
  Every given residue-field extension has this canonical composite structure.
- An embedded `R`-subalgebra is `∃ B : Subalgebra R L`. Its inclusion, multiplication,
  and `R`-action are Mathlib's existing ones; no separate domain assumption is required
  because a subalgebra of a field is already a domain.
- Finiteness as an `R`-module is `Module.Finite R B`.
- Exhaustion by fractions with nonzero denominator is exactly
  `∀ x : L, ∃ b c : B, (c : L) ≠ 0 ∧ x = (b : L) / (c : L)`.
  Fractions use the inclusion into this very field `L`, not an unspecified isomorphism.
- The nonempty regular open is `∃ U : Set (PrimeSpectrum B), IsOpen U ∧ U.Nonempty ∧
  ∀ q ∈ U, IsRegularLocalRing (Localization.AtPrime q.asIdeal)`.
  `PrimeSpectrum B` is the Zariski topological space underlying `Spec B`.
- Every finite type `R`-algebra is `(A : Type (max u v)) [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A]`.
- Openness of its complete regular locus is
  `IsOpen {q : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime q.asIdeal)}`.
  This is the expanded J-2 clause appearing literally in `IsQuasiExcellent` from
  the recorded `def-exc-excellent-ring` module; the node's “equivalently” is a name
  for this assertion, not an additional independent claim.
- Both test fields and test algebras use `Type (max u v)` with explicitly bound `u v`.
  Their universe is not independently smaller than the base ring, so the field-model
  quantifier cannot become vacuous on a large ring. No finite set or cardinality bound
  is imposed; `v` permits arbitrarily large ambient universes.

Dependency declarations and sources read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (193–204).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` (the prime
  complement localization); `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField` (26–34), with the canonical base algebra structure.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable` (102–110).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (119–123).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map` (469–480).
  Only the underlying prime spectrum is needed in the statement.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` (48–53) and
  `IsRegularRing` (91–94); the former is used on prime localizations.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` (37–40).
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, with its explicitly expanded
  J-2 clause, and `IsExcellent`; imported as the dependency's recorded module.

The modules of already stated proof dependencies are also imported:
`Sheaf.FieldTheory.SeparableExtension` (`Algebra.IsSeparableExtension`),
`Sheaf.FieldTheory.MakeSeparable`
(`Algebra.exists_finite_purelyInseparable_separable_extension`),
`Mathlib.RingTheory.Noetherian.Basic` (`IsNoetherianRing.of_finite`), and
`Mathlib.RingTheory.FiniteType` (`Algebra.FiniteType.isNoetherianRing`).
The three J-0/regular-locus proof lemmas have no Lean records in the snapshot, so there
are no recorded modules to import for them. They are not needed to type this statement.

Edge cases checked: if `R` is the zero ring, it has no primes, so `hmodels` is vacuous
and the only unital `R`-algebras are zero rings with empty, hence open, regular locus.
The zero finite type algebra is allowed for arbitrary `R`. A field subalgebra has
`0 ≠ 1`, and denominator one is permitted. `U` must be nonempty, not merely the empty
regular open. Identity and characteristic-zero purely inseparable extensions are
included. No injectivity of `R → B` is imposed: its kernel is the specified prime.
There is no node fault or disputed statement.

Searches made (logged through `msearch.py` under Q14 and this item):

- LeanFinder: `residue field finite purely inseparable extension finite algebra regular
  locus open J-2`. Eight results concern residue-field maps, finite residue-field
  extensions, quasi-finiteness and unramifiedness; none is the criterion.
- Loogle: `IsRegularLocalRing, IsNoetherianRing, Algebra.FiniteType`. Zero hits.
- Grep: `IsRegularLocalRing|IsQuasiExcellent|IsExcellent` with subdirectory
  `Mathlib/RingTheory` initially returned zero hits because that is not the wrapper's
  subdirectory convention. Repeated correctly with `RingTheory`: ten lines in
  `RegularLocalRing/Polynomial.lean` and `RegularLocalRing/Defs.lean`; these provide
  regularity notions and a polynomial-localization lemma, not the criterion.
- LeanSearch: `J2 criterion finite purely inseparable residue field extensions with
  finite models having nonempty regular open`. Unavailable: Internal Server Error;
  this is not recorded as a negative search result.
- Direct `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for this node id,
  `J-2`, `lemma-J-2`, and regular/open combinations found only proof references in
  `FieldsExcellent`/`QuasiExcellentNagata` and unrelated geometry; no existing criterion.
- Direct `rg` across Mathlib, upstream and side sources for
  `regularLocus.*residueField|residueField.*finite_models|isOpen_regularLocus_of_residueField_finite_models`
  found no declaration, and the upstream names table had no corresponding name.

Validation: the final module is checked only through the prescribed `scompile.py` wrapper;
`deliver2.py --no-push` is used for the required compile/preflight dry run. The independent
second-reading section is intentionally left to the next worker.

## Second reading by Q14

I independently opened the node, the complete delivered Lean module, all eight statement
 dependency records and their declaration sources, and the recorded proof-dependency
interfaces. The local literature directory is absent, so I read the official Stacks
07PC and 07P7 pages and fetched the TeX directly from
<https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex>.
I read the opening of `section-singular-locus`, `definition-J`, and the complete
`lemma-J-2` and its proof. The standing assumption is a Noetherian commutative ring;
there is no standing domain, nonzero, characteristic, or finiteness-of-dimension assumption
on the base. The embedded finite domain model in the node is the source's model identified
with its image in its specified fraction field.

The object/hypothesis/conclusion list, matched with the Lean, is as follows. Every entry
passes; no statement repair is needed.

1. Object and base hypothesis: a commutative Noetherian ring `R` is precisely
   `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
2. Every prime of this ring: the first binders of `hmodels` are
   `∀ (p : Ideal R) [p.IsPrime]`. No maximality assumption is present.
3. The specified residue field is `p.ResidueField`, not `R / p` or an arbitrary field.
   Its source declaration is `IsLocalRing.ResidueField (Localization.AtPrime p)`.
4. Every field extension of that residue field is represented by
   `(L : Type (max u v)) [Field L] [Algebra p.ResidueField L]`. The two hypotheses
   `[Module.Finite p.ResidueField L] [IsPurelyInseparable p.ResidueField L]` express
   exactly finite dimension and pure inseparability.
5. The stipulated composite map from `R` is `[Algebra R L]` together with
   `[IsScalarTower R p.ResidueField L]`. I checked `IsScalarTower.algebraMap_eq` in
   `Mathlib.Algebra.Algebra.Tower`: it identifies this map with the composite through
   the canonical residue field. Conversely that composite always supplies such an
   algebra and tower, so these binders do not restrict the allowed extensions.
6. The finite model may depend on both `p` and `L`: it is inside their quantifiers as
   `∃ B : Subalgebra R L, Module.Finite R B ∧ ...`. A subalgebra inherits its domain
   and nonzero structure from the field; no separate assumption that `R` is a domain
   or embeds into it is introduced. Module finiteness uses the induced `R`-action.
7. Fractions must exhaust this very `L`: the clause
   `∀ x : L, ∃ b c : B, (c : L) ≠ 0 ∧ x = (b : L) / (c : L)` asserts exactly this.
   Both numerator and denominator use the actual subalgebra inclusion.
8. The nonempty regular open in its spectrum is
   `∃ U : Set (PrimeSpectrum B), IsOpen U ∧ U.Nonempty ∧ ...`.
   I checked that `Spec` uses the usual prime spectrum with the Zariski topology;
   no scheme structure is needed for this topological clause.
9. Every local ring on the chosen open is regular: the remaining clause is
   `∀ q ∈ U, IsRegularLocalRing (Localization.AtPrime q.asIdeal)`.
   This is the actual prime localization, using the recorded regular-local predicate.
10. The conclusion concerns an arbitrary finite type algebra, with precisely
    `(A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]`.
    It neither assumes a domain nor excludes nonreduced algebras.
11. Openness of the full regular locus is exactly
    `IsOpen {q : PrimeSpectrum A | IsRegularLocalRing (Localization.AtPrime q.asIdeal)}`.
    The conclusion is not restricted to some nonempty open subset.
12. The final equivalent wording is a name for assertion 11 for every `A`.
    I opened `Sheaf.RingTheory.ExcellentRing`: its `IsQuasiExcellent` definition has
    precisely this expanded J-2 clause, in addition to its separate Noetherian and
    G-ring clauses. The delivery correctly concludes J-2 alone. Instantiating `v = u`
    gives its same-universe test-algebra convention.

Dependency audit: I read `IsNoetherianRing` and its ideal-finiteness equivalence,
`Localization.AtPrime`, `Ideal.ResidueField`, `IsPurelyInseparable` and
`isPurelyInseparable_iff_pow_mem`, `Module.Finite`, `AlgebraicGeometry.Spec`,
`IsRegularLocalRing`, `Algebra.FiniteType`, and `IsQuasiExcellent` in the recorded modules.
They render the node's notions, rather than similarly named substitutes. In particular,
`Module.Finite` is module generation, not cardinal finiteness, and regularity is not
smoothness over a residue field. The proof interfaces `Algebra.IsSeparableExtension`
and `Algebra.exists_finite_purelyInseparable_separable_extension` were also opened:
the latter takes field generation via `(⊤ : IntermediateField k K).FG` and supplies
finite purely inseparable extensions and the commuting square as used in the docstring.
The three unstated regular-locus proof nodes still have no Lean record in this snapshot;
they are proof prerequisites, not missing objects required to type the current statement.
No new definition node or dependency module is included or needed.

Edge cases: the zero base ring has no primes, so the model premise is vacuous;
its unital algebras are zero rings and their regular locus is empty and open. The
zero test algebra is also allowed over a nonzero base. Finite type includes zero
algebra generators (`n = 0`), and module finiteness imposes no positive generator
count. There is no independent index set. The open `U` is required to be nonempty,
so an empty open cannot witness the model hypothesis. A model inside a field is
nonzero, and fractions with denominator one are allowed. Identity extensions and
characteristic zero are included; the exponential-characteristic formulation of pure
inseparability yields precisely the identity-extension condition in characteristic zero.
The kernel of `R → B` is the chosen prime, without assuming injectivity of that map.
Both test fields and test algebras live in `Type (max u v)`, at least the base universe;
there is no vacuous quantification over a universe too small for the base. The theorem
is polymorphic in both explicitly bound universes. Lower-universe objects can be lifted
to that common universe, and finite extensions and finite type algebras have small models.

Independent duplicate searches, using different phrasing from the worker:

- LeanFinder through `msearch.py`: `Noetherian commutative ring regular locus of
  finitely generated algebras inseparable finite residue extensions`. Eight hits:
  quasi-finiteness, finite residue fields, geometric reducedness, and essential finite
  type residue-field maps; their printed types do not state this regular-locus criterion.
- Loogle through `msearch.py`: `"IsRegularLocalRing", "IsOpen"`; zero hits.
- LeanSearch through `msearch.py`: `Finite integral models of residue field extensions
  imply openness of regular loci`; unavailable with Internal Server Error, not evidence
  that no theorem exists.
- Direct `rg` in pinned Mathlib RingTheory, all upstream `WeilConjectures`, all side
  `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `regularLocus|regular_locus|JTwo|IsJ2|finite_models|J-2|lemma-J-2` found only the
  references in `FieldsExcellent` and `QuasiExcellentNagata`. A broader regularity/open
  search found regular-local lemmas, projective-dimension loci, and geometric loci,
  not this criterion. Thus the new statement module is retained.

H5/H6/H8/H9: no definitions, auxiliary axioms, private encodings, local notation, or
proved statements occur; the sole theorem proof is `sorry`. The source/blueprint
docstrings are present and carry all seven node proof steps, including the compositum
`KL` correction already in the node's proof. No `statement_change` is present or needed.
The recorded signature is byte-for-byte equal to the signature in the module, all Lean
lines are at most 100 characters, and every variable and universe is explicitly bound.

Mismatches and changes: none found in the Lean, node statement, or dependency interfaces.
I left them unchanged and appended this independent reading and its source/search evidence.
Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.

The explicit `scompile.py Q14 lem-exc-j2-residue-field-criterion` run completed with
exit code 0 for the sandbox and library-path checks, with no diagnostics or warnings.
