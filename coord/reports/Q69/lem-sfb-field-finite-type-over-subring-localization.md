## Worker report

The new module `Sheaf.RingTheory.FieldFiniteTypeSubringLocalization` states
`Subring.exists_isField_away_finite_of_finiteType`, with its proof postponed by
`sorry`. It follows Stacks Project, Algebra, Tag 00FY,
`lemma-field-finite-type-over-domain`, read at algebra.tex:6611–6627. No new
notion or dependency module is required, and the accepted stage-1 split is unchanged.

Clause-by-clause correspondence:

- A field K: `{K : Type u} [Field K]`, with the universe explicitly bound.
- A commutative subring R of K containing 1: `(R : Subring K)`. The inherited
  commutative ring structure and `R.subtype` are the actual subring and its
  inclusion, including preservation of 1.
- K is a finitely generated R-algebra: `(hfinite : R.subtype.FiniteType)`.
  This is exactly the recorded dependency `RingHom.FiniteType`, using the
  algebra structure induced by the inclusion, without a separate arbitrary
  scalar action or finite-field-extension hypothesis.
- There exists a nonzero s in R: `∃ (s : R) (hs : s ≠ 0), ...`.
- The principal localization R[1/s]: `Localization.Away s`, the recorded
  dependency's quotient localization at `Submonoid.powers s`.
- That localization is a field: `IsField (Localization.Away s)`.
  `IsField` asserts nontriviality, commutativity and inverses for every nonzero
  element of the existing ring, rather than choosing an unrelated ring structure.
- The stated embedding into K is
  `IsLocalization.Away.lift (S := Localization.Away s) s (g := R.subtype)
    (isUnit_iff_ne_zero.mpr (Subtype.coe_injective.ne hs))`.
  The proof argument transports s ≠ 0 through the injective subtype inclusion
  and uses the field criterion for units. Mathlib's lift is the unique extension
  of this inclusion, with its documented formula r/s^n ↦ r*s^(-n).
  `Function.Injective` states that this canonical map is an embedding.
- K is finite-dimensional over R[1/s] via that embedding: `RingHom.Finite`
  of the same canonical lift. By its definition this is `Module.Finite` for
  the algebra and module induced by that map. Since the base is asserted to be
  a field, this is precisely finite-dimensionality. No arbitrary module action
  or existentially chosen map is substituted for the canonical one.

Statement dependencies used, after opening their declarations and docstrings:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; the conclusion uses
  the compatible field predicate `IsField`, Mathlib.Algebra.Field.IsField.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  Mathlib.RingTheory.FiniteType; its body is `Algebra.FiniteType` for `f.toAlgebra`.
- `def-weil-ring-localization-away`: `Localization.Away`,
  Mathlib.GroupTheory.MonoidLocalization.Away; its ring structure and canonical
  lift are provided by Mathlib.RingTheory.Localization.Away.Basic.

The public imports supply these notions. The plain proof imports preserve the
accepted DAG proof plan: Mathlib.AlgebraicGeometry.Morphisms.FiniteType for the
pointwise locally-finite-type criterion and affine spectra;
Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact for quasi-compactness;
WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty for
`AlgebraicGeometry.exists_open_closed_subset_fibre_nonempty`;
Mathlib.RingTheory.Spectrum.Prime.Topology for
`PrimeSpectrum.isTopologicalBasis_basic_opens`,
`PrimeSpectrum.localization_away_isOpenEmbedding` and
`PrimeSpectrum.localization_away_comap_range`;
Mathlib.RingTheory.Ideal.Maximal for `Ideal.exists_le_maximal`; and
Mathlib.RingTheory.Jacobson.Ring for
`finite_of_finite_type_of_isJacobsonRing` (the Zariski lemma).
The module's theorem docstring includes every step of the accepted proof.

Edge cases checked before writing: s = 0 is explicitly excluded; a zero subring
cannot contain 1 in a field, so no missing nontriviality assumption is needed;
R = K and zero algebra generators allow s = 1 and a one-dimensional extension;
finite fields and all characteristics are included; proper nonfield subrings
are allowed, with no Noetherian, Jacobson or finite-presentation assumption.
A subring of K lives in K's universe, so a single explicit universe covers all
such actual subrings without a hidden universe equality assumption.

Searches made for an existing statement (all returned successfully):

- `msearch.py ... leanfinder`: "A field finitely generated as an algebra over a
  subring is finite over a principal localization of the subring which is a
  field". Hits were `Algebra.EssFiniteType.cond`, essential finite type
  localization interfaces, finite localization results, and local finite type
  criteria. None asserts a principal localization of the subring is a field.
- `msearch.py ... leansearch`: "A field finite type over a subring is finite over
  a principal localization which is a field". Hits were finite type localization
  preservation, the finite type property of an away localization, and essential
  finite type interfaces, not this existence statement.
- `msearch.py ... loogle`: "Algebra.FiniteType, IsLocalization.Away". The only
  hit was `Algebra.QuasiFinite.of_isIntegral_of_finiteType`; it has different
  hypotheses and conclusion and does not supply the required field localization.
- `msearch.py ... grep` in RingTheory:
  `exists.*(isField|is_field)|[Ff]ield.*[Ff]inite[Tt]ype|[Ff]inite[Tt]ype.*[Ff]ield`.
  The 21 hits concern quasi-finite, residue, smooth, and unramified algebras,
  maximal ideals or nonfield spectra; no exact match.
- `rg` over both lean/WeilConjectures and lean/Sheaf with the field/finite-type
  patterns, and an item-id search over lean/WeilConjectures, found no copy.
  `FiniteTypeFieldExtensionNeighbourhood` concerns descent after scalar extension,
  and `IsolatedPrimeResidueFinite` concerns isolated primes over a field.
  Neither states the field-over-subring assertion. A full-name search in those
  sources and dag/lean_names_upstream.json found no declaration name collision.

Validation: scompile.py compiled this file separately in both sandbox and library
module modes, against the server's published build, with no errors or warnings.
The only theorem has exactly the requested `sorry` proof. No node fault or
STATEMENT-DISPUTED flag is present.

## Second reading by Q69

This is an explicit second pass by the same worker; no separate agent was
started, as required by the dispatch brief. The maintainer supplies the
independent review. Reopened the node and module and checked each clause:
`Field K`, actual unital subring R, finite type of its inclusion, nonzero s,
the specific quotient localization, its field predicate, the canonical lift's
injectivity, and module finiteness through exactly that lift. The nonzero proof
is proof-only data determined by hs, not an extra assumption. RingHom.Finite
uses the lift's induced module structure, so there is no implicit unrelated
scalar action. The source proof's nonzero-domain and singleton-spectrum steps
are present in the docstring. No mathematical mismatch was found; no statement
or proof dependency was changed. The earlier stage-1 unchanged-node ending does
not apply: this stage-2 submission adds the previously absent lean record,
as explicitly authorized by coord/brief-stage2.md §0 and coord/queue.tsv.
