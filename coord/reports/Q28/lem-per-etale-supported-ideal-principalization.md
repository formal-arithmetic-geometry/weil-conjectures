## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSupportedIdealPrincipalization` states
`AlgebraicGeometry.Scheme.IdealSheafData.exists_admissibleBlowup_isInvertible_comap_etale`.
Its only theorem has proof `sorry`; no definitions or auxiliary theorems are introduced.
The theorem docstring transcribes all five proof steps and names their dependencies.
The natural-language statement and its accepted split are unchanged.

Clause-by-clause correspondence:

- Schemes S and V: `{S V : Scheme.{u}}`, with the universe explicitly declared.
- S quasi-compact and quasi-separated: `[CompactSpace S] [QuasiSeparatedSpace S]`.
- Effective Cartier divisor on S: `D : S.IdealSheafData`, `hD : D.IsInvertible`.
  IdealSheafData retains the actual quasi-coherent ideal and closed subscheme.
  The recorded upstream IsInvertible is explicitly defined as affine-locally regular
  principal; it therefore states exactly the effective-Cartier hypothesis.
- U is S minus the support of D: every occurrence is the same `D.support.compl`.
  There is no independently chosen open or missing equality with this complement.
- U quasi-compact: `hU : IsCompact (D.support.compl : Set S)`.
- U schematically dense: `hdense : SchematicallyDenseOpen D.support.compl`.
  Opening the existing definition shows injectivity of restriction from every open W
  to W intersect U, precisely injectivity of the specified structure-sheaf morphism.
- Etale e: `(e : V ⟶ S) [Etale e]`.
- e quasi-compact and separated: `[QuasiCompact e] [IsSeparated e]`.
- e of finite presentation in the convention of Stacks 01TP: locally of finite presentation
  follows from Etale (via Smooth); quasi-compact is explicit; quasi-separated follows
  from IsSeparated (`Morphisms/Separated.lean`, instance at line 68). Thus all three
  components of finite presentation are present, despite Mathlib's weaker introductory
  prose in FinitePresentation.lean. No Noetherian substitute is used.
- V quasi-compact and quasi-separated: `[CompactSpace V] [QuasiSeparatedSpace V]`.
- A finite-type quasi-coherent ideal K: `(K : V.IdealSheafData)` and
  `hK : K.toModules.IsQuasiCoherentFiniteType`. The dependency's definition is exactly
  the conjunction `SheafOfModules.IsQuasicoherent K.toModules ∧
  SheafOfModules.IsFiniteType K.toModules`. The actual ideal module is the canonical
  `K.toModules`, not a chosen module or an abstract mono.
- K restricts to the unit ideal above U:
  `hunit : K.comap (e ⁻¹ᵁ D.support.compl).ι = ⊤`. Comap along this canonical open
  immersion is restriction, and top is the unit ideal of that open subscheme.
- Existence of a U-admissible blowup: `∃ B : IsAdmissible S D.support.compl`.
  Opening the upstream structure gives the quasi-coherent centre `B.I`, its
  finite-typeness `B.finiteType`, and disjointness of U from its closed support.
  This is equivalent to its restriction on U being unit. The scheme and morphism
  used in the conclusion are specifically `B.I.blowup` and `B.I.blowupMap`.
  Choosing the canonical blowup is an equivalent presentation of the existence
  claim: it supplies the specified identification by the identity isomorphism.
  Conversely any datum with a specified identification over S transports its ideal
  and invertibility to this canonical blowup. No centre or identification is discarded
  in favour of an arbitrary modification or a mere existence of a map.
- Fibre product: `pullback e B.I.blowupMap`, hence V times_S S1 in the stated order.
- Extended ideal with its actual inclusion: `K.comap (pullback.fst e B.I.blowupMap)`.
  This is the recorded ideal-sheaf extension along the projection to V, not tensor
  pullback without passage to its image.
- Invertibility, equivalently local generation by a nonzerodivisor:
  `(K.comap (pullback.fst e B.I.blowupMap)).IsInvertible`. The existing predicate
  spells out the latter affine-local condition. For an ideal with its inclusion,
  a rank-one free trivialization maps 1 to a regular generator by injectivity;
  conversely multiplication by a regular generator is an isomorphism from the ring
  to that ideal. Thus this single predicate renders both equivalent descriptions;
  it imposes no additional condition on an abstract module.
- No Noetherian or excellence hypothesis: there is no such binder or instance.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-scheme-conventions`: convention-only record. Its meanings are
  Mathlib's `CompactSpace`, `QuasiSeparatedSpace`, `QuasiCompact`, `IsSeparated`,
  `LocallyOfFinitePresentation`, and `QuasiSeparated`, with finite presentation
  interpreted as all three conditions, as above.
- `def-nagata-effective-cartier-ideal` and `def-nagata-invertible-ideal`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`,
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
  Both recorded interfaces are usable: for an actual ideal the node's locally
  free rank-one description is equivalent to the recorded regular-principal one.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; its affine-local definition and
  `Etale.iff_flat_and_formallyUnramified` give the node's meaning.
- `pqf-def-coherent`: `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`,
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`.
- `def-nagata-admissible-blowup`: `AlgebraicGeometry.IsAdmissible`,
  `WeilConjectures.Blowup.AdmissibleBlowup`.
- `def-nagata-global-blowup`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  `WeilConjectures.Blowup.Gluing`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.fst`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-nagata-extended-ideal`: `Scheme.IdealSheafData.comap`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`.
- Added the already landed `def-trf-schematically-dense-open` to stmt_deps, using
  `AlgebraicGeometry.SchematicallyDenseOpen` from
  `Sheaf.TraceFormula.SchematicallyDenseOpen`; no new notion is defined.

The stated proof dependencies are imported privately: module flattening, the Cartier
pullback comparison, the tensor/extended-ideal comparison, blowup complement,
module strict transform, the etale fibre theorem, and the free-neighbourhood theorem.
The etale base-change and qcqs permanence dependencies are Mathlib matches, already
available through the public Etale and QuasiSeparated imports. The proof dependency
`lem-trf-relative-flat-cartier-support` has no recorded Lean declaration, audit, or
Mathlib match; consequently there is no module of that node to import. It is cited
by name and its complete required use is explained in the theorem docstring.
It is a proof prerequisite, not a missing notion needed to type this statement.

Sources checked: local Stacks flat.tex at `theorem-flatten-module` (Tag 0815),
including its hypotheses and conclusion; the source modules and declaration
signatures/docstrings listed above; and the current blueprint's
`lem-per-artin-gabber-affine-curve.proof.md`, Step 3. The statement retains the
additional ideal/strict-transform comparison and rank-one argument explicitly
asserted in this node; it does not mistake module flattening alone for the conclusion.

Edge cases checked before writing:

- Empty S forces V empty; no nonemptiness assumption excludes this case.
- V or its fibre product can be empty; IsInvertible is pointwise and vacuous there.
- D can be the empty Cartier divisor (unit ideal), giving U = S. The supported-ideal
  hypothesis then gives K unit. The unit-centre blowup witnesses the conclusion.
- U empty with schematic density forces S empty; there is no illicit exclusion or
  use of a generic point. On a nonempty scheme the zero ideal cannot be Cartier.
- K zero on a nonempty component is disallowed only when forced by the actual unit
  restriction and Cartier density, rather than by an artificial nonzero hypothesis.
- Nonreduced schemes, zero-divisors away from a regular boundary equation, arbitrary
  characteristic, and non-Noetherian qcqs schemes remain allowed.
- The single arbitrary scheme universe u is the standard common universe of the
  recorded scheme-morphism and fibre-product APIs; no independent smaller universe
  makes a test-object condition vacuous. No field, test algebra, or index is restricted.

Searches for an existing statement (fresh msearch calls for Q28 and this item):

- LeanFinder: `A finite type ideal on an etale scheme becomes invertible after an
  admissible blowup of its base` — 8 results, etale localizations/etale-locus algebra;
  no base principalization theorem.
- Loogle: `"Etale", "Ideal", "IsInvertible"` — 0 results.
- LeanSearch: `Principalize a finite type quasi coherent ideal on an etale scheme
  by blowing up its base` — 8 results, etale base change, localization and algebra;
  no supported-ideal principalization theorem.
- Mathlib grep via msearch: `admissible.*blow|blow.*principal|flatten.*[Mm]odule|
  [Ii]nvertible.*[Ii]deal` — 23 hits, fractional/invertible-ideal algebra and unrelated
  material; no theorem producing this base blowup.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for principalization, supported ideals,
  admissible blowups and schematic density found centre principalization and module
  flattening, not this etale supported-ideal conclusion. The existing predicates
  IsAdmissible, IsInvertible, comap, IsQuasiCoherentFiniteType and SchematicallyDenseOpen
  are reused. The exact item-id search found no upstream declaration.
- Exact proposed declaration-name search in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json` found no existing declaration.

No statement correction, new node, dependency repair, or mathematical dispute was needed.
Validation: prescribed scompile.py compiled the module in both sandbox and library mode
cleanly, with no errors or unexpected warnings. Delivery preflight is run after this report.

## Second reading by Q28

A separate pass by this same dispatcher worker reread the actual node statement and
final Lean file. No other agent was started, as the dispatch brief prohibits that.
The independent maintainer review is still required by the delivery workflow.

The second pass checked the qcqs hypotheses for both schemes; the effective Cartier
ideal; the fixed complement U; compactness and injectivity on all open sections;
etale, quasi-compact, separated and full finite-presentation conditions on e;
the genuine finite-type quasi-coherent ideal K and its unit restriction; and the
existential canonical blowup with its retained finite-type centre. It then checked
that pullback.fst projects to V and that comap is the actual extended ideal, and
unfolded IsInvertible to see the nonzerodivisor clause. No clause, empty case,
Noetherian assumption, or arbitrary-map replacement was found. The existing
schematic-density node was added to stmt_deps; all original dependencies remain.

In particular, the IsAdmissible record packages a centre rather than an arbitrary
morphism equipped with a blowup isomorphism. Using that centre's actual canonical
blowup in this existential theorem supplies the missing morphism and identity
identification, so it does not require a duplicate definition or an interface repair.
The regular-principal predicate is also exact for ideals already equipped with their
inclusion. No mathematical statement changes were made during the second pass.
