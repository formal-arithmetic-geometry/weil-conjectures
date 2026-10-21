## Worker report

Attach the existing `Profinite.padicIntegersCondensedRing`, together with its
underlying commutative ring object and both inclusion maps, from
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, lines 118–150.
No module is added: only the item's `lean` record changes.

Read the whole item, its four statement dependencies and their recorded
declarations and docstrings, the current blueprint's
`sec-proetale-coefficients/sk-def-sfb-condensed-ring/def-sfb-padic-integers-condensed-ring.md`
and `.proof.md`, and the upstream constructions. No repair note exists for this
item. The requested CompactObject example has been withdrawn; its node now
records `WeilConjectures.CategoryTheory.CompactObject`, which was read instead.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- The prime and algebraic closure inherited from the subfield dependency are
  `(ℓ : ℕ) [Fact ℓ.Prime]` and `PadicAlgCl ℓ`. Mathlib
  `NumberTheory/Padics/Complex.lean:65–94` equips this algebraic closure with
  the extending norm (`PadicAlgCl.norm_extends`), not the completed algebraic
  closure `PadicComplex`.
- A field with a specified embedding is `(E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)]`. The map is `algebraMap E (PadicAlgCl ℓ)`;
  a ring map out of a field is injective. Conversely a unital field embedding
  into the commutative field supplies this algebra structure. No assumption
  that E contains ℚℓ is made here, nor finite-dimensionality or completeness.
- The restricted absolute value and topology are supplied by
  `PadicAlgCl.normedFieldOfAlgebra ℓ E`, which the abbreviation explicitly
  installs. In `WeilConjectures.NumberTheory.Padics.Extension:134–144`, this
  is `NormedField.induced` along the given embedding, so its norm is the
  ambient norm composed with that embedding and its topology is induced.
- The ring of integers is `PadicAlgCl.integers ℓ E`, a `ValuationSubring E`.
  Read `Padics/Extension.lean:146–183`: `valuationOfAlgebra` is the ambient
  valuation composed with the embedding; `integers` is its valuation subring;
  `mem_integers_iff` is definitionally
  `x ∈ integers ℓ E ↔ ‖algebraMap E (PadicAlgCl ℓ) x‖₊ ≤ 1`.
  The NNReal inequality is exactly the node's real norm-at-most-one condition.
  The inherited subtype topology is the subspace topology inside E, and
  transitivity of induced topologies gives the restriction from ℚ̄ℓ.
  The valuation subring already has commutative ring operations; the subtype
  topological-ring instance is available with the induced norm installed.
- The condensed ring is exactly `continuousMapRingSheaf (integers ℓ E)`.
  Its output is `Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}`.
  It is definitionally the recorded dependency
  `continuousMapRingSheafOfUniverse.{u, 0} (integers ℓ E)`, including its
  underlying presheaf and proof-irrelevant sheaf-condition field.
- For every `S : Profinite.{u}`, sections are
  `RingCat.of (ULift.{u + 1} C(S, integers ℓ E))` with pointwise operations.
  The lift implements the coefficient universe convention and changes no
  section. For `f : S' ⟶ S`, restriction is
  `a ↦ ULift.up (a.down.comp f.hom.hom)`. These are the literal upstream
  definitions in `Condensed/ContinuousMap.lean:77–94`.
- The underlying abelian sheaf is `Profinite.padicIntegersRingObj ℓ E`,
  defined by forgetting rings to abelian groups. Its canonical ring-object
  structure is commutative by the existing
  `Profinite.isCommMonObj_padicIntegersRingObj` instance, lines 139–142.
  The scratch consumer also identifies it with the dependency's actual
  `continuousMapRingObjOfUniverse.{u, 0}` and specializes the dependency's
  `isCommMonObj_continuousMapRingObjOfUniverse.{u, 0}` for its recorded
  `sfbSheafTensorStructure` and canonical `MonObj`.
- The arrow to the field is
  `Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E`.
  Its source and target are exactly this condensed ring and the recorded
  `Profinite.padicSubfieldCondensedRing ℓ E`. It applies the recorded
  `continuousMapRingSheafMapOfUniverse.{u, 0}` to
  `(integers ℓ E).subtype` and `continuous_subtype_val` by definitional
  equality. At a section a and point s it gives `(a.down s : E)`.
- The final clause adds `[Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]` only for
  `Profinite.padicIntCondensedRingToPadicIntegersCondensedRing ℓ E`.
  The tower says precisely that the embedding is ℚℓ-linear. Its source is
  the recorded `Profinite.padicIntCondensedRing ℓ`, its target is this item.
  It applies the recorded postcomposition construction to
  `AlgebraicGeometry.ProEtale.padicIntToIntegers ℓ E` with
  `AlgebraicGeometry.ProEtale.continuous_padicIntToIntegers ℓ E`.
  Read `RingObjects/EllAdic.lean:221–243`: this is the codomain restriction
  of the composition of `PadicInt.Coe.ringHom` with `algebraMap ℚ_[ℓ] E`.
  The image lies in the valuation ring by `PadicAlgCl.norm_extends` and
  the defining inequality for `PadicInt`. Continuity is induced-topology
  continuity. The section formula is exactly
  `((map.hom.app (op S) a).down s : E) = algebraMap ℚ_[ℓ] E (a.down s)`.

The four dependency interfaces used are:

1. `def-sfb-padic-subfield-condensed-ring`:
   `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
   `Profinite.padicSubfieldCondensedRing`.
2. `def-sfb-continuous-map-condensed-ring`:
   `Sheaf.Topology.ContinuousMapCondensedRing`,
   `Profinite.continuousMapRingSheafOfUniverse`,
   `continuousMapRingObjOfUniverse`, `continuousMapRingObjOfUniverseMonObj`,
   and `isCommMonObj_continuousMapRingObjOfUniverse` in namespace Profinite.
3. `def-sfb-continuous-map-condensed-ring-map`:
   `Sheaf.Topology.ContinuousMapCondensedRingMap`,
   `Profinite.continuousMapRingSheafMapOfUniverse`.
4. `def-sfb-padic-int-condensed-ring`:
   `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
   `Profinite.padicIntCondensedRing`.

Also read the proof-dependency Mathlib ultrametric criterion in
`Analysis/Normed/Field/Ultra.lean:140–143` and the p-adic integer definition
in `NumberTheory/Padics/PadicIntegers.lean:59–60`. No theorem or definition
is duplicated and no additional proof dependency needs a new declaration.

Edge cases checked: E need not contain ℚℓ (for example its prime subfield);
no finite-extension, completeness, discrete-valuation or uniformizer
assumption appears. E can be the full algebraic closure. Zero and one lie in
the valuation subring; the norm-one boundary is included. Empty S is allowed
by the unrestricted `Profinite` binder; its unique continuous function gives
the trivial section ring, and both postcomposition formulas still hold.
Every prime including 2 is allowed. The profinite universe u is arbitrary.
For E in any larger universe, injectivity into the Type-0 `PadicAlgCl ℓ`
implies `Small.{0} E` by `small_of_injective`; thus the small field model
used by the recorded subfield dependency excludes no embedded field.

Searches actually performed with the prescribed `msearch.py`:

- `leanfinder`, query “The valuation ring of a subfield of an algebraic
  closure of the p-adic numbers defines a condensed commutative ring of
  continuous maps with inclusions from the p-adic integers and into the
  field”: eight hits, including `PadicComplexInt`, `PadicAlgCl`,
  `PadicAlgCl.valued` and p-adic ring instances; none states this whole
  condensed-ring construction.
- `loogle`, query `PadicInt, ValuationSubring, Condensed`: zero hits.
- `grep`, query
  `padicIntegersCondensedRing|PadicAlgCl.integers|continuousMapRingSheaf`:
  zero Mathlib hits.
- `leansearch`, query “A topological commutative valuation ring of a
  subfield of an algebraic closure of the p-adic numbers gives a condensed
  ring of continuous functions on profinite sets”: eight hits, including
  `ValuativeTopology`, `TopCat.continuousFunctions`, `PadicComplexInt`,
  `ContinuousMap.instCommRingOfIsTopologicalRing` and `PadicAlgCl.valued`;
  these do not supply the whole condensed-ring construction.
- Direct `rg` in `lean/WeilConjectures` located the exact declaration
  at `CategoryTheory/RingObjects/Condensed/EllAdic.lean:121` and both
  inclusion maps at lines 127 and 147. A literal node-id search there gave
  no hit. The `dag/lean_names_upstream.json` name search gave no hit.
  Direct `rg` in `lean/Sheaf` found existing consumers in
  `Paper/CompletedCondensedCoefficients.lean` and four other files, all
  using this same upstream construction, not another definition.

Validation is a scratch consumer `scratchpad/Validate.lean`, outside the
delivered `lean/` tree, compiled only with `scompile.py`. It checks the
valuation-subring membership, topological-ring instance, equality with the
recorded sheaf, section and restriction formulas, both commutativity
interfaces, both maps' equality with the recorded postcomposition
construction, their section formulas, and smallness of an arbitrary-universe
embedded field. The scratch file disables auto-implicit variables.
An initial scratch style warning was fixed with `let`; an underdetermined
tensor size was resolved by specializing the dependency's commutativity
theorem at `.{u, 0}` and separately identifying its underlying sheaf.
The final scratch compile passed without warnings or errors: 12.6 seconds
in the sandbox context and 9.8 seconds in the library context.

No new node, dependency module, statement correction, hollow definition,
or statement dispute is needed. The maintainer supplies the independent review.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
