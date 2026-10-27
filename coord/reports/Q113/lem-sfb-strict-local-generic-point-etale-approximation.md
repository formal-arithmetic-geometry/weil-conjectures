## Worker report

The module `Sheaf.AlgebraicGeometry.StrictLocalGenericPointEtaleApproximation` states
`AlgebraicGeometry.strictLocalGenericPoint_etale_approximation`, with proof `sorry`.
It introduces no definition or auxiliary theorem. The node is copied with only its
`lean` field changed. Its natural-language statement, statement dependencies, proof,
and proof dependencies remain verbatim. All ten proof steps are included in the
statement docstring, with the original dependency citations.

Source checked: `literature/stacks-project/limits.tex`,
`lemma-descend-finite-presentation` (Tag 01ZM), including its morphism-descent clause
and affine reduction. This is the node's finite-coordinate specialization, not a
claim that 01ZM literally has this statement. Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
part (3). The lemma is a supporting trait approximation below that unit, and does
not alter the unit's statement or route.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The DVR `R` is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's DVR class is a local principal ideal
  ring with nonzero maximal ideal, under `IsDomain`.
- The chosen strict henselization `D` is `[CommRing D] [Algebra R D]` together
  with `P : Algebra.StrictHenselizationPresentationIn.{u, u} R κsep D`.
  The `κsep` field, residue-field algebra, `IsSepClosure`, `Algebra R κsep`, and
  residue scalar-tower binders are precisely the data of the dependency's
  pointed-etale-colimit definition. They do not assume an algebraic closure of
  the generic fraction field or perfectness of the residue field. `P` retains
  the given universal cocone and algebra identification, including the chosen
  structural map `algebraMap R D`.
- `K = Frac R` is `[Field K] [Algebra R K] [IsFractionRing R K]`.
  `F = Frac D` is `[Field F] [Algebra D F] [IsFractionRing D F]`, with
  `[IsDomain D]` recording the domain implicit in that fraction-field notation.
  For a strict henselization of a DVR this domain property follows from the
  strict-henselization DVR theorem; no DVR or henselian condition on `D` beyond
  the given presentation is postulated.
- The canonical `K`-structure on `F` is recorded by `[Algebra R F]
  [IsScalarTower R D F] [Algebra K F] [IsScalarTower R K F]`.
  The tower equations force agreement on `R`, and fraction-field uniqueness
  forces the canonical map on `K`; there is no unrelated choice of action.
- A finite-type `K`-scheme is `(V : Scheme.{u})
  (sV : V ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType sV] [QuasiCompact sV]`.
  This is exactly the recorded dependency convention for finite type.
- The given point is `(v : Spec (CommRingCat.of F) ⟶ V)`, and its being a
  `K`-morphism is `hv : v ≫ sV = Spec.map (CommRingCat.ofHom (algebraMap K F))`.
- The output DVR is existential `A : Type u`, its `CommRing`, `IsDomain` and
  `IsDiscreteValuationRing` instances; its fraction field is the actual Mathlib
  construction `FractionRing A`.
- The two ring maps are `i : R →+* A` and `j : A →+* D`. Their prescribed
  composite is `j.comp i = algebraMap R D`.
- The affine structural morphism is `Spec.map (CommRingCat.ofHom i)`.
  Its `Etale` predicate renders etaleness. Its `LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated` conjuncts render finite presentation
  in the precise Stacks 01TP convention fixed by the dependency node.
- `Function.Injective j`, `IsLocalHom j`, and `j.FaithfullyFlat` are exactly
  the three clauses on `A → D`. `IsLocalHom` reflects units; for local rings
  this says the maximal ideal maps into the maximal ideal, by
  `IsLocalRing.local_hom_TFAE` / `map_nonunit`.
  The local-ring structure of `D` is a property of the given strict
  henselization, so the statement needs no additional local-ring hypothesis.
- `k : K →+* FractionRing A` and `l : FractionRing A →+* F` are tied to `i`
  and `j` by the two restriction equations
  `k.comp (algebraMap R K) = (algebraMap A (FractionRing A)).comp i` and
  `l.comp (algebraMap A (FractionRing A)) = (algebraMap D F).comp j`.
  They are uniquely determined by these equations (`IsFractionRing.ringHom_ext`).
  Both are injective since their sources and targets are fields. The equations
  also imply `l.comp k = algebraMap K F`, using the two input tower identities
  and `j.comp i = algebraMap R D`. These maps therefore specify the canonical
  fraction-field embeddings, without replacing them by arbitrary maps.
- The descended point is
  `vA : Spec (CommRingCat.of (FractionRing A)) ⟶ V`.
  The equation `vA ≫ sV = Spec.map (CommRingCat.ofHom k)` makes it a
  `K`-morphism. The final equation
  `Spec.map (CommRingCat.ofHom l) ≫ vA = v` is exactly that its pullback
  along `Frac A → F` is the original point. An `L`-valued point of a
  `K`-scheme is an `L`-section of its base change, so composition with
  `Spec F → Spec L` is the standard point-base-change convention.
- No henselian hypothesis on `R`, no properness or separatedness condition on
  `V`, and no integral/finite hypothesis on `i` appears.

Dependency declarations used (read signatures and docstrings in source):

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing` (the `def-sc-discrete-valuation-ring` Mathlib leaf).
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn`, and its defining
  `Algebra.strictHenselizationPointedDiagramIn`; the presentation is used
  directly as `P`, not replaced with a private strict-henselization predicate.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `.QuasiCompact`: `LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- The convention-only `def-weil-pbc-scheme-conventions` has no declaration
  of its own: finite presentation is written out using
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` from
  Mathlib's morphism modules.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`:
  `Module.FaithfullyFlat`; the bare-map form `RingHom.FaithfullyFlat` is
  publicly imported from `Mathlib.RingTheory.RingHom.FaithfullyFlat` and
  installs precisely the module structure from `j.toAlgebra`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` is imported for
  `def-pc-base-change`; read `baseChange_morphism_projections` and
  `baseChange_section_characterization`. Its convention is the usual
  pullback of points/sections, which here is the displayed composition.
- `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`,
  `IsFractionRing`, and the unique fraction-field-lift characterization.

The modules recorded for stated proof dependencies are included as plain
imports. This includes the strict-henselization triples, etale local-ring
triples, strict-henselization DVR, pointed-etale filteredness, maximal-ideal,
and etale trait-stalk modules, plus the Mathlib modules carrying filtered
colimit representatives, DVR dimension, etale field algebras, localization,
PID torsion-free flatness, and local faithfully flatness. The local source of
`Sheaf.AlgebraicGeometry.StrictHenselizationDVR` currently contains its old
statement inside a withdrawal comment; its import remains in the proof plan,
but no unavailable declaration is used to type this statement. The delivery
has no missing statement notion and does not repair proof dependencies.

Edge cases checked before drafting:

- `V` empty: there is no field-valued morphism `v`, so the implication is
  vacuous without adding a `Nonempty V` hypothesis.
- Zero coordinate generators, e.g. `V = Spec K`: the conclusion can use
  `A = R` and the canonical fraction-field maps; the proof chooses any
  pointed stage by filtered nonemptiness. No positive-dimensional or
  nonempty-index hypothesis was introduced.
- Empty product in the principal-neighbourhood refinement: `f = 1` is
  allowed; the conclusion imposes no nontrivial localization.
- Nonhenselian `R` and imperfect residue fields: the presentation permits
  both; no `HenselianLocalRing R`, perfectness, or characteristic binder
  occurs. The field `R` and zero-ring `R` cases are excluded exactly by
  the node's DVR definition, not by a new condition.
- Nonproper, nonseparated finite-type `V` are allowed. A point factors
  through one affine chart; none of the statement's maps demands a
  properness extension to `Spec A`.
- The scheme/ring/index encodings share the arbitrary universe `u`.
  The strict-henselization test-algebra universe is `max u u = u`, never
  below that of the base; the existential stage `A` has that same size.
  There are no auto-bound variables (`set_option autoImplicit false`).

Searches made (2026-10-24):

1. `msearch.py ... leanfinder` with query
   "A point over the fraction field of a strict henselization of a DVR
   descends to the fraction field of an etale local DVR neighbourhood":
   8 hits, including `RingHom.Etale.ofLocalizationSpan`,
   `RingHom.Etale.ofLocalizationSpanTarget`, Henselian-ring statements,
   `Algebra.exists_etale_of_isEtaleAt`, and `Scheme.descResidueField`.
   Their displayed types concern localization etaleness, Hensel lifting,
   etale loci, or residue-field maps, not this approximation theorem.
2. `msearch.py ... loogle '"Etale", "IsDiscreteValuationRing"'`: 0 hits.
3. `msearch.py ... grep 'strictHensel|strict_hensel|henselization'
   RingTheory`: 0 Mathlib hits.
4. `msearch.py ... leansearch` with query
   "A point over the fraction field of the strict henselization of a DVR
   descends to an etale local DVR neighbourhood": 8 hits. These are
   Henselian ring properties, valuation lifting, etale-locus localization,
   and locality of etale maps; none states the approximation.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for strict henselizations,
   generic points, DVRs and fraction fields: existing presentation and
   inertia modules found, with no exact statement. Read
   `WeilConjectures/AlgebraicGeometry/Sites/StrictHenselizationGeneric.lean`:
   it proves the strict localization at a generic geometric point is a
   separably closed field, a different statement.
6. `rg` for the full item id in `lean/WeilConjectures` and for the selected
   declaration name in `dag/lean_names_upstream.json`, `lean/Sheaf`, and
   `lean/WeilConjectures`: no match. No existing declaration is duplicated.

Validation: the module-mode file was compiled through the prescribed
`scompile.py Q113 lem-sfb-strict-local-generic-point-etale-approximation ...`.
Both sandbox and library-path compiles passed. After adding the remaining
proof-dependency Mathlib imports, both compiles passed again (34.0 s and
3.7 s), with no errors or non-sorry warnings. All lines are at most 100
characters. The node record's `lean.statement` is extracted verbatim from
the theorem keyword through the signature before `:=`.

No statement correction, new node, or dependency module was required.
No statement dispute was found.

## Second reading by Q113

This is a second reading by the same dispatcher-started worker, not a claim
of an independent worker review: this assignment explicitly forbids starting
other agents and provides an independent maintainer review after delivery.
I reopened the node and module to check the following correspondences.

The DVR condition is the full `IsDomain` plus `IsDiscreteValuationRing`,
including the nonfield condition. The chosen `D` uses the recorded colimit
presentation and its actual `R`-algebra structure. The residue separable
closure binders are required by that exact dependency, rather than an added
geometric hypothesis. The fraction-field and scalar-tower binders ensure
that the input point has the prescribed `K`-structure. The domain on `D`
is inherent in `Frac D`, and a consequence of the strict-henselization DVR
property, not an assumption on a different class of local rings.

Finite type of `V` includes both local finite type and quasi-compactness.
For the output map of spectra I checked all four separate morphism-property
conjuncts: etale, locally finite presentation, quasi-compact, and
quasi-separated. The last three are precisely the node's finite-presentation
convention; neither etaleness alone nor merely local finite presentation was
substituted for it. The ring-map factorization and all three predicates on
`j` are present. Unit reflection is exactly maximal-ideal preservation on
these local rings.

Finally I checked the direction of every contravariant `Spec.map`: the
map induced by `l : Frac A → F` starts at `Spec F`, and its composite with
`vA` is the given `v`. Both fraction-field restriction equations are present,
so `l` cannot be an arbitrary field map; the `K`-morphism clause on `vA`
uses the similarly determined `k`. No equality to a point on an unrelated
base-changed scheme is substituted for this equality of maps to `V`.
All existence binders remain existential, and no henselian, properness, or
integrality assumption has slipped into the theorem. This reading found
no statement mismatch. It prompted adding the remaining recorded Mathlib
proof-dependency imports; the resulting module passed both server compiles.

Dry-run validation: `deliver2.py Q113 lem-sfb-strict-local-generic-point-etale-approximation --no-push` passed the server preflight and both per-file compilation checks (dry-run commit `9d6b2af1412`).
