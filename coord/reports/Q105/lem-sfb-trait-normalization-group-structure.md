## Worker report

The module `Sheaf.AlgebraicGeometry.TraitNormalizationGroupStructure` states
`AlgebraicGeometry.TraitNormalization.existsUnique_group_structures` with one `sorry`.
The node statement, statement dependencies, proof and proof dependencies are unchanged.
The four concrete helper definitions bundle the existing canonical schemes and maps
in `Over S`; they introduce no independent mathematical notion or choice.

Clause-by-clause reading (all names below are in `AlgebraicGeometry.TraitNormalization`):

- `V : Type u`, `[CommRing V] [IsDomain V] [IsDiscreteValuationRing V]` is the
  specified DVR. `L : Type u`, `[Field L] [Algebra V L] [IsFractionRing V L]`
  gives its fraction field and canonical map. The residue field is exactly
  `IsLocalRing.ResidueField V`, with quotient map `IsLocalRing.residue V`.
- `G : Over (Spec (.of V))`, `[GrpObj G]` supplies the V-scheme, multiplication,
  identity, inverse and all group diagrams. This is an arbitrary group object,
  with no commutativity assumption.
- `[Flat G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`
  renders the three structural properties of G. Finite type is the conjunction
  of locally finite type and quasi-compactness, as the recorded dependency requires.
- `reduction G` is literally `Over.mk (G.left.nilradical.subschemeι ≫ G.hom)`.
  Hence its underlying scheme is precisely H = G_red. `reductionι G` is the
  actual nilradical subscheme inclusion j, bundled over the base using `Over.homMk`.
- `normalization G` is literally the recorded componentwise normalization of H,
  with its canonical composite structure map. `normalizationπ G` is exactly
  `H.fromReducedNormalization`, bundled over the base; it is not an arbitrary
  finite map or arbitrary normal cover.
- The four structural instances on each of `(reduction G).hom` and
  `(normalization G).hom` render flatness, separatedness and finite type of H and N.
- `[IsFinite (normalizationπ G).left]` renders finiteness of nu.
- The first `GeometricallyReduced` instance is on `pullback.snd H.hom eta`,
  where eta is `Spec.map` of `algebraMap V L`. This is exactly H_L over L.
- The second such instance is on `pullback.snd N.hom s`, where s is `Spec.map`
  of the residue quotient. This is exactly N_k over the residue field.
  Mathlib's `GeometricallyReduced` quantifies over field-valued base changes;
  over a field these are precisely field extensions with their structure maps.
  Its `IsReduced` is scheme reducedness, not a condition just on rational points.
- The first conclusion says `IsIso ((Over.pullback eta).map (normalizationπ G))`.
  This is the canonical nu_L, not an unnamed isomorphism between the two fibres.
  An isomorphism in the over category is exactly an isomorphism over L.
- The second conclusion `∃! hH : GrpObj (reduction G), ...` states uniqueness of
  the group structure on H making the actual j a homomorphism. Its `IsMonHom`
  explicitly uses `hH.toMonObj` and the original structure on G.
- The third conclusion applies to every H group structure for which j is a
  homomorphism (the preceding clause supplies exactly one). It says
  `∃! hN : GrpObj (normalization G), ...`, with `IsMonHom` explicitly using
  `hN.toMonObj` and `hH.toMonObj`. This states uniqueness of the N group structure
  making nu a homomorphism; it does not assert only uniqueness among H structures
  that happen also to admit an N structure.
- `IsMonHom` preserves identity and multiplication; for group objects it also
  preserves inverse by Mathlib's `CategoryTheory.GrpObj.inv_hom`.
  Base change preserves group objects and homomorphisms (`Functor.mapGrp`).
  Consequently the first and third conclusion together say precisely that nu_L
  identifies the base-changed group structures. There is no additional choice of
  a generic-fibre group law: the law on N_L is the transport through nu_L.
- There is no affine, connected, henselian, complete, excellent, perfect-field,
  residue-characteristic or commutativity hypothesis. A common universe for the
  base, fraction field and schemes is the usual schemes convention; any larger
  fraction-field model is isomorphic to one in the base universe.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; its signature includes the
  domain assumption, principal ideal and local structures, and nonfield clause.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, with its affine characterization.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, publicly imported through the
  recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in the recorded finite-type module.
- `def-weil-pbc-scheme-reduction`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`, from
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and its Basic import.
- `def-weil-pbc-reduced-normalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization` in `Sheaf.AlgebraicGeometry.ReducedNormalization`.
  Its construction is the coproduct of function-field normalizations of the
  reduced irreducible components, including the empty coproduct.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-pc-base-change`: the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` explicitly uses
  `CategoryTheory.Over.pullback` for schemes and maps. We use that same functor.
- Additional Mathlib APIs: `GrpObj`, `IsMonHom`, `GrpObj.inv_hom` and
  `Functor.mapGrp` from the cartesian group-object modules;
  `GeometricallyReduced` from `Mathlib.AlgebraicGeometry.Geometrically.Reduced`.

Every proof-dependency module currently recorded is imported nonpublicly unless
already a public statement import. The Mathlib matches for Noetherianity, flatness,
finite type, smoothness, going down, components and properness are also imported.
The two proof nodes `lem-sfb-smooth-normal-ascent` and
`lem-sfb-componentwise-normalization-generic-properties` have neither usable Lean
records nor Mathlib matches in the read clone, so there are no modules of those
nodes to import. They are not needed to type this statement and have not been
silently replaced by hypotheses. The proof docstring reproduces all eight DAG
steps, including the separate valuative lift of the identity.

Edge cases checked before writing: an empty total group scheme cannot carry
`GrpObj` over the nonempty spectrum of a DVR, since its unit would be a section.
An empty special fibre of G is likewise excluded by the identity section;
this is a consequence of `GrpObj`, not an extra hypothesis. The reduction has
the same underlying space and the componentwise normalization is surjective,
so their special fibres are nonempty as well. No separate nonemptiness
hypothesis is introduced.
Disconnected, nonaffine and noncommutative group schemes remain allowed.
Imperfect residue fields and all residue characteristics remain allowed.
The trivial group scheme over V gives the identity normalization and identity
maps in the conclusion. Nonreduced G is permitted; the geometric reducedness
hypothesis is imposed only on H_L. A field is excluded exactly by the DVR
not-a-field clause of the dependency, not by an extra hypothesis.

Searches (the raw service output is in the sandbox `searches.jsonl`):

- `msearch.py leanfinder`: "Finite normalization of a flat group scheme over a
  discrete valuation ring has a unique compatible group structure" returned
  relative morphism-normalization APIs, not this theorem.
- `msearch.py loogle`: "GrpObj, IsMonHom" returned no hits (unqualified GrpObj
  not found by the search service); their actual source definitions were read.
- `msearch.py leansearch`: "A unique group scheme structure on the finite
  componentwise normalization over a discrete valuation ring" returned the
  relative normalization APIs and unrelated normalization monoids, no match.
- `msearch.py grep`: "normalization|normalisation" in `AlgebraicGeometry/Group`
  returned zero hits; "reducedNormalization|normalization.*GrpObj|GrpObj.*normalization"
  across Mathlib returned zero hits.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no occurrence of the target id or proposed declaration names, and no
  matching normalization-group theorem. A broad group-object search found
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Reduced`; reading it shows its
  reduction bundles are specialized to a field, and its group structure needs
  a perfect field. They cannot apply to Spec V. The present helpers merely
  bundle the recorded general-scheme constructions without redefining them.

Source read: online Prasad--Yu PDF, Appendix A.4 proof, printed p.29,
https://math.stanford.edu/~conrad/papers/qrg.pdf, including Remark A.3 on p.28.
No statement fault or STATEMENT-DISPUTED flag is needed.

Validation: prescribed `scompile.py Q105 lem-sfb-trait-normalization-group-structure`
compiled both sandbox and library module modes cleanly, 2.1 seconds each.
Only the main theorem is postponed; all four helper definitions have real data.

## Second reading by Q105

A second self-reading was performed with the node and final module open; no
independent agent was started, following the dispatcher's explicit instruction.
The maintainer's independent delivery review is still required. The reading
checked each structural hypothesis on all three schemes, both distinct fibre
hypotheses, the actual canonical maps, and both separate uniqueness claims.
It also checked that inverse preservation and the generic group identification
are consequences of the selected Mathlib interfaces, not missing geometric
conditions. The self-reading corrected the edge-case discussion: a scheme living only
over the open generic point has no identity section over V and is not a group
scheme over V. The Lean statement already handled this correctly. No node
correction was made.
