## Worker report

The module `Sheaf.AlgebraicGeometry.GenericGeometricallyReducedPreparation` states
`AlgebraicGeometry.exists_generic_geometricallyReduced_preparation`, with proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.
The node is unchanged outside its `lean` record.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 6718–6783,
Tag 0550, `lemma-make-generic-fibre-geometrically-reduced`, statement and full proof.
The node asks for the prepared base, reduced pullback, flatness, finite presentation,
and generic geometric reducedness; it does not ask for the source lemma's additional
explicit morphism from the reduction to the original restricted family.

Hypothesis and clause matching:

- Schemes and the morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`; the explicitly
  declared universe `u` is arbitrary.
- Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the conjunction
  recorded by `def-weil-finite-type-morphism`.
- Irreducibility, including nonemptiness, is `[IrreducibleSpace S]`.
- The open subset is `U : S.Opens`, with `(U : Set S).Nonempty`.
- The new integral affine scheme is `T : Scheme.{u}`, with `IsIntegral T ∧ IsAffine T`.
- Its map to the open is `q : T ⟶ U.toScheme`; `IsFinite q` renders finiteness.
- `(topologically IsHomeomorph).universally q` renders universal homeomorphism,
  exactly as recorded in the corresponding definition node.
- The composite to the original base is `q ≫ U.ι`. Thus `pullback f (q ≫ U.ι)`
  is exactly `X ×_S T`, and its `.nilradical.subscheme` is exactly the reduction.
  The structural map of this reduction to T is
  `(pullback f (q ≫ U.ι)).nilradical.subschemeι ≫ pullback.snd f (q ≫ U.ι)`.
  This actual composite, repeated literally, is the subject of every conclusion.
- `Flat` of that composite renders flatness. `LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated` of the same composite together render
  finite presentation, including all three conditions of the dependency's comparison clause.
- `∀ η : T, IsGenericPoint η Set.univ → ...` means the generic point of T.
  Existence and uniqueness follow from integrality and scheme sobriety, so this
  quantification neither excludes nor adds a case.
- `GeometricallyReduced (... .fiberToSpecResidueField η)` says the scheme-theoretic
  fibre, with its canonical morphism to Spec κ(η), becomes reduced over every
  field extension of κ(η). The recorded `def-pc-geometrically-irreducible`
  `mathlib_match.how` explicitly includes this geometric reducedness clause.
  Mathlib's GeometricallyReduced quantifies over field-valued points, equivalent
  over a field to quantifying over field extensions. No arbitrary substitute
  fibre, map, or predicate is introduced.

Dependency declarations read and used (paths below are module names):

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace`, `IsIrreducible`,
  `irreducibleComponents` (the item only uses irreducibility).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`
  (the item uses only the finite clause, not integral morphisms).
- `Mathlib.CategoryTheory.MorphismProperty.Limits`:
  `CategoryTheory.MorphismProperty.universally`, with
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`:
  `AlgebraicGeometry.topologically`, and `Mathlib.Topology.Homeomorph.Defs`: `IsHomeomorph`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.nilradical`;
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, `.subschemeι`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `.fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Geometrically.Reduced`:
  `AlgebraicGeometry.GeometricallyReduced`.

These are imported publicly, directly or through the listed public imports.
Already stated proof dependencies are imported nonpublicly: `Mathlib.RingTheory.FiniteType`,
`Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.FieldTheory.PurelyInseparable.Basic`,
and `Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation`. The latter's declaration
`AlgebraicGeometry.exists_nonempty_open_flat_finitePresentation_restrict` and full
proof docstring were read. Other proof-only nodes have no recorded declaration yet;
no substitute declaration or import is invented. The five-step proof in the docstring
reproduces all five node proof steps and their non-elementary citations.

Edge cases checked: an empty X and empty generic fibre are allowed (geometric
reducedness does not assert nonemptiness); S cannot be empty because irreducibility
includes nonemptiness. S may be nonreduced, non-Noetherian, or nonaffine. Neither f
nor X is assumed separated or quasi-separated. The conclusion's quasi-separatedness
is retained as a genuine condition. T is nonempty by integrality. Characteristic zero
and positive characteristic are both included, with no characteristic hypothesis.
The universe is explicit, and geometric reducedness uses Mathlib's standard
same-universe scheme predicate rather than a quantifier in a smaller universe.

Searches actually run:

- `msearch.py ... leanfinder`: "A finite type morphism over an irreducible scheme
  admits a finite universal homeomorphism making the reduction flat finitely
  presented with geometrically reduced generic fibre". Eight hits included
  `finite_appTop_of_universallyClosed`, `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`,
  `UniversallyOpen.of_flat`, `Flat`, `isField_of_universallyClosed`,
  `Algebra.Smooth.exists_finiteType`, the finite-dimensional affine-space local
  presentation instance, and `IsIntegral`. None constructs the prepared family.
- `msearch.py ... loogle`: `"GeometricallyReduced", "IsFinite"`: zero hits.
- `msearch.py ... leansearch`: "finite universal homeomorphism reduced base change
  flat geometrically reduced generic fibre": unavailable, Internal Server Error.
- `msearch.py ... grep`: `generic.*reduc|reduc.*generic`, subdirectory
  `AlgebraicGeometry`: six hits, all generic-point occurrences in Geometrically/Reduced,
  FunctionField, or Properties; none states the preparation lemma.
- `rg` in the upstream `WeilConjectures` tree for `generic.*reduc|reduc.*generic|Generic.*Reduc|Reduc.*Generic`:
  generic-point, generic irreducibility and component results, no preparation theorem.
  `grep -rn` for the item id there returned no match. `tools/lean_names_upstream.py show`
  was also run; no item-specific matching declaration was identified.
- `rg` in `lean/Sheaf` for generic reducedness and `GeometricallyReduced` found
  reduced-flat affine preparation and geometric generic-fibre lemmas. The former's
  signature does not supply the finite inseparable extension or geometrically reduced
  generic fibre. Existing statements requiring generic geometric reducedness as input
  do not establish the item. No existing exact statement was found.

Validation: `scompile.py` compiled the delivered module cleanly on the server,
nice 19, two threads, 60 seconds per file (reported runtime 1.3 seconds).
No local compiler or library build was run. No disputed statement was found.


## Second reading by NB

I independently read the repository node, its sandbox copy, the entire delivered
module, and Stacks `more-morphisms.tex`, Tag 0550,
`lemma-make-generic-fibre-geometrically-reduced` (statement and proof, lines
6718–6783). The source assumes precisely finite type and an irreducible base;
there is no standing Noetherian, reduced, separated, affine, or characteristic
hypothesis. The node requests a subset of the source's conclusions: it omits
clause (5), the finite universal homeomorphism from the reduced source to X_V.
The delivered Lean follows the node and does not add this clause.

Independent inventory and clause-by-clause verdicts (all PASS):

1. Objects X and S, schemes, and f : X → S: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   The explicit universe `u` is arbitrary; no extra structure on either scheme.
2. Finite type of f: `[LocallyOfFiniteType f] [QuasiCompact f]`, precisely the
   conjunction in `def-weil-finite-type-morphism`, not finite presentation.
3. Irreducibility of S: `[IrreducibleSpace S]`. The definition extends
   preirreducibility with `Nonempty S`, matching the node's convention.
4. A nonempty open U of S: `∃ U : S.Opens, (U : Set S).Nonempty ∧ ...`.
   Affineness of U is not added as a requirement in the statement.
5. An integral affine S': `∃ T : Scheme.{u}, IsIntegral T ∧ IsAffine T ∧ ...`.
   Integrality includes nonemptiness and reducedness, and affineness means the
   canonical map to Spec of global sections is an isomorphism. These are the
   standard scheme notions, not assumptions about an arbitrary coordinate ring.
6. A finite universal homeomorphism to that same U:
   `∃ q : T ⟶ U.toScheme, IsFinite q ∧
   (topologically IsHomeomorph).universally q ∧ ...`.
   `IsFinite` includes `IsAffineHom` and finite coordinate-ring maps.
   `universally` checks all pullback squares; `topologically IsHomeomorph`
   checks the underlying map is continuous, open and bijective. Thus this is
   exactly the recorded definition, including surjectivity after base change.
7. The specified Y = (X ×_S S')_red, with its canonical map to S': write
   `P = pullback f (q ≫ U.ι)` only as explanatory prose here. The Lean uses
   `P.nilradical.subscheme` as the domain and
   `P.nilradical.subschemeι ≫ pullback.snd f (q ≫ U.ι)` as the structural map.
   The nilradical is `.radical ⊥`; the subscheme is constructed by gluing the
   affine quotients, and `subschemeι` is its canonical inclusion. No independent
   existential source, arbitrary map, or private reduction is substituted.
8. Flatness over S': `Flat` of this exact structural composite. The recorded
   affine definition is equivalent to flatness of every local-ring map by
   `Flat.iff_flat_stalkMap`.
9. Finite presentation over S': `LocallyOfFinitePresentation`, `QuasiCompact`,
   and `QuasiSeparated` of this same composite. All three are necessary for
   the finite-presentation comparison clause of the dependency node.
   `QuasiSeparated` means the diagonal is quasi-compact; it is a conclusion,
   not an extra input assumption.
10. Generic point η' of S': `∀ η : T, IsGenericPoint η Set.univ → ...`.
    `IsGenericPoint` means the closure of the singleton is the whole space.
    An integral scheme is irreducible and sober, so its generic point exists
    and is unique. The universal conditional is therefore equivalent to the
    node's assertion at the generic point and is not vacuous.
11. Geometric reducedness of Y_η': `GeometricallyReduced` of the same
    structural composite's `.fiberToSpecResidueField η`.
    `Scheme.Hom.fiber` is the pullback along `T.fromSpecResidueField η` and
    `fiberToSpecResidueField` is its second projection. `GeometricallyReduced`
    unfolds to `geometrically IsReduced`; over Spec κ(η),
    `geometrically_iff_of_commRing` quantifies over field extensions via
    `[Algebra κ(η) K]`. This matches every field extension in the node, not
    just reducedness over κ(η) or over its separable closure.

Dependency verification: I opened every statement dependency node, including
its `lean` record or `mathlib_match`, and the actual defining signatures in
Mathlib: `LocallyOfFiniteType`, `QuasiCompact`, `IrreducibleSpace`, `IsIntegral`,
`IsAffine`, `IsFinite`, `MorphismProperty.universally`, `topologically`,
`IsHomeomorph`, `pullback`, `pullback.snd`, `Scheme.nilradical`,
`IdealSheafData.subscheme`, `subschemeι`, `Flat`, `LocallyOfFinitePresentation`,
`QuasiSeparated`, `Scheme.Hom.fiber`, `fiberToSpecResidueField`,
`GeometricallyReduced`, and `geometrically`. The reducedness clause is explicitly
included in `def-pc-geometrically-irreducible`'s Mathlib match. None of these
records needs a substitute or a dependency module. There are no new definition
nodes, dependency modules, or statement corrections in this delivery.

I also read `GenericFlatFinitePresentation.lean`, including
`exists_nonempty_open_flat_finitePresentation_restrict`: its input is finite
type over an integral scheme, and its output is flatness and local finite
presentation on a nonempty open, exactly what proof step 5 uses. The other
recorded proof dependencies that have declarations are imported from Mathlib.
Unstated proof-only dependencies are not invented. The theorem's docstring
retains the node's five steps, including denominator scaling, the characteristic
zero case, the universal-homeomorphism criterion, reduction at the generic
fibre, and the final simultaneous shrinking for finite presentation.

Edge cases: empty X and empty generic fibre are allowed, since reducedness
and geometric reducedness do not imply nonemptiness. Empty S is excluded
exactly by the node's irreducibility hypothesis; empty T is excluded exactly by
integrality. Nonreduced and non-Noetherian S are permitted. No quasi-separatedness
or separatedness of f or X is assumed. Characteristic zero and all positive
characteristics are included; no characteristic instance is added. There is
no index type or integer parameter, so empty-index and n = 0 cases impose no
restriction. All schemes and field tests use the same arbitrary universe u,
following the recorded Mathlib geometric predicate; there is no independent,
smaller test universe. Schemes from different universes can be represented
in a common larger universe.

Independent searches, with different wording from the worker:

- `msearch.py ... leanfinder`: “Elimination of nilpotents after radicial
  alteration of an irreducible base yields a flat finitely presented model
  with reduced geometric generic fiber”. Eight hits: algebraic geometric
  reducedness, its descent to subalgebras, reduced normalization, reduced
  unramified algebras, and affine reducedness. None constructs this family.
- `msearch.py ... loogle`: `"GeometricallyReduced", "Flat"`. Four hits:
  reducedness over a reduced locally Noetherian base, two reduced-pullback
  instances, and reducedness over a base with finitely many components.
  All assume geometric reducedness; none prepares the base.
- `msearch.py ... grep`: `inseparab|radicial|homeomorph` in
  `AlgebraicGeometry/Geometrically`: six hits concerning existing geometric
  properties, no preparation theorem.
- `rg` on upstream `WeilConjectures` and the project's `lean/Sheaf` for
  `GeometricallyReduced`, `geometricallyReduced`, and geometric-reduction
  wording. I opened the closest project declarations:
  `exists_generic_radicial_geometrically_reduced_model`,
  `exists_radicial_generic_reduced_preparation`,
  `exists_radicial_reduced_flat_generic_fibre`, and
  `exists_reduced_flat_affine_preparation`. The first three require an affine
  source and/or geometrically irreducible generic fibre; the last does not
  assert generic geometric reducedness. Their signatures are not this node.
  Upstream's perfect-field and smooth-morphism results likewise have extra
  hypotheses. No exact existing statement was found.

Mismatches found: none. Changes: appended this independent reading and its
search evidence; retained the Lean module and node record verbatim. The module
has one theorem with proof `sorry`, no definitions or proved auxiliary results,
no file-local notation or instances, and no line longer than 100 characters.
All variables and universe u are explicitly bound. The module and theorem
have their required source/blueprint docstrings. I checked programmatically
that `lean.statement` is verbatim the theorem signature in the module.

Second-reader validation: `scompile.py NB lem-pur-generic-geometrically-reduced-preparation` compiled the sole delivered
module cleanly on the server in 1.3 seconds, nice 19, two threads,
60 seconds per file. No local compiler or global build was invoked.
