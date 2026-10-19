## Worker report

The module `Sheaf.TraceFormula.ReducedFibreModification` states
`AlgebraicGeometry.exists_reduced_fibre_modification`, with one `sorry` and no definitions.
It formalizes the source-based corrected node, not the false dense-open clause of the old
node. The correction, counterexample and complete citer audit appear below.

Hypotheses and clauses, with the node and Lean file open:

- Integral base: `{S X : Scheme.{u}} [IsIntegral S]`. This includes nonemptiness of S.
- Quasi-compact and quasi-separated base: `[CompactSpace S] [QuasiSeparatedSpace S]`.
  On schemes these are exactly the finite-affine-cover and compact-intersection conditions.
- Generic point and function field: `(η : S) (hη : IsGenericPoint η Set.univ)`.
  The field `S.residueField η` is k(S); the canonical map is
  `S.fromSpecResidueField η`. An arbitrary generic point is bound, rather than a
  private choice of function field or generic point.
- Dominant morphism: `(f : X ⟶ S) [IsDominant f]`, the dense-image class.
- Finite presentation of f: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`; the latter two conditions are essential, not omitted.
- Geometric reducedness of its generic fibre:
  `[GeometricallyReduced (f.fiberToSpecResidueField η)]`. The fibre projection has domain
  `pullback f (S.fromSpecResidueField η)`. Mathlib's geometric reducedness tests all maps
  from spectra of fields, precisely all extensions of the generic field in this case.
- Integral altered base: `∃ (S' : Scheme.{u}) (_ : IsIntegral S') (r : S' ⟶ S)`.
- Proper surjective alteration: `IsProper r ∧ Surjective r`.
- Finite separable generic field: existential `L : Type u`, `Field L`,
  `Algebra (S.residueField η) L`, with `Module.Finite (S.residueField η) L` and
  `Algebra.IsSeparable (S.residueField η) L`.
- Its *whole* generic fibre is Spec L over k(S):
  `e : r.fiber η ≅ Spec (CommRingCat.of L)` and the equality
  `e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)) =
  r.fiberToSpecResidueField η`. Thus this is not merely an abstract scheme isomorphism
  or a field extension unrelated to r.
- Finite map with the specified target:
  `∃ (Y' : Scheme.{u}) (q : Y' ⟶ pullback f r), IsFinite q ∧ ...`.
- Actual generic invertibility of q: the `IsIso` condition on the underlying arrow of
  `(Over.pullback (e.inv ≫ r.fiberι η)).map (Over.homMk q rfl)`.
  Here `e.inv ≫ r.fiberι η : Spec L ⟶ S'` is the induced generic map, and q is a
  morphism over S' from structure map `q ≫ pullback.snd f r` to `pullback.snd f r`.
  This is the canonical induced base-change arrow, not an arbitrary isomorphism
  between the fibre products.
- Flatness: `Flat (q ≫ pullback.snd f r)`.
- Finite presentation of the new family: the three conjuncts
  `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` on that same composite.
- All reduced geometric fibres: `GeometricallyReduced (q ≫ pullback.snd f r)`.
  Mathlib's field-test definition is equivalent to reducedness over algebraic closures
  of all residue fields; no choice of algebraic closure restricts the quantifiers.
- No normality, Noetherianity, dimension, or flatness assumption on f is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`,
  `AlgebraicGeometry.IsReduced` (definitions of all integral/reduced schemes).
- `Mathlib.Topology.Sober`: `IsGenericPoint` (closure of the singleton is the specified set).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (affine-local presentation).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded bundle uses
  `Limits.pullback`, its projections and `Over.pullback` for scheme and morphism base
  change. I read the complete current module using `scompile.py --source`, because
  the older slopmaster2 checkout does not contain it. Its module-base-change declaration
  is for modules, so the statement correctly uses its documented scheme convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`;
  also `AlgebraicGeometry.IsDominant` for the expressly defined dominance condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, for the geometric fibres as recorded by
  `def-weil-geometric-fibre`.
- `Mathlib.AlgebraicGeometry.Geometrically.Reduced`: `GeometricallyReduced`, reusing the
  geometric field-test predicate rather than defining a second notion. The underlying
  `geometrically` quantifies over field spectra and arbitrary pullback squares;
  `geometrically_iff_forall_fiberToSpecResidueField` identifies the fibrewise meaning.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`; `Module.Finite` expresses
  finite degree. These implement the node's already specified finite separable extension.

The two former definition dependencies `def-trf-modification` and
`def-trf-schematically-dense-open` are removed only because the corrected statement
no longer uses their stronger notion. Their recorded declarations and docstrings were
read in full; they are usable for ordinary modifications, but cannot express Temkin's
§3.5 finite generic modification of a possibly nonflat target.

Proof-only imports retain all stated proof-dependency modules:
`Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback`,
`Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`,
`Sheaf.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree`, and the Mathlib
quasi-separatedness and universal-injectivity modules. Other Mathlib proof dependencies
are already public statement imports (flatness, properness and finiteness).
The currently unrecorded proof prerequisites finite eta flatification, valuation reduced
fibre normalization, finite eta spreading, qcqs Riemann–Zariski refinement, and finite eta
gluing have no module to import. They are only proof prerequisites, not missing notions
needed to type this statement. The theorem docstring contains all nine proof steps and
their dependency IDs.

Edge cases checked before writing:

- The integral base is nonempty. Empty X is incompatible with dominance, as it should be.
- Individual geometric fibres may be empty; `IsReduced` permits them.
- S a field and f geometrically reduced: identity alteration, L=k(S), and identity q
  satisfy the conclusion. Degree-one extensions are permitted.
- Nonseparated X and arbitrary dimension remain permitted; finite presentation includes
  quasi-separatedness but does not require separatedness.
- No perfection or characteristic-zero hypothesis is imposed. `Algebra.IsSeparable`
  is the correct finite-extension condition in positive characteristic too.
- Nonflat input with a vertical component is allowed by the corrected conclusion;
  the finite generic map can discard that component. This detects the original error.
- Schemes, residue fields, test fields and the finite extension share universe u,
  matching Mathlib's scheme universe convention. No independent smaller universe of
  test fields can make geometric reducedness vacuous, and finite extensions admit a
  representative in the same universe.

Searches for an existing theorem:

- `msearch.py ... leanfinder`: dominant finitely presented morphism, geometrically reduced
  generic fibre, flat reduced-fibre finite modification after separable alteration.
  Eight hits, including `Algebra.IsGeometricallyReduced.of_forall_fg`,
  `Algebra.Smooth.exists_finiteType`, and reducedness of normalization; no existence theorem.
- `msearch.py ... loogle '"GeometricallyReduced"'`: twelve hits, the predicate and its
  base-change/flat-total-space consequences; none constructs the alteration and finite map.
- `msearch.py ... grep 'reduced.?fib(re|er)|reducedFibre|reducedFiber' AlgebraicGeometry`:
  only `Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean`, the preservation API.
- Direct `rg` searches in upstream `WeilConjectures` and project `lean/Sheaf` for the node
  ID and reduced-fibre spellings found slicing and reduced-fibre preservation, limit
  descent, and consumers such as `ValuationCurveFiniteNormalization`; none states this
  theorem. Searches for `reduced_fibre_modification|reducedFibreModification` in the
  upstream-name index and both source trees also found no declaration.
- `msearch.py ... leansearch`: the same plain-language existence query returned eight
  hits: smooth implies local finite presentation, the flat affine criterion, dominance,
  and extensionality for dominant maps. No alteration or reduced-fibre existence theorem.

Validation: prescribed `scompile.py Q01 lem-trf-reduced-fibre-modification` compiled
this delivered module cleanly, including its canonical `Over.pullback` arrow.
No helper definition, extra theorem, extra axiom or auto-bound implicit was introduced.

## Statement corrected

The original statement is preserved verbatim in `statement_change.old_statement` in
the delivered node. Its false clause required a schematically dense open U in the whole
possibly nonflat target X×S S', with schematically dense inverse image, over which q
is an isomorphism. All other mathematical hypotheses and conclusions are retained.

Counterexample: let S=Spec k[t], and X be the disjoint union of S and the closed point
Spec k over t=0. This is dominant and finitely presented with geometrically reduced
generic fibre Spec k(t). After any proper surjective alteration r:S'→S with integral S',
the pulled-back vertical component V(t) is nonempty, while t is nonzero at the generic
point of S'. Schematic density of U in the target forces its intersection with this
vertical component to be nonempty. Isomorphism over that open would give a nonempty
open of the flat source on which the nonzero base element t acts as zero. Flatness over
the integral base makes multiplication by t injective on such local rings, a contradiction.

The correction follows the primary PDF
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf,
§3.5 opening paragraph (printed p. 20), Theorem 3.5.5 and Step 0 (printed pp. 21–22).
The opening paragraph explicitly interprets the relevant eta modification as a proper
morphism whose induced generic-fibre map is an isomorphism. This is distinct from the
stronger definition for flat multipointed curves in §1.2. Finite maps are proper, so
`IsFinite q` and the actual induced generic `IsIso` render exactly the needed conclusion.
This is a supporting tool node, not the blueprint unit's own statement. Its
`blueprint.is` is null, so the authorized §1(C) correction applies.

The node's proof steps 1, 7, and 8 lose only their unsupported dense-open assertions.
No proof dependency is removed or added. Removing the two now-unused statement
dependencies is recorded by `old_stmt_deps`; the original proof is in `old_proof`.

Full citer audit: `rg -l '"lem-trf-reduced-fibre-modification"' dag/nodes`, followed by
checking actual `stmt_deps` and `proof_deps`, found exactly two citers. Other textual
hits are historical blueprint ancestry references, not dependency edges.

- `lem-trf-valuation-curve-finite-normalization`: holds true. Its proof step 2 uses the
  proper separable alteration, finite generic isomorphism and flat finitely presented
  reduced geometric fibres. All remain. Its input is already flat and integral.
- `lem-trf-valuation-curve-projective-preparation`: holds true. Both applications use
  the same retained conclusions. They concern flat families; any schematic density
  needed later follows independently from their flatness, rather than the deleted
  nonflat-target assertion.

No citer is edited.

Related node fault reported for maintainer review: the proof prerequisite
`lem-trf-finite-eta-flatification` itself currently asserts the same impossible
schematically dense target open for a nonflat input. Its finite generic-isomorphism
flatification consequence is the source's Step 0 and is all this proof plan needs.
It is a proof-only prerequisite outside this statement delivery's dependency-repair
scope, so its statement is not silently changed here.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
