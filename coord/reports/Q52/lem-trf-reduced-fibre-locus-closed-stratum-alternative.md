## Worker report

The module `Sheaf.AlgebraicGeometry.ReducedFibreLocusClosedStratumAlternative` states
`AlgebraicGeometry.exists_nonempty_open_reduced_geometricFiber_closed_stratum_alternative`.
Its only proof is `sorry`; it introduces no definitions or helper theorems.

The source is Stacks `more-morphisms.tex`, Tag 0579, second proof paragraph,
read together with Tags 0576, 0577 and 0578. The generic-fibre alternatives need
only finite type and an irreducible base. The node's quasi-compact, locally
finitely presented morphism is finite type, and these hypotheses survive the
base change to a closed stratum. Consequently the node correctly extracts this
argument without the Noetherian hypothesis used elsewhere in Tag 0579.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Quasi-compactness: `[QuasiCompact f]`, not an assumption on the identity of `Y`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`; no additional
  finite-presentation or quasi-separatedness assumption occurs.
- The geometric fibre at `y` is exactly
  `pullback f (Y.fromSpecAlgebraicClosureResidueField y)`. Reading the upstream
  definition shows that its second argument is
  `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
  (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y`.
  Thus the chosen closures are the existing canonical `AlgebraicClosure`s.
  No new geometric-point or fibre definition is made. This implements the
  dependency's recorded `pullback` specialization literally. The choice of
  closure does not affect reducedness, by the recorded algebraic-closure test.
- Reducedness is `AlgebraicGeometry.IsReduced` of that pullback. This is the
  sectionwise definition in the dependency record, equivalent to the stalkwise
  definition by `isReduced_of_isReduced_stalk` and its converse instance.
- Every irreducible closed subset: arbitrary `(Z : Set Y)` with
  `(hZclosed : IsClosed Z)` and `(hZirreducible : IsIrreducible Z)`.
  `IsIrreducible` includes nonemptiness, exactly as required.
- A relatively open subset is `V : TopologicalSpace.Opens Z`; the subtype `Z`
  has the induced topology. Its points are automatically points of `Z`.
- Nonemptiness is `(V : Set Z).Nonempty`.
- `V ⊆ E_f` is the first alternative, `∀ z : Z, z ∈ V → IsReduced (...)`.
  Here `z.val` is the same point of `Y` at which the geometric fibre is taken.
- `V ∩ E_f = ∅` is the second alternative,
  `∀ z : Z, z ∈ V → ¬ IsReduced (...)`. Thus the disjunction concerns one
  uniform alternative on all of `V`, not a pointwise choice between alternatives.
- There are no assumptions on reducedness or Noetherianity of `Y` or its
  stratum, flatness of `f`, or nonemptiness of fibres.

Dependency declarations used (full signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its public dependency
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, exposed through the public scheme-pullbacks import.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.Topology.Irreducible`: `IsIrreducible`, exposed by the public
  scheme-properties import. This is the exact subset notion named by the
  irreducible-components dependency's Mathlib match.
- Existing upstream `WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField`:
  `AlgebraicGeometry.Scheme.fromSpecAlgebraicClosureResidueField` is the
  canonical composite specifying the geometric point, not a new definition.

Every already-stated proof dependency is imported privately. The closed-subscheme
existence match uses `Scheme.IdealSheafData.subschemeι` and `range_subschemeι`
(from `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, exposed by the private
closed-immersion import), together with its vanishing ideal. Closed immersions use
`IsClosedImmersion` from `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
Sobriety uses the scheme `QuasiSober` instance and `QuasiSober.sober` from
`Mathlib.Topology.Sober`. Base-change permanence uses the `QuasiCompact` and
`LocallyOfFinitePresentation` base-change instances, with
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` for the dependency's full record.
The three project proof modules imported are:

- `Sheaf.AlgebraicGeometry.GenericConstancyGeometricReducedness`:
  `AlgebraicGeometry.exists_nonempty_open_geometricallyReduced_fiber_iff_generic`.
- `Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`:
  `AlgebraicGeometry.geometricallyReduced_iff_isReduced_pullback_algebraicClosure`.
- `Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`:
  `AlgebraicGeometry.geometricReduced_fibre_locus_baseChange`.

The declaration docstring carries all five proof steps with the matching DAG
identifiers. The module makes no change to the node's mathematical statement,
proof, or dependency lists, and needs no new node or dependency repair.

Edge cases checked before writing: `Y` empty permits no `IsIrreducible Z`;
`Z = ∅` is likewise excluded by that predicate. Empty `X`, or empty individual
fibres, remain included and have reduced geometric fibres. A singleton stratum
has its whole subspace open. Nonreduced or non-Noetherian base schemes are
allowed. No perfectness or characteristic restriction is imposed on residue
fields; reducedness is tested after their algebraic closures. The single scheme
universe `u` covers any given pair of schemes after choosing a common universe;
there is no independent lower universe of test objects or empty quantification.

Searches (all performed for this item with the prescribed `msearch.py` wrapper):

- LeanFinder: "For a quasi compact locally finitely presented morphism of schemes
  every irreducible closed subset has a nonempty relatively open subset on which
  geometric fibres are all reduced or all nonreduced". Eight hits, including
  scheme quasi-sobriety, quasi-finiteness, Jacobson fibres and normalization;
  no existing declaration of this alternative.
- Loogle: `AlgebraicGeometry.GeometricallyReduced`. Twelve hits, including the
  class and its base-change instances and reducedness over reduced bases; no
  statement of the stratum alternative.
- Mathlib grep: `([Ii]rreducible|[Cc]onstructible|[Gg]eneric).*([Rr]educed|[Ff]iber)|([Rr]educed|[Ff]iber).*[Cc]onstructible`
  in `AlgebraicGeometry`. Twenty hits; the geometric-reducedness and
  geometric-integrality modules do not state this alternative.
- LeanSearch: "The reduced geometric fibre locus is constant on a nonempty
  relatively open part of every irreducible closed subset". Eight hits,
  including irreducible closed sets, generic points and geometric reducedness
  of algebras; no exact theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for geometricReduced,
  geometric reducedness with closed/stratum, and the item identifier: the
  existing base-change and constructibility results are different statements.
  The latter adds qcqs assumptions on the base, so is not an existing match.
  Additional broader searches for closed/reduced objects also yielded no match.
  Inspection of that result located the reusable geometric-point composite.
- Direct search in `dag/lean_names_upstream.json` for this identifier and
  `exists_nonempty_open.*[Rr]educed`: no match.

Validation: prescribed `scompile.py` compiled both the sandbox translation and
actual library module successfully (1.6 s and 1.5 s respectively), with no errors
or non-sorry warnings. Auto-implicit binding is disabled explicitly. All lines
are at most 100 characters. No statement dispute or node fault was found.

## Second reading by Q52

A second pass by this same assigned worker re-opened the node and complete module
and checked all binders and both branches; independent review is left to the
maintainer as the dispatcher brief specifies. The critical checks were that
openness is in the subtype `Z`, nonemptiness is asserted for `V`, irreducibility
is the nonempty `IsIrreducible` predicate, and the disjunction is outside the
point quantifiers. Both branches use the same canonical algebraic-closure fibre
and the same ambient point `z.val`. There are exactly the two finiteness
hypotheses of the node. Nothing assumes reducedness, flatness, Noetherianity,
quasi-separatedness, or nonempty fibres. The statement introduces no new data
and the only postponed proof is the named theorem. No mismatch required a change.
