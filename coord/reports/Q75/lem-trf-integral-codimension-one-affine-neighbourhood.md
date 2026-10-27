## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralCodimensionOneAffineNeighbourhood` states
`AlgebraicGeometry.exists_isAffineOpen_superset_of_isIntegral_of_stalk_dimension_le_one`.
Its only theorem has proof `by sorry`; no definitions or auxiliary theorems are introduced.
The node changes only in `lean`.

Source read: `literature/stacks-project/varieties.tex`, Tag 09NJ,
`lemma-finite-set-codim-1-points-in-affine`, statement and full proof (lines 9016–9064).
The node's finite-set formulation includes the empty and generic-only cases, which its
expanded proof explicitly handles. No source-wide Noetherianity or finite-type assumption
is present in this lemma.

Hypotheses and conclusion matched clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| X is a scheme | `(X : Scheme.{u})`, with explicitly declared universe `u` |
| X is integral | `[IsIntegral X]`; includes nonemptiness |
| X is separated | `[X.IsSeparated]`; Mathlib's absolute separatedness, equivalently separated structure morphism to the terminal scheme |
| T is a subset of X | `(T : Set X)` |
| T is finite, possibly empty | `(hT : T.Finite)`, with no nonempty assumption |
| Every selected local ring is Noetherian | `(hnoetherian : ∀ x ∈ T, IsNoetherianRing (X.presheaf.stalk x))` |
| Every selected local ring has Krull dimension at most one | `(hdimension : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) ≤ 1)` |
| There is an affine open subscheme V of X | `∃ V : X.Opens, IsAffineOpen V` in the conjunction; `IsAffineOpen V` is defined as `IsAffine V`, for the canonical open subscheme |
| V contains T | `T ⊆ (V : Set X)` |

Statement dependency interfaces read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral` (nonempty, integral sections on every nonempty open).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, importing
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`. This node includes separatedness;
  `AlgebraicGeometry.IsSeparated` defines the closed-diagonal condition on morphisms and
  `AlgebraicGeometry.Scheme.IsSeparated` applies it to `terminal.from X`. Properness itself
  is not a hypothesis here.
- `def-weil-pbc-module-stalk`: `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor` and its `stalkObj` use Mathlib's stalk carrier.
  Here only the scalar ring stalk is needed: `X.presheaf.stalk x`, namely
  `TopCat.Presheaf.stalk` from `Mathlib.Topology.Sheaves.Stalks`, the colimit over open
  neighbourhoods. No module-stalk functor is applied to a ring.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, equivalent to every ideal being finitely generated.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : WithBot ℕ∞`, the supremum of strict prime-chain lengths.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`. Affineness of the canonical open subscheme is expressed with
  `AlgebraicGeometry.IsAffineOpen` from `Mathlib.AlgebraicGeometry.AffineScheme`.

The source files and full signatures/docstrings of the seven statement dependencies were
read. All already give the required notions; no dependency repair is needed. The module
publicly imports these dependency modules and the affine-open interface. All other imports
are the recorded proof dependencies: `Mathlib.AlgebraicGeometry.FunctionField`,
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`,
`Mathlib.AlgebraicGeometry.AffineScheme` (already public),
`Mathlib.RingTheory.KrullDimension.Basic` (already public),
`Mathlib.RingTheory.DiscreteValuationRing.Basic`,
`Mathlib.AlgebraicGeometry.ValuativeCriterion`,
`Sheaf.RingTheory.OneDimensionalSubringsCommonDvr`,
`Sheaf.AlgebraicGeometry.SemilocalSubringAffineGluing`,
`Mathlib.AlgebraicGeometry.Gluing`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`Sheaf.AlgebraicGeometry.AffineSourceStalkIsomorphismNeighbourhood`.
The proof docstring retains all six DAG steps with the nodes each uses, including the
empty/generic reduction and the localness argument for inclusions in a common DVR.

Edge cases checked before writing: T empty makes both local-ring hypotheses vacuous and
requires only an affine open; integrality supplies a point and hence such an open. A
singleton generic point has a field stalk of dimension zero, and every nonempty affine
open contains it. A singleton codimension-one point has its usual affine neighbourhood.
The inequality allows dimension zero as well as one; it is not replaced by equality.
An empty scheme cannot satisfy `IsIntegral`, exactly as the dependency node specifies.
Only selected stalks must be Noetherian; no global or local Noetherianity assumption on X
was added. No field, characteristic, quasi-compactness, closedness of selected points or
projectivity hypothesis is added. The universe is arbitrary and all binders are explicit;
`set_option autoImplicit false` checks this.

Searches actually run with `msearch.py Q75 lem-trf-integral-codimension-one-affine-neighbourhood`:

- `leanfinder`: "A finite set of points with Noetherian local rings of Krull dimension at
  most one on an integral separated scheme has a common affine open neighbourhood".
  Eight hits: local affine charts, a finite-morphism affine-property instance,
  `Scheme.affineOpenCover_X`, the affine-cover instance,
  `exists_isAffineOpen_mem_and_subset`, and locally Noetherian/finite affine cover results.
  None produces a common affine open under these hypotheses.
- `loogle`: `AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsAffineOpen`.
  Two hits: `functionField_isFractionRing_of_isAffineOpen` and
  `IsAffineOpen.primeIdealOf_genericPoint`. Neither asserts neighbourhood existence.
- `grep` under `AlgebraicGeometry`:
  `(codim.*affine|finite.*points.*affine|affine.*finite.*points)`. Zero hits.
- `leansearch`: "Finite codimension at most one points of an integral separated scheme
  have a common affine open neighbourhood". Eight hits: affine neighbourhood of one
  point, spectrum-map version of that fact, affine basis and local affine property,
  intersections via basic opens, affine cover, affineness of a subsingleton open, and
  the affine-property description of separatedness. No exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `codim.*affine|finite.*points.*affine|affine.*finite.*points|exists_isAffineOpen_of.*(integral|Integral)|exists_isAffineOpen.*(finite|Finite)`.
  Read the plausible hits: upstream `Mathlib/AlgebraicGeometry/Properties.lean` handles
  finitely many generic points plus one arbitrary point; projective-space
  `AffineNeighbourhood.lean` requires a quasi-projective immersion; upstream
  `Mathlib/AlgebraicGeometry/AffineScheme.lean` assumes an existing affine containing the
  selected points; `Sheaf/AlgebraicGeometry/ProjectiveFiniteAffineNeighbourhood.lean`
  requires an affine morphism to projective space over an affine base. None matches.
- `rg` for the exact node id in `lean/WeilConjectures`: zero hits. Exact proposed
  declaration name in Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json`:
  zero hits. No second definition or duplicate theorem was found.

No statement dispute, source fault, correction, new node or dependency module.

Validation: `scompile.py` compiled the delivered file in both sandbox mode (1.8 seconds)
and library module mode (2.2 seconds), with no errors or unexpected warnings.

## Second reading by Q75

Author self-check; independent delivery review belongs to the maintainer, as the worker
brief specifies. Re-read the node, Tag 09NJ and the finished declaration together.
`X : Scheme.{u}` introduces exactly the scheme, `IsIntegral` includes its required
nonemptiness, and `X.IsSeparated` is absolute separatedness. `T : Set X` and `T.Finite`
represent the finite set without enumerating it or discarding the empty case. Both
stalk conditions quantify over exactly `x ∈ T`, and use the same structure-sheaf stalk.
`≤ 1` retains the generic-point case. The existential binds an open of X and its two
conjuncts say precisely that the associated open subscheme is affine and contains T.
No stronger condition on V is present. Every parameter and universe is bound explicitly.
No mathematical mismatch was found, and no statement or dependency fields were changed.
