## Worker report

The module `Sheaf.TraceFormula.NodalLimitLCIPureStage` states
`AlgebraicGeometry.nodal_limit_lci_pure_stage`. Its sole proof is `sorry`.
No definition, helper theorem, new node, dependency repair, or statement correction is needed.
The existing node is copied with only `lean` changed.

Clause-by-clause rendering:

- The nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. The index universe is the scheme universe.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. Each stage has
  `CompactSpace` and `QuasiSeparatedSpace`; every `D.map f` has `IsAffineHom`.
- The given limit is `c : Cone D` with `hc : IsLimit c`. Thus `S` is `c.pt`
  and its canonical projections are `c.π.app (op i)`.
- The fixed stage is `a : I`. The initial source is `Xₐ : Scheme.{u}` with
  `CompactSpace Xₐ` and `QuasiSeparatedSpace Xₐ`; its map is `gₐ`.
  Finitely presented is exactly the three explicit instances
  `LocallyOfFinitePresentation gₐ`, `QuasiCompact gₐ`, `QuasiSeparated gₐ`.
- The limit source is `pullback gₐ (c.π.app (op a))`; its map `h` is the
  second projection. `hflat` is `Flat` of that projection.
- Each geometric point is an arbitrary `Ω : Type u` with `[Field Ω]`
  `[IsAlgClosed Ω]` and `y : Spec (.of Ω) ⟶ c.pt`. This is exactly the
  recorded geometric-point encoding, using the scheme universe, not a smaller
  independent test-field universe. The theorem is universe polymorphic.
- `hfib` states `IsEmpty` of the geometric pullback or its `IsPureDimension 1`
  together with the completion condition at every point outside its map's
  `smoothLocus`. No closed-point restriction or connectedness is added.
- Each completion is `AdicCompletion (IsLocalRing.maximalIdeal R) R`, for
  the actual stalk `R` of that geometric fibre. `Nonempty (… ≃+* …)` expresses
  isomorphism with `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`.
  The node asks for a ring isomorphism, and the statement adds no coefficient
  linearity or chosen parameters to that condition.
- The common later stage is `∃ b, ∃ hab : a ≤ b`; the result holds for
  every `i` and every `hbi : b ≤ i`. Its transition arrow is
  `D.map (homOfLE (hab.trans hbi)).op`, and `gᵢ` is `pullback.snd gₐ` of it.
- The first two conjuncts are exactly `Flat gᵢ` and
  `LocallyOfFinitePresentation gᵢ`.
- The ordinary-fibre clause quantifies over every `s : D.obj (op i)` and
  asserts `Nonempty (gᵢ.fiber s) → (gᵢ.fiber s).IsPureDimension 1`.
- The last clause quantifies over every algebraically closed geometric field
  and point of this stage. It asserts an empty geometric fibre or purity of
  dimension one together with an affine LCI neighbourhood for every point.
- The neighbourhood is `U : C.affineOpens` with `z ∈ U.1`. Its coordinate
  algebra uses the actual geometric fibre structure map, via `appLE` and
  `Scheme.ΓSpecIso`, to obtain its `Ω`-algebra structure. The explicit
  `ft : Algebra.FiniteType Ω Γ(C,U.1)` and
  `Algebra.IsLocalCompleteIntersection Ω Γ(C,U.1)` are the node's finite
  generation and algebraic LCI condition. Pointwise neighbourhoods form an
  affine open cover, and conversely any such cover supplies these neighbourhoods.
  Thus this is exactly the cover formulation stated in the node.

Dependency declarations used (full signatures and docstrings read in source):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` and the quasi-compact
  API: `QuasiSeparated`, `QuasiCompact`, `QuasiSeparatedSpace`, `CompactSpace`.
  The convention node introduces no additional declaration.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points
  are written inline as prescribed by `def-weil-geometric-point`.
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`
  identifies this encoding with a point and residue-field embedding.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`; this realizes both fibre-product and geometric-fibre dependencies.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsLocalCompleteIntersection` (and its global-CI definition).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `Scheme.Hom.smoothLocus`.
  The record's deprecated `IsSmooth` spelling is not needed.
- `Mathlib.RingTheory.AdicCompletion.Basic`, with ring structure from `.Algebra`:
  `AdicCompletion`; `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `exists_limit_affine_transition`; its cone/IsLimit interface encodes the given limit.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, used for ordinary fibres.

The stated proof dependencies are imported as plain imports, including
`completeIntersectionFibres_limit_descent`, `nodal_curve_lci_criterion`,
`pure_relative_dimension_finite_stage`, `pure_relative_dimension_base_change`,
`topologicalKrullDimAt_eq_of_equidimensional_open`, and
`topologicalKrullDim_component_eq_of_constant_local_dimension`. Mathlib proof
leaves are supplied by `AlgebraicClosure`, `PullbackCarrier` (surjectivity and its
base-change stability), and `FiniteStability` (finite-presentation base change
and composition). `lem-trf-field-extension-component-local-dimension` currently
has neither a Lean record nor a Mathlib match; it is a proof-only prerequisite,
so there is no module to import yet. This does not obstruct this statement.

Sources read: `literature/stacks-project/curves.tex`, lemma-nodal-lci (0C4E)
and lemma-descend-nodal-family (0C5F); `limits.tex`, lemma-descend-syntomic
(0C3L) and lemma-descend-dimension-d (0EY2). The six-step proof docstring
follows the node's proof, including geometric-to-ordinary purity and a common
upper bound for the two tails.

Edge cases checked before writing: empty `Xₐ`, empty limit base, empty ordinary
and geometric fibres, smooth geometric fibres (the completion implication is
vacuous), and a singleton directed set (the tail can start at `a`). No
nonemptiness of a fibre, connectedness, Noetherianness, separatedness, or
characteristic assumption has been added. `Nonempty I` is required as in the
node, and the allowed empty affine cover is rendered by the vacuous pointwise
neighbourhood condition. Repeated or equal indices are allowed by `Preorder`.
There is no statement dispute or correction.

Searches performed on 2026-10-24:

- `msearch.py ... leanfinder`: "A flat finitely presented nodal curve over an
  inverse limit eventually has flat local complete intersection geometric
  fibres of pure dimension one". Eight results: flatness, smooth relative
  dimension, flat openness and associated standard facts; none is this theorem.
- `msearch.py ... loogle`: "AlgebraicGeometry.Flat,
  AlgebraicGeometry.LocallyOfFinitePresentation". Twelve results, including
  universally open, etale and smooth-fibre criteria; no finite-stage nodal result.
- `msearch.py ... grep`: "nodal|IsLocalCompleteIntersection|pureDimension"
  in Mathlib `AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch`: "Local complete intersection geometric fibres
  and pure relative dimension descend along inverse limits of schemes".
  Eight results: general local descent, finite presentation, properness and
  related APIs; none is this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for nodal limit/stage names,
  and `grep -rn` for the exact item id upstream: no exact theorem. The related
  `NodalFamilyNoetherianApproximation` uses this argument but states a different
  conclusion. The exact proposed declaration is absent from the upstream-name map.
- The recorded dependencies and the existing `LocalCompleteIntersectionScheme`
  and nodal-fibre modules were read. Their predicates differ from the full
  assertion here; the algebraic LCI notion is reused directly, not copied.

Validation: `scompile.py Q76 lem-trf-nodal-limit-lci-pure-stage` compiled the
sandbox and final library module successfully, with no errors or warnings.

## Second reading by Q76

The dispatcher assigned one worker and expressly forbids subagents; this is a
second clause audit by that worker, not a claimed independent review. The
maintainer's independent delivery review remains the independent reading.

Reopened the node and the completed Lean file. Checked the direction of
`(homOfLE (hab.trans hbi)).op` (from the later stage to `a`), the second
projection as each base-changed family map, and the further second projection
as its geometric-fibre structure map. Checked that `hc` requires the given
cone to be limiting; the theorem does not assume only an arbitrary cone.
Checked that all three finite-presentation clauses are present, every later
stage is quantified, ordinary fibres range over all points, and geometric
fibres range over arbitrary algebraically closed fields in the scheme
universe. The completion test is at all nonsmooth points, while the lci clause
uses actual coordinate algebras and their canonical coefficient map, with
finite type explicitly supplied. Empty fibres are admitted in both branches.
The proof docstring contains all six steps. No mismatch was found in this
second reading; no source or node correction was made.
