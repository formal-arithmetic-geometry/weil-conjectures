## Worker report

The new module `Sheaf.AlgebraicGeometry.Curve.ReducedBoundarySmooth` states
`AlgebraicGeometry.reducedBoundary_smoothOfRelativeDimension_zero`, with one `sorry` proof
and no definitions. It renders the unchanged statement of `lem-a1-reduced-boundary-smooth`.
The six-step natural-language proof is in its declaration docstring, including every DAG
proof dependency used in the node's proof. The node copy changes only `lean`.

The source was read in the current main-20261015 blueprint,
`sec-deligne-laumon-a1/sk-p-dl-a1-perverse/thm-a1-curve-perverse-heart.proof.md`, Step 2.
Also read Stacks `varieties.tex`, lemma-algebraic-scheme-dim-0 (06LH);
`algebra.tex`, lemma-minimal-prime-reduced-ring (00EU); and `morphisms.tex`,
lemma-etale-over-field (02GL) and lemma-etale-smooth-unramified (02GK).

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Perfect base field k | `{k : Type u} [Field k] [PerfectField k]` |
| C, U, Z are schemes | `{C U Z : Scheme.{u}}` |
| C is a k-scheme | `[C.Over (Spec (.of k))]`; the given structure morphism is `C ↘ Spec (.of k)` |
| C is smooth over k | `[Smooth (C ↘ Spec (.of k))]` |
| C is separated over k | `[IsSeparated (C ↘ Spec (.of k))]` |
| C is finite type over k | `[LocallyOfFiniteType (C ↘ Spec (.of k))]` and `[QuasiCompact (C ↘ Spec (.of k))]` |
| C has pure dimension one | `(hC : C.IsPureDimension 1)` |
| j:U→C is an open immersion | `(j : U ⟶ C) [IsOpenImmersion j]` |
| j is dense | `(hj : DenseRange j)` |
| i:Z→C is a closed immersion | `(i : Z ⟶ C) [IsClosedImmersion i]` |
| Z has the reduced structure | `[IsReduced Z]` |
| i is the closed complement of j | `(hZ : Set.range i = (Set.range j)ᶜ)` |
| Z is a k-scheme | Its induced structure map is the actual composite `i ≫ C ↘ Spec (.of k)` in every conclusion |
| Z is finite type | `LocallyOfFiniteType (i ≫ C ↘ Spec (.of k)) ∧ QuasiCompact (i ≫ C ↘ Spec (.of k))` |
| Z is reduced | `IsReduced Z` in the conjunction, as explicitly asserted by the node |
| dim Z ≤ 0 | `topologicalKrullDim Z ≤ 0` |
| dim Z = −∞ if Z is empty | `IsEmpty Z → topologicalKrullDim Z = ⊥` |
| The structure morphism is smooth | `Smooth (i ≫ C ↘ Spec (.of k))` |
| It has pure relative dimension zero | `SmoothOfRelativeDimension 0 (i ≫ C ↘ Spec (.of k))` |

A reduced closed immersion with the prescribed closed image is exactly the reduced induced
closed subscheme structure, up to its unique isomorphism over C. No arbitrary map or
unspecified scheme structure replaces the complement. U needs no separately chosen
k-structure: its inherited one is j followed by C's structure map, just as for Z.
Mathlib's `SmoothOfRelativeDimension 0` already includes smoothness; both clauses are
spelled out because the node explicitly asserts both. No absolute dimension equality
`dim Z = 0` or nonemptiness assumption is introduced.

The statement dependencies use their recorded interfaces, read with docstrings and full
signatures in the pinned sources:

| Dependency | Module and declarations |
| --- | --- |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`; its imported `Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact` |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion` |
| def-weil-pure-dimension | `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, `AlgebraicGeometry.SmoothOfRelativeDimension` |
| def-pc-reduced-scheme | `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`, importing `Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`; no properness assumption |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`: `topologicalKrullDim : WithBot ℕ∞` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom` |

`PerfectField` is Mathlib's existing notion from `Mathlib.FieldTheory.Perfect`, not a
private predicate. Its polynomial separability definition gives exactly separability of
all algebraic extensions through `Algebra.IsAlgebraic.isSeparable_of_perfectField`.
All variables and the common scheme/ring universe `u` are explicitly bound;
`set_option autoImplicit false` is enabled.

The recorded, already stated proof interfaces are imported without `public`:
`Sheaf.AlgebraicGeometry.Dimension` (`Scheme.dim_eq_topologicalKrullDim`),
`Sheaf.AlgebraicGeometry.NowhereDenseDimZero` (`dim_le_zero_of_isNowhereDense`),
`Sheaf.AlgebraicGeometry.ClosedPointField`
(`closedPoint_iff_residueField_trdeg_zero_and_finite`),
`Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`
(`etale_sigmaDesc_spec_of_finite_separable`), and
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
(`smooth_and_fibre_dimension_zero_of_etale`). Their source modules were read.
The remaining Mathlib proof leaves are imported through `Topology.Irreducible`,
`AlgebraicGeometry.Artinian`, `AlgebraicGeometry.Noetherian`,
`AlgebraicGeometry.Limits`, `AlgebraicGeometry.ResidueField`, and
`RingTheory.KrullDimension.Zero`. These supply irreducible components, finite/discrete
Artinian schemes, scheme coproducts and singleton affineness, residue fields, and the
minimal-prime localization criterion. No import-cycle omission is needed.

Edge cases checked before writing:

- Empty boundary (including j an isomorphism): dimension is at most zero and exactly
  `⊥`, with no points at which relative dimension must be checked. Every conclusion
  remains meaningful, including the empty coproduct in the proof plan.
- Empty C: pure dimension one is vacuous; the maps force U and Z empty. No Nonempty
  binder excludes this case. If U is empty, density forces C empty.
- Disconnected C: pure dimension is quantified over every irreducible component, not
  replaced by integrality or geometric connectedness.
- Non-rational closed points: finite separable residue extensions are allowed; no
  algebraic-closedness or equality of residue fields to k is assumed.
- Characteristic zero and positive characteristic perfect fields: no finiteness,
  characteristic, or countability restriction is imposed.
- Reducedness and perfectness are retained; a nonreduced boundary need not be smooth,
  and inseparable residue extensions over an imperfect field need not be etale.

Searches made with `msearch.py Q10 lem-a1-reduced-boundary-smooth`:

- LeanFinder: `The reduced closed complement of a dense open of a smooth curve over a
  perfect field is smooth of relative dimension zero`. Eight hits, all smooth-chart
  definitions, smoothness consequences, and standard-smooth algebra infrastructure;
  none states the reduced boundary theorem.
- Loogle: `"SmoothOfRelativeDimension", "IsReduced"`. Successful query, zero hits.
- grep in Mathlib/AlgebraicGeometry: `reduced.*boundary|boundary.*smooth|PerfectField|SmoothOfRelativeDimension`.
  Eleven hits on the smooth locus over a perfect field, the existing relative smoothness
  definition, and its etale comparison; no boundary theorem.
- LeanSearch: `The reduced closed complement of a dense open of a smooth curve over a
  perfect field is etale`. Eight hits: etale definitions, standard-smooth-zero implies
  etale, and etale-locus infrastructure; no exact statement.
- `rg` in upstream `WeilConjectures/` and shared `lean/Sheaf/` for the item id,
  `reduced.*boundary|boundary.*smooth|reducedBoundary|reduced_boundary`: related
  boundary constructions and alteration statements, no exact theorem. In particular
  upstream `EtaleCohomology/Purity/RealSheaves/BoundaryConstruction.lean` supplies
  finite/closed boundary points under connected finite-field curve assumptions, not
  this theorem over arbitrary perfect fields. Its source was inspected.
- `rg` in `dag/lean_names_upstream.json`, Mathlib, upstream `WeilConjectures/`, and
  `lean/Sheaf/` for the proposed name and closely related spellings: no collision.

There is no statement dispute, correction, missing notion, or dependency repair.

Validation: `scompile.py Q10 lem-a1-reduced-boundary-smooth` compiled the delivered
file cleanly both as sandbox and library module (2.6 s and 5.6 s respectively).
No warnings were printed. Only the theorem body is `sorry`.

## Second reading by Q10

A separate rereading of the unchanged node and the completed file checked every row
above, especially the difference between absolute and relative dimension, the empty
boundary, and the actual composite used as Z's k-structure. This is the dispatcher's
single-worker delivery; the independent maintainer review remains separate.
The existing `Scheme.IsPureDimension` definition quantifies over irreducible components
and admits the empty scheme, exactly as the node requires. The finite-type clause uses
both locally finite type and quasi-compactness on the same structure morphism. The
complement equality and reduced closed immersion describe precisely the specified Z.
All conclusions of the node are present, including its explicit repeated reducedness
and the minus-infinity empty case. No extra hypotheses or conclusions were found, and
no changes were needed after this rereading. The module and declaration docstrings
identify the exact source and give all six steps of the node's proof.
