## Repair of returned head a64f961aa796

H2 repaired: replaced `lem-trf-nodal-point-etale-locality` in the item's
`stmt_deps` with the already landed definition node
`def-trf-completed-local-scalar-map`, and corrected the dependency table and
explanation below. The scalar-map definition's recorded declaration and
explicit construction were checked in the current source. The theorem node
remains a proof dependency. The Lean module is byte-for-byte unchanged.
Compared with current main, the node changes only `lean` and adds the owning
definition node to `stmt_deps`; all other fields match current main.

The returned head passed server compilation and dry-run preflight, then was
pushed at `a64f961aa79`. The earlier disk-full failures recorded below are
historical. The repaired packet passed server compilation and dry-run preflight
(`9a89e4e17ca`, nothing pushed). The final report update is validated again
before delivery.

## Worker report

Item: `lem-trf-etale-cover-field-curve-nodality`, group NA, stage 2.

The module `Sheaf.AlgebraicGeometry.EtaleCoverFieldCurveNodality` states
`AlgebraicGeometry.etale_cover_field_curve_nodality`. Its only declaration is
this theorem, with proof `sorry`. There are no new definitions, dependency
repairs, or corrections to the mathematical statement.

Source read: Stacks `curves.tex`, lemma-nodal-family-etale-local-source
(Tag 0C5D, lines 4823–4847), and lemma-node-etale-local (0C57, lines
4445–4468); `descent.tex`, lemma-dimension-at-point-local (04N4, from
line 5173), lemma-dimension-at-point (04NL, from 8063), and
lemma-smooth-smooth-local-source (036U, from 6928); `varieties.tex`,
lemma-dimension-locally-algebraic (0A21, from 3783), especially (3) and (5).
The theorem states the node's locally algebraic field case, rather than the
more general relative family assertion of 0C5D.

Hypotheses, individually:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  No characteristic restriction or chosen algebraic closure is used.
- The k-scheme C is `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
  `[LocallyOfFiniteType f]` supplies exactly local finite type, not global
  finite type or quasi-compactness.
- The arbitrary family is `{I : Type v} (D : I → Scheme.{u})`
  `(e : ∀ i : I, D i ⟶ C)`. The k-structure of each D i is its composite
  `e i ≫ f`, so every e i is a morphism over k. This does not introduce an
  unrelated second k-structure on the source.
- `[∀ i : I, Etale (e i)]` states that every covering morphism is étale.
- `hcover : ∀ x : C, ∃ (i : I) (y : D i), e i y = x` is joint
  surjectivity. There is no surjectivity assumption on an individual e i.
- `[∀ i : I, LocallyOfFiniteType (e i ≫ f)]` explicitly retains local finite
  type over k for the D i, as requested in the node (it also follows from
  the preceding assumptions).
- `[IsLocallyNoetherian C]` and `[∀ i : I, IsLocallyNoetherian (D i)]`
  explicitly retain all the node's local Noetherianity hypotheses.

Conclusions, individually:

1. The first conjunct quantifies over every `i` and `y : D i` and asserts
   `topologicalKrullDimAt y = topologicalKrullDimAt (e i y)`. This is local
   topological dimension, the infimum of dimensions of open neighbourhoods,
   not dimension of the local ring. It includes generic and nonclosed points.
2. The second conjunct is `∀ n : ℕ, C.IsPureDimension n ↔
   ∀ i : I, (D i).IsPureDimension n`. The existing purity definition quantifies
   over all irreducible components with their subspace topology. Thus this
   includes n = 0 and the empty scheme convention in the node.
3. The third conjunct is the pointwise smoothness equivalence. Its left side
   is `∃ V : C.Opens, e i y ∈ V ∧ Smooth (V.ι ≫ f)` and its right side is
   `∃ W : (D i).Opens, y ∈ W ∧ Smooth (W.ι ≫ e i ≫ f)`. These are precisely
   smoothness on an open neighbourhood, not merely formal smoothness of
   stalks or global smoothness.
4. The last conjunct is guarded by `C.IsPureDimension 1`. By conclusion 2
   this is equivalent to purity of dimension one on all D i. Its first part
   quantifies over every i and y and negates both open-neighbourhood smoothness
   predicates, giving every nonsmooth pair as in the node. Conclusion 3 makes
   either nonsmoothness condition equivalent to the other, so this excludes
   no pair intended by the node.
   The conclusion is an iff between `Nonempty (@AlgEquiv k ... ...)` for
   the two completed stalks and the identical nodal quotient. Each completion
   is literally `AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
   (X.presheaf.stalk x)`. The target is
   `MvPowerSeries (Fin 2) k ⧸ Ideal.span
   {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}`.
   Constants on the quotient give its usual k-algebra structure; the stalk
   completion uses `(f.completedLocalScalarMap x).toAlgebra`, or the
   corresponding composite structural map on D i. No arbitrary algebra
   structure or coefficient-field splitting occurs. An algebra equivalence
   between these complete local rings preserves their unique maximal ideals,
   hence every power, and is automatically a homeomorphism for the adic
   topologies. Thus no additional topological structure on `AlgEquiv` is needed.
5. The second part under the same purity guard is exactly the universal
   criterion: every nonsmooth x of C has this completed local algebra iff
   every nonsmooth y of every D i does. The left and right negated
   neighbourhood predicates are written separately for their actual schemes.
   No assumption that such points are closed is added.

The declaration's docstring carries all four proof steps of the DAG: flat
fibre-dimension additivity and zero-dimensional étale fibres; the component
maximum and constant-local-dimension criterion for purity; pointwise
smoothness and completed-local nodality; then assembly via joint surjectivity,
including the empty case. No part of that proof is implemented in this stage.

Dependency declarations used, with the signatures and docstrings read in their
source modules:

| Node | Module | Declaration |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs (reexported by IsAlgClosed.Basic) | Field |
| def-weil-algebraic-closure | Mathlib.FieldTheory.IsAlgClosed.Basic | IsAlgClosed |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | AlgebraicGeometry.LocallyOfFiniteType |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale | AlgebraicGeometry.Etale |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-kun-topological-dimension-at-point | WeilConjectures.Mathlib.Topology.KrullDimension | topologicalKrullDimAt |
| def-weil-pure-dimension | Sheaf.AlgebraicGeometry.PureDimension | AlgebraicGeometry.Scheme.IsPureDimension |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.Smooth |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic and Algebra | AdicCompletion |
| def-weil-pbc-multivariate-power-series | Mathlib.RingTheory.MvPowerSeries.Basic | MvPowerSeries |
| def-trf-completed-local-scalar-map | Sheaf.AlgebraicGeometry.NodalPointEtaleLocality | AlgebraicGeometry.Scheme.Hom.completedLocalScalarMap |

`def-trf-completed-local-scalar-map` owns the canonical scalar-map definition
used in the signature. Its landed `existing: true` record points to
`AlgebraicGeometry.Scheme.Hom.completedLocalScalarMap` in
`Sheaf.AlgebraicGeometry.NodalPointEtaleLocality`. It is the added statement
dependency. The theorem node `lem-trf-nodal-point-etale-locality` remains only
in `proof_deps`, as in the base node; its theorem
`AlgebraicGeometry.nodalPoint_etale_locality` applies at any point, and either
nodal presentation forces both points to be closed.

The stated proof dependencies are imported without `public`, except for the
nodal module and purity definition needed in the signature. These imports
include `flat_composite_fibre_dimension_at_point`,
`smooth_and_fibre_dimension_zero_of_etale`,
`topologicalKrullDim_component_eq_of_constant_local_dimension`, and
`smooth_at_iff_of_etale` from their recorded modules. The general component
maximum node `lem-trf-locally-algebraic-dimension-components` has no Lean or
Mathlib binding in the read DAG, so there is no recorded module to import;
its proof step remains documented. It is only a proof dependency, not a
missing notion required to elaborate this statement.

Edge cases checked before writing: empty C and I (joint surjectivity then
forces empty C, and all conclusions are vacuous); nonempty I with empty
source components; the identity cover; repeated/disconnected covers; n = 0;
a nonpure example with both one- and two-dimensional components; smooth
curves (nodality assertions vacuous); the ordinary crossing uv = 0;
nonclosed points (no artificial closedness restriction on the iff);
arbitrary characteristic, including 2. There are no separatedness,
quasi-compactness, irreducibility, reducedness, finiteness of the family, or
nonemptiness hypotheses. u and v are explicitly declared and independent;
autoImplicit is disabled. No node faults or disputed statements were found.

Searches actually run:

- `msearch.py leanfinder` with “An etale cover of schemes locally of finite
  type over an algebraically closed field preserves local topological
  dimension, detects pure dimension and nodal completions”: eight hits,
  mainly Scheme.Etale, IsEtale and relative-smoothness infrastructure;
  no combined cover/nodality statement.
- `msearch.py leanfinder` with “Etale cover detects pure dimension and nodal
  completed local algebras”: eight hits including RingHom.Etale.propertyIsLocal,
  Algebra.etaleLocus and relative dimension zero; no exact match.
- `msearch.py loogle` with `"Etale", "dimension"`: eight hits, including
  AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero and its instance;
  these give the relative-dimension-zero characterization, not the node.
- `msearch.py grep` with `nodal|IsPureDimension|topologicalKrullDimAt` in
  Mathlib/AlgebraicGeometry: zero hits.
- `rg` in the named WeilConjectures and Sheaf source directories for
  `nodal`, `jointly_surjective_etale`, `smooth_at_iff_of_etale`, and
  `completedLocalScalarMap`, plus the item-id grep in WeilConjectures:
  the item id has no upstream match. The useful existing source interfaces
  are NodalPointEtaleLocality and SmoothEtaleLocalSource, both read in full.
  More targeted `rg` for the proposed declaration name and dimension/etale
  combinations found no combined theorem. Broader Sheaf hits concern other
  nodal geometry, normalization, and resolution statements.

Validation: the prescribed scompile.py wrapper has been invoked. The first
attempt ended in the server's library compile with
`resource exhausted (error code: 28, no space left on device)`; this is an
infrastructure error, not a Lean diagnostic about the statement. The second scompile.py attempt failed with the identical server error.
The required deliver2.py --no-push also failed at its initial server compile
with the same error and printed “COMPILE FAILED on the server, nothing pushed”.
Consequently no preflight result or successful compilation is claimed, and
no delivery was pushed. Server storage cannot be repaired within this
worker’s sandbox-only write authorization. All prepared files remain here
for a retry after the server storage failure is repaired.

## Retry on 2026-10-24

Retained the earlier packet and began with the required deliver2.py --no-push.
It again failed during the server library compile with
`resource exhausted (error code: 28, no space left on device)`, before preflight
or a Lean diagnostic about this statement. The current saved node was compared
with the shared read clone: only `lean` and the authorized addition of the landed
`lem-trf-nodal-point-etale-locality` to `stmt_deps` differ. The recorded signature
matches the theorem verbatim, all Lean lines are at most 100 characters, and the
record date is the current UTC date. The saved mathematical statement and module
were retained. Retried the prescribed scompile.py wrapper; see the retry outcome
below. No direct repository or launcher-tool changes were made.

The scompile.py retry also exited 1 with the same library-compile error:
`resource exhausted (error code: 28, no space left on device)`. Compilation
and delivery therefore remain unverified; nothing was pushed. This is a server
storage/tool failure outside the sandbox-only repair authorization.

## Dispatcher retry 2026-10-24 10:53 UTC

Started by reading the saved report and running the prescribed dry run.
Both deliver2.py --no-push and a fresh scompile.py invocation exited 1
with the server library-compile error `resource exhausted (error code: 28,
no space left on device)`. No Lean diagnostic or preflight result was reached.
The saved packet was retained; its recorded signature matches the source,
no Lean line exceeds 100 characters, and only lean and the documented added
statement dependency differ from the current read clone. No repair note is
present. Nothing was pushed. The storage failure remains outside this
worker’s sandbox-only write authorization.


## Dispatcher retry 2026-10-24 10:56 UTC

Read the retained report and began with the prescribed deliver2.py --no-push.
It exited 1 during the server library compile with
`resource exhausted (error code: 28, no space left on device)`.
A fresh prescribed scompile.py invocation also exited 1 with that exact error.
Neither invocation reached a Lean diagnostic or successful preflight; nothing
was pushed. Retained all saved module and node content. The self-check found
only lean and the documented landed statement dependency changed against the
current read clone; the recorded theorem signature matches verbatim, no Lean
line exceeds 100 columns, and autoImplicit is disabled. No item repair note
exists. Server storage cannot be repaired within the sandbox-only write scope;
no live repository or launcher-tool edits were made.


## Dispatcher retry 2026-10-24 11:00 UTC

Inspected the retained report and began with the required deliver2.py --no-push.
It exited 1 during the server library compile with
`resource exhausted (error code: 28, no space left on device)`.
The separate prescribed scompile.py retry also exited 1 with the same error.
Neither reached a Lean diagnostic or preflight, and nothing was pushed.
The saved packet remains unchanged: only lean and the documented added
lem-trf-nodal-point-etale-locality statement dependency differ from the current
read clone. The recorded signature matches verbatim, all Lean lines fit
100 columns, autoImplicit is disabled, the record date is current UTC, and
there is no repair note. No repository or launcher-tool edits were made.
Server storage repair is outside the worker sandbox-only write authorization.


## Dispatcher retry 2026-10-24 11:04 UTC

Read the saved report and began with the required deliver2.py --no-push.
It exited 1 during the server library compile with
`resource exhausted (error code: 28, no space left on device)`.
A separate prescribed scompile.py invocation exited 1 with the identical error.
Neither reached a Lean diagnostic or successful preflight; nothing was pushed.
The saved packet is retained. The self-check confirms that only lean and the
documented stmt_deps addition differ from the shared read clone, the recorded
signature matches the theorem verbatim, no Lean line exceeds 100 characters,
autoImplicit is disabled, and the record date remains 2026-10-24.
Server storage repair lies outside the sandbox-only write authorization.
No live repository or launcher-tool edits were made.


## Dispatcher retry 2026-10-24 11:07 UTC

Inspected the retained report and began with the required deliver2.py --no-push.
It exited 1 during the server library compile with
`resource exhausted (error code: 28, no space left on device)`.
A separate prescribed scompile.py invocation exited 1 with the identical error.
Neither reached a Lean diagnostic or successful preflight; nothing was pushed.
The saved module and node remain unchanged. The self-check confirms that only
lean and the documented stmt_deps addition differ from the shared read clone,
the recorded signature matches verbatim, no Lean line exceeds 100 characters,
autoImplicit is disabled, and no repair note is present.
Server storage repair lies outside the sandbox-only write authorization.
No live repository or launcher-tool edits were made.


## Dispatcher retry 2026-10-24 11:10 UTC

Read the saved report and began with the required deliver2.py --no-push.
It exited 1 during the server library compile with
`resource exhausted (error code: 28, no space left on device)`.
A separate prescribed scompile.py invocation exited 1 with the identical error.
Neither reached a Lean diagnostic or successful preflight; nothing was pushed.
The saved module and node remain unchanged. The self-check confirms that only
lean and the documented stmt_deps addition differ from the shared read clone,
the recorded signature matches verbatim, all Lean lines fit 100 columns,
autoImplicit is disabled, and there is no repair note. Server storage repair
is outside the sandbox-only write authorization. No live repository or
launcher-tool edits were made.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
