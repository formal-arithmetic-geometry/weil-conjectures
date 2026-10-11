## Worker report

The module `Sheaf.AlgebraicGeometry.FindGloballyGenerated` states
`AlgebraicGeometry.Scheme.Modules.exists_globallyGenerated_invertible_nonvanishing_eq`.
Its sole proof is `sorry`; no definition or proof is added. The node is unchanged except for
its `lean` record. No new nodes, dependency modules, statement corrections or disputed
statements are needed.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`, with explicit universe `u`.
- Integral: `[IsIntegral X]`, including nonemptiness, reducedness and irreducibility.
- Separated: `[X.IsSeparated]`, absolute separatedness over the terminal scheme.
- Noetherian: `[IsLocallyNoetherian X] [CompactSpace X]`; together these are exactly
  Mathlib's `IsNoetherian X`, not merely local Noetherianness.
- Topological Krull dimension one: `(hdim : topologicalKrullDim X = 1)`.
- Open subscheme: `(U : X.Opens)` represents the open with its induced scheme structure.
- Affine: `(hU : IsAffineOpen U)`.
- Nonempty: `(hne : (U : Set X).Nonempty)`.
- Finite complement: `(hfin : (Set.compl (U : Set X)).Finite)`.
- Existence of an O_X-module: `∃ L : X.Modules`.
- Invertibility: `L.IsInvertible`.
- Global generation: `Nonempty (SheafOfModules.GeneratingSections L)`; the structure
  supplies global sections and an epimorphism from the free module on those sections,
  exactly the recorded generating-sections definition and its local-surjectivity clause.
- A global section: `∃ s : L.val.presheaf.obj (Opposite.op ⊤)`.
- The prescribed section locus: `nonvanishingLocus L s = (U : Set X)`.
  This uses the recorded definition of X_s without introducing another locus. Equality of
  the underlying opens specifies the same open subscheme with its induced structure.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; the node is a Mathlib leaf.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties` (available through the used imports).
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated` and the scheme specialization
  `AlgebraicGeometry.Scheme.IsSeparated`, `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
  Only separatedness is assumed, not properness.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter`, the Mathlib match for this leaf; separation is not part of
  this topological compactness convention.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, valued in `WithBot ℕ∞`.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, imported through Ample.
- `def-weil-pbc-generating-sections`: `SheafOfModules.GeneratingSections`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`.
- `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`, `Sheaf.AlgebraicGeometry.Ample`.
  The locus is germ outside maximal ideal times stalk, precisely the node's X_s.

Source and edge cases: the local Stacks checkout is absent on this machine, so I opened
https://stacks.math.columbia.edu/tag/09NB. Its local hypotheses (Noetherian dimension-one
stalks at complement points) follow from this node's global hypotheses, as explained in
proof step 1 and the existing stage-1 review. The proof docstring records all five node
steps and their cited inputs. The empty scheme is excluded by integrality; the empty U is
explicitly excluded by hne. A dimension-zero scheme is excluded by hdim. An empty finite
complement is permitted: U = X affine, and the unit module with section 1 provides the
conclusion. A nonempty finite complement is illustrated by P^1 with U = A^1, where O(1)
and the section vanishing at infinity work. No smoothness, normality, field, characteristic,
properness or projectivity is imposed. There is no fixed number of generating sections or
complement points. The module and section universes follow X.Modules, consistently with
the dependency record, and u is unrestricted.

Searches for an existing declaration:

- `msearch.py ... leanfinder "integral separated Noetherian one dimensional scheme affine
  open finite complement globally generated invertible sheaf section"`: eight hits,
  including `isAffine_of_isAffineOpen_basicOpen`, integral affine criteria and fraction-field
  lemmas; none is this existence statement.
- `msearch.py ... loogle "SheafOfModules.GeneratingSections, AlgebraicGeometry.IsIntegral"`:
  zero hits.
- `msearch.py ... grep "globally.generated|find_globally|finite.*complement"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "globally generated invertible sheaf section prescribed affine
  open integral separated curve"`: unavailable, Internal Server Error; no conclusion drawn
  from that service.
- `rg` in source `WeilConjectures` for the node id, `find_globally`, and `globally.generated`:
  no matching statement; `Serre.lean` confirms the `GeneratingSections` convention at
  lines 447-450, and unrelated global-generation statements do not prescribe an affine open.
- `rg` in project `lean/Sheaf` for these terms and finite complements: related tensor,
  finite-section-cover and ample-existence lemmas, but no theorem matching the item.
- `rg` in `dag/lean_names_upstream.json` for the item and expected names: no match.

Validation: server single-file compile and deliver2 dry run are run before READY.
The second reader supplies the independent reading and delivers; this report contains no
second-reading claim.

## Second reading by E1

I independently read the node statement, its Stacks source (09NB), the dependency records, and
`FindGloballyGenerated.lean`. The objects and clauses match as follows:

- `X : Scheme.{u}` is the integral scheme; `[IsIntegral X]` supplies integrality (and hence the
  nonempty generic-point situation used by 09NB).
- `[X.IsSeparated]` is the separatedness hypothesis. No properness, smoothness, normality,
  projectivity, field, or characteristic hypothesis is present.
- `[IsLocallyNoetherian X] [CompactSpace X]` are precisely Mathlib's two fields of
  `IsNoetherian X`, matching the node's Noetherian hypothesis without adding a separate condition.
- `hdim : topologicalKrullDim X = 1` is the stated dimension-one condition.
- `U : X.Opens`, `hU : IsAffineOpen U`, `hne : (U : Set X).Nonempty`, and
  `hfin : (Set.compl (U : Set X)).Finite` render the nonempty affine open and finite point
  complement. The finite complement may be empty, as in `U = X`.
- The conclusion introduces `L : X.Modules`, asserts `L.IsInvertible`, and asserts
  `Nonempty (SheafOfModules.GeneratingSections L)`, the recorded global-generation notion.
  It then introduces the global section
  `s : L.val.presheaf.obj (Opposite.op ⊤)` and states
  `nonvanishingLocus L s = (U : Set X)`, exactly the `X_s = U` clause (with the locus compared
  as an underlying set).

The quantifier order is `X`, its instances, dimension, `U`, its three hypotheses, then `L` and
`s`, matching the node and source. The Lean declaration compiled unchanged with the recorded
imports; no unbound variables or universes remain. No mismatch was found, so no code or node
statement was changed.

Edge cases checked: integrality excludes the empty scheme; `hne` excludes an empty `U`; the
zero-dimensional case is rejected by `hdim`; an empty finite complement is allowed; no fixed
number of complement points or generators is assumed; `u` is unrestricted. The source's weaker
local stalk hypotheses are implied by the node's global Noetherian dimension-one assumptions,
which is the specialization recorded by the node and does not alter its conclusion.

Searches were rechecked with `msearch.py` LeanFinder/Loogle/LeanSearch queries, `rg` in Mathlib,
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`; they found no existing
statement of this theorem. The LeanSearch service returned an internal-server error, while the
other searches returned only generic sheaf-generator or affine-open results. Therefore the
module remains a new statement with its sole proof `sorry`.
