## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum` states
`AlgebraicGeometry.exists_affineOpen_closed_stratum`, with its sole proof `by sorry`.
No definitions are introduced and the node is changed only in `lean`.

Hypothesis and conclusion correspondence:

- The scheme is `Y : Scheme.{u}`, for an explicitly declared arbitrary universe `u`.
- The finite indexed family is `N : ℕ`, `S : Fin N → Set Y`. Relabeling the paper's
  indices 1 through N by 0 through N-1 changes no data.
- Coverage is `hcover : (⋃ i, S i) = Set.univ`; pairwise disjointness is
  `hdisjoint : Pairwise (fun i j ↦ Disjoint (S i) (S j))`.
- Each part is locally closed by `hlocallyClosed : ∀ i, IsLocallyClosed (S i)` and
  constructible by `hconstructible : ∀ i, Topology.IsConstructible (S i)`.
- The given point, selected index, and its membership are `y : Y`, `k : Fin N`,
  and `hy : y ∈ S k`. Disjointness makes this selected index unique; no redundant
  uniqueness hypothesis is added.
- The affine open neighborhood is `∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ ...`.
  Mathlib defines `IsAffineOpen V` as affineness of the open subscheme.
- Clause (1) is `IsClosed (Subtype.val ⁻¹' S k : Set V)`.
- Clause (2) is the conjunction of `IsLocallyClosed` and `Topology.IsConstructible`
  for `Subtype.val ⁻¹' S i : Set V`, universally quantified over `i`.
- Clause (3) is `IsCompact ((Subtype.val ⁻¹' S k : Set V)ᶜ)`. `IsCompact` means
  quasi-compactness without a Hausdorff assumption. All three conclusions use the
  subspace topology on `V`. The complement's openness follows from clause (1), so
  an additional redundant openness conjunct is unnecessary.

Dependency declarations read and used:

- `Mathlib.Topology.Defs.Basic`: `IsLocallyClosed`, the literal open/closed intersection
  definition recorded by `def-weil-locally-closed-subset`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`, the Boolean-subalgebra
  definition recorded by `def-weil-constructible-subset`; `IsRetrocompact`, and
  `Topology.IsConstructible.preimage_of_isOpenEmbedding` (Tag 005J).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen`,
  `AlgebraicGeometry.Scheme.isBasis_affineOpens`, and
  `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.quasiSeparatedSpace_of_isAffine` (the other clause of the
  affine-qcqs proof dependency).
- `Sheaf.Topology.ConstructibleIsRetrocompact`:
  `Topology.IsConstructible.isRetrocompact`.

The last two modules are ordinary proof imports, not public imports. The other
proof dependencies are already available from the public imports. The theorem's
docstring gives all three steps of the node's proof with the corresponding node ids.
The Stacks source passages for Tags 005J, 09YH, and 01IT were read locally and agree
with those steps.

Edge cases checked: for `N = 0` there can be no `k : Fin N`; an empty scheme has no
`y`, so these instances are vacuous as in the node. Empty parts are allowed and cannot
be selected by `hy`; the restrictions of other parts may be empty. With one part the
selected restriction is the whole neighborhood and its complement is empty, hence
quasi-compact. No Noetherian, quasi-compact, quasi-separated, nonempty-stratum,
separation, characteristic, or base-field hypothesis has been added to `Y`.

Searches made before writing:

- `msearch.py ... leanfinder "A finite locally closed constructible partition of a scheme
  has an affine neighborhood of a point on which its stratum is closed and its complement
  is quasi compact"`: eight hits (quasi-separatedness criteria, affine open covers,
  quasi-compact covers, and quasi-affineness), no exact theorem.
- `msearch.py ... loogle "IsLocallyClosed, Topology.IsConstructible, IsAffineOpen"`:
  zero hits, with unknown identifier `IsAffineOpen` reported by the service.
- `msearch.py ... grep "IsLocallyClosed|IsConstructible" AlgebraicGeometry`:
  17 hits on immersions, groups, and finite-presentation images, no exact theorem.
- `rg` in the source project's `WeilConjectures` and this project's `lean/Sheaf`
  for constructible partitions, the item id, and `closed_stratum`: related sheaf
  stratification statements, but no exact theorem or declaration tagged with this id.
- Additional `rg` of `dag/lean_names_upstream.json`, `WeilConjectures`, and `lean/Sheaf`
  for affine-stratum names and the chosen declaration name found no matching theorem.
- Read `WeilConjectures.Topology.Stratification`: it bundles exactly the same finite
  partition data. The present statement takes that data as separate explicit binders;
  it introduces no competing structure or definition.

No statement dispute, correction, new node, or unusable dependency was found.
Server validation is performed only through `scompile.py`; no local Lean compiler is used.


## Second reading by NM

I independently read the node, its entire Lean module, both statement-dependency
nodes, all six proof-dependency nodes and the actual recorded declarations. I read
Stacks topology.tex, Definition 005G and Lemmas 005H, 005J, 09YH, 0901;
schemes.tex, Lemma 01IT; and algebra.tex, Lemmas 00E8 and 090M. The topology
lemmas have exactly their stated topological hypotheses; the affine basis requires
only a scheme. The spectral hypothesis in 0901 is available on the chosen affine
neighborhood, not imposed on the original scheme. The node's three-step proof
uses the more direct 09YH route, correctly reproduced in the docstring.

Object, hypothesis and conclusion checklist (all verdicts: exact):

- An arbitrary scheme Y: `(Y : Scheme.{u})`, with explicitly bound arbitrary `u`.
- A finite family of subsets indexed 1 through N: `(N : ℕ)` and
  `(S : Fin N → Set Y)`. Zero-based indexing merely relabels this finite set.
- The family covers Y: `(hcover : (⋃ i, S i) = Set.univ)`.
- Distinct parts are disjoint:
  `(hdisjoint : Pairwise (fun i j ↦ Disjoint (S i) (S j)))`.
- Every part is locally closed: `(hlocallyClosed : ∀ i, IsLocallyClosed (S i))`.
  I opened `IsLocallyClosed`: it literally requires an open/closed intersection,
  exactly the recorded dependency's notion.
- Every part is constructible:
  `(hconstructible : ∀ i, Topology.IsConstructible (S i))`.
  I opened its Boolean-subalgebra definition and `IsRetrocompact`: these use open
  retrocompact generators, matching Definition 005G through Lemma 005H as explained
  in the dependency node. This is global constructibility, as the node requires.
- A point and its selected stratum: `(y : Y) (k : Fin N) (hy : y ∈ S k)`.
  Coverage and disjointness give existence and uniqueness of this selection; the
  selected index remains universally quantified before the existential neighborhood.
- An affine open subscheme containing that point:
  `∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ ...`.
  I opened `IsAffineOpen`: it is `IsAffine` of that actual open subscheme.
- Clause (1), selected intersection closed in V:
  `IsClosed (Subtype.val ⁻¹' S k : Set V)`.
- Clause (2), every intersection locally closed and constructible in V:
  `(∀ i, IsLocallyClosed (Subtype.val ⁻¹' S i : Set V) ∧
    Topology.IsConstructible (Subtype.val ⁻¹' S i : Set V))`.
  Subtype preimages express the intersections in the induced topology, not in Y.
- Clause (3), the open complement is quasi-compact:
  `IsCompact ((Subtype.val ⁻¹' S k : Set V)ᶜ)`.
  Openness follows exactly from clause (1), so it needs no separate conjunct.
  Mathlib compactness here has no Hausdorff requirement.

The recorded affine-basis, open-restriction, affine-compactness and
quasi-separatedness signatures were opened in Mathlib. I also opened the whole
`Sheaf.Topology.ConstructibleIsRetrocompact` module: its statement quantifies over
arbitrary topological spaces without extra instances. These are usable dependencies;
none needs replacement. There are no new definition nodes or dependency modules
in this delivery, and no statement correction needing citer checks.

Edge cases: `N = 0` has no `k : Fin N`; the empty scheme has no `y`, exactly
matching the pointed assertion's vacuous cases. Empty strata are permitted, but
`hy` excludes selecting one. With a single stratum the complement is empty.
No nonempty, Noetherian, qcqs, separated, characteristic, field, coefficient,
or additional universe restriction is present. Zero-object and characteristic
cases impose no additional condition because the assertion is purely about schemes
and their underlying subsets.

Independent H4 searches (different wording from the first reader):

- LeanFinder via msearch: "A point in a constructible locally closed subset of a
  scheme has an affine neighbourhood where that subset is closed with compact
  complement": eight ingredient hits on locally constructible sets, prime-spectrum
  closedness and compact opens; no exact neighborhood theorem.
- Loogle via msearch: `IsLocallyClosed, IsCompact`: one unrelated locally-integrable
  theorem; no exact match.
- LeanSearch via msearch: "An affine open neighbourhood of a point makes its
  locally closed constructible stratum closed and has quasi compact complement":
  unavailable (Internal Server Error), recorded as unavailable, not a negative result.
- msearch grep `IsLocallyClosed|IsConstructible` in AlgebraicGeometry: 17 ingredient
  hits (immersions, groups, finite-presentation images); no exact match.
- Local rg over Mathlib AlgebraicGeometry, upstream WeilConjectures and project
  lean/Sheaf with `closed_stratum`, `constructible.*partition`,
  `partition.*constructible`, `exists.*affine.*[Cc]losed`, `[Cc]losed.*[Ss]tratum`
  found stratification and sheaf statements, not this theorem. Exact-name search
  of upstream name inventory and both project libraries found no collision.
- I opened upstream `Topology.Stratification` and its fields: it bundles the same
  data used by these explicit binders. This delivery introduces no replacement
  structure or definition, so there is no duplicate notion.

No mathematical or Lean mismatch was found; no Lean or node change was needed.
The module has one named theorem with whole proof `sorry`, no definitions or
private helpers, and no file-local notation or instances. Both docstrings include
the source and blueprint tag; the theorem docstring includes all three proof steps.
I checked that `lean.statement` equals the file signature verbatim and that all
lines satisfy the 100-character convention. The second reading changes only this
report, adding the independent audit.

Server scompile.py validation passed cleanly: 1.3 seconds, nice 19, two threads,
60-second per-file limit; no errors or warnings. No local compiler was invoked.
