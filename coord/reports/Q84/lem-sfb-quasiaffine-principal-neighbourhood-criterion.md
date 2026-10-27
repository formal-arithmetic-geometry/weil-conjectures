## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffinePrincipalNeighbourhood` states
`AlgebraicGeometry.Scheme.exists_isQuasiAffine_open_iff` with its sole proof `sorry`.
No definitions or extra nodes are needed, and no mathematical statement was changed.
All variables and the universe `u` are explicitly bound; `autoImplicit` is disabled.

Clause-by-clause correspondence:

- A scheme Y: `(Y : Scheme.{u})`, without any quasi-separatedness assumption on Y.
- A subset E: `(E : Set Y)`, with its induced subspace topology.
- Quasi-compactness of E: `(hE : IsCompact E)`. Mathlib's
  `isCompact_iff_compactSpace` identifies this with compactness of the subspace E;
  compactness here has no Hausdorff requirement.
- An open subscheme U: `U : Y.Opens`, with restricted scheme `U.toScheme`.
  Its canonical map `U.ι` is an open immersion. Every open subscheme is represented
  this way up to isomorphism, so this quantification loses no case.
- Clause (i), containment of E: `E ⊆ (U : Set Y)`.
- Clause (i), quasi-compact quasi-affineness: `U.toScheme.IsQuasiAffine`.
  Mathlib's `Scheme.IsQuasiAffine` extends `CompactSpace`; no separate compactness
  conjunct is necessary. Its canonical immersion into Spec of global sections is
  an open immersion. Conversely a quasi-compact open of an affine is quasi-affine
  by `Scheme.IsQuasiAffine.of_isImmersion`, exactly the node's convention.
- Equivalence of (i) and (ii): `↔`.
- Clause (ii), every e in E: `∀ (e : Y), e ∈ E →`.
- Clause (ii), an ambient open V containing all of E: `∃ V : Y.Opens,
  E ⊆ (V : Set Y) ∧ ...`. Thus V is not merely a neighbourhood of e.
- Clause (ii), quasi-separatedness of V: `QuasiSeparatedSpace V.toScheme`.
  `quasiSeparatedSpace_iff_forall_affineOpens` says exactly that intersections
  of affine opens are quasi-compact. No quasi-compactness of V is imposed.
- Clause (ii), a global section on V: `∃ g : Γ(Y, V), ...`. By the construction
  of the restricted structure sheaf, sections of O_V over V are precisely sections
  of O_Y over V, which is what this notation denotes.
- The principal open V_g is written `Y.basicOpen g`, an open of Y contained in V.
  `Scheme.mem_basicOpen''` identifies membership with existence of a germ in V
  which is a unit; this is exactly the given definition of V_g. The restricted
  scheme `(Y.basicOpen g).toScheme` is its open subscheme structure.
- Clause (ii), quasi-affineness and containment of e:
  `(Y.basicOpen g).toScheme.IsQuasiAffine ∧ e ∈ Y.basicOpen g`.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; the local-affine
  structure and full morphism signature were read.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. The canonical open subscheme uses
  `Scheme.Opens.toScheme` and `Scheme.Opens.ι` from Mathlib's restriction API.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`, read at their definitions.
  Mathlib's quasi-affineness uses this Spec in its canonical map.
- Additional existing notions: `Scheme.IsQuasiAffine` from
  `Mathlib.AlgebraicGeometry.QuasiAffine`, `Scheme.basicOpen` from
  `Mathlib.AlgebraicGeometry.Scheme`, `QuasiSeparatedSpace` and its affine-open
  characterization from `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

Proof dependencies are imported privately from their recorded Mathlib source modules
(AffineScheme, Morphisms.QuasiCompact, Morphisms.QuasiSeparated, ResidueField,
RingTheory.Spectrum.Prime.Topology, and QuasiAffine).
`lem-sfb-qcqs-quasiaffine-basic-open-cover` has no local recorded declaration yet,
but its exact fixed-scheme input exists upstream as
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen` in
`WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`, which is imported privately.
This is only a proof dependency, not a missing notion in the theorem's signature.
The docstring supplies every step of the node's finite-cover proof and names its inputs.

Edge cases checked mathematically before writing:

- E empty: the right side is vacuous and the empty open is affine (Spec of the
  zero ring), hence quasi-affine; no Nonempty binder is present.
- Y empty: necessarily E is empty, covered by the preceding case.
- E equal to Y: the statement reduces to the fixed-scheme covering criterion;
  requiring each V to contain all E forces V to be the whole scheme.
- V need not be quasi-compact, separated, affine or equal to Y.
- Y need not be quasi-separated: the finite-cover argument works inside a selected
  quasi-separated V after treating E empty separately.
- g = 0 gives the empty basic open; g = 1 gives all V. Membership excludes the
  former for a selected point, and the latter supplies the forward implication.
- The universe u is unrestricted and preserved by open restriction; no test scheme
  in a smaller independent universe is used.

Source checked: Raynaud, *Un critère d'effectivité de descente*, Lemma 3.7,
printed p.14, and preceding Lemma 3.6. Read the primary Numdam scan:
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf .
The source states the same equivalence and permits varying ambient neighbourhoods.
There is no statement dispute or correction.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder`: “A quasi-compact subset has a quasi-affine open
  neighbourhood iff each point is in a quasi-affine basic open of a global section
  on a quasi-separated neighbourhood of the subset”. Eight hits, including
  `Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`; those concern affine basic
  opens on one fixed scheme and do not state this equivalence for a subset.
- `msearch.py ... loogle`: `"IsQuasiAffine", "basicOpen"`. Two hits, the fixed-scheme
  criterion and its basic-open basis lemma, neither matching this statement.
- `msearch.py ... grep`, subdirectory AlgebraicGeometry:
  `(IsQuasiAffine|quasi.affine).*(basicOpen|neigh)|(basicOpen|neigh).*(IsQuasiAffine|quasi.affine)`.
  Six hits in QuasiAffine and AffineTransitionLimit; none is this criterion.
- `msearch.py ... leansearch`: “Quasi-affine open neighbourhood of a quasi-compact
  subset from principal open neighbourhoods”. Eight hits about affine bases, finite
  affine covers and the fixed-scheme affine-basic-open criterion; no exact match.
- `rg -n` with the same concept pattern and the node id in `lean/WeilConjectures`
  and `lean/Sheaf`: upstream has the fixed qcqs quasi-affine-basic-open criterion
  at `WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean:142`; the only
  neighbourhood-related Sheaf hit is unrelated representability material.
- `rg -n 'exists_isQuasiAffine_open_iff|quasiAffine.*[Nn]eigh|[Nn]eigh.*[Qq]uasiAffine'`
  in Mathlib, WeilConjectures and Sheaf: no matches. The new declaration name is free.

Validation uses only the required `scompile.py` server wrapper and `deliver2.py`.
The initial module compiled cleanly in both sandbox and library module modes.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
