## Worker report

The module `Sheaf.AlgebraicGeometry.TameLogQuotientModification` states
`AlgebraicGeometry.exists_logRegular_modification_of_tame_quotient`, with `sorry`.
No definitions or other theorems are added. The node's statement, statement dependencies,
and proof are unchanged. The module docstring contains all seven proof steps.

Hypotheses and clauses, checked against the node:

- The schemes C and X have universe u. Integral C and X are `[IsIntegral C]` and
  `[IsIntegral X]`. Noetherianity is `[IsNoetherian C]`, `[IsNoetherian X]`;
  Mathlib's class includes local Noetherianity and quasi-compactness.
- Excellence on C and X is `_hC` and `_hX`, the recorded `IsExcellent` predicate on
  every affine coordinate ring. Scheme separatedness is `[C.IsSeparated]`: the
  structure morphism to the terminal scheme (Spec Z) has closed-immersion diagonal.
- The given boundary B is represented by `(U : Set C)ᶜ`, for `U : C.Opens`.
  It is closed, and `hU : DenseRange U.ι` says its open complement is dense, hence
  B is nowhere dense. This is equivalent to the node's closed nowhere dense subset.
  `_hlog` applies the exact recorded divisorial fs log regular pair declaration
  to the inclusion of that complement, not to an arbitrary log structure.
- A finite group is `G : Type v` with `[Group G] [Finite G]` (the group universe
  is independent of the schemes). The action is the Mathlib monoid homomorphism
  `a : G →* Aut C`, so all group laws and all scheme automorphisms are specified.
- `_horder` says `Nat.card G` is a unit at every scheme stalk. This is precisely
  invertibility on C; it is not a global characteristic-zero restriction.
- `_hboundary` says membership of U is invariant under every group element;
  equivalently the closed complement B is preserved.
- `_hfree` supplies a dense invariant open V and says the stabilizer of each
  geometric point in V is trivial: for algebraically closed Ω, `t ≫ (a g).hom = t`
  implies `g = 1`. This does not confuse geometric freeness with freeness on
  the underlying prime ideals. It permits e.g. nontrivial actions on a field.
- `_hadmissible` supplies an affine open W containing every `(a g).hom x` for
  each x, exactly the admissibility condition in the node.
- The quotient map is `π : C ⟶ X` with `[IsFinite π]`. `hπ` is invariance as
  scheme morphisms. `_hquot : Topology.IsQuotientMap π` supplies surjectivity
  and the quotient topology; `_horbits` identifies its underlying point fibres
  exactly with the G-orbits.
- `_hsheaf` specifies the invariant structure sheaf using the CANONICAL
  `π.app W` on EVERY open W of X. It is injective, and its image is exactly
  the sections fixed by every a(g). The `eqToHom` is the equality of preimage
  opens induced by `hπ g`; contravariant restriction transports the original
  section into precisely the same ring as `(a g).hom.app`. There is no freely
  chosen identification or comparison map. Thus the compatible sectionwise
  identifications give O_X = (π_* O_C)^G as ring sheaves.
- The conclusion quantifies an actual scheme M, integrality and Noetherianity
  witnesses, and `ρ : M ⟶ X`. Its first conjunct is `IsProper ρ`; the second
  asserts `IsExcellent` on every affine coordinate ring of M.
- Birationality is the existence of `e : M.PartialIso X` with
  `e.source.ι ≫ ρ = e.iso.hom ≫ e.target.ι`. Mathlib's PartialIso includes
  density of both opens and their scheme isomorphism. The equation forces
  this to be the restriction of ρ, rather than just abstract birationality.
- The resulting boundary is `(UM : Set M)ᶜ`. The open UM and
  `hUM : DenseRange UM.ι` give closedness and nowhere density. The exact recorded
  divisorial log regular predicate gives log regularity. The last conjunct
  `ρ ⁻¹' (π '' ((U : Set C)ᶜ)) ⊆ (UM : Set M)ᶜ` is precisely the required
  inverse-image inclusion, with no extra requirement on the new boundary.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (and its full definition via
  quasi-excellence and universal catenarity).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, used by excellence;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`, with its full
  geometric-stalk, chart, rank, and stratum definition inspected.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated` and `.ClosedImmersion`:
  `Scheme.IsSeparated`, `IsSeparated`, `IsClosedImmersion` (transitive imports).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, used by separatedness (transitive import).
- Standard additional Mathlib interfaces, not private copies:
  `CategoryTheory.Aut`, `Scheme.Hom.app`, `Scheme.PartialIso`,
  `Topology.IsQuotientMap`, `DenseRange`, and the ordinary set operations.

All already-stated proof dependencies are imported: finite-type/proper interfaces,
`Sheaf.RingTheory.IsExcellentFiniteTypeLocalization`,
`Sheaf.AlgebraicGeometry.FiniteOverProjective`,
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`,
`Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition`.
The proper-target-local declaration is in the proper module. The four currently
unstated proof dependencies (Gabber modification, projective finite quotient,
very tame quotient log regularity, and relative affine-open gluing) have no
recorded module, so no import can yet be added for them. They are not needed to
form this statement. No import cycle is introduced.

Edge cases checked: B empty (U = top) is allowed; the resulting boundary can be
nonempty. The trivial group has order one and the identity quotient is allowed.
Nontrivial generic Galois field actions are allowed because `_hfree` uses maps
from Spec of an algebraically closed field. Positive characteristic is allowed
exactly where the finite group order is invertible. The empty scheme is excluded
by the given integrality, not by an added hypothesis. M's boundary cannot be all
of M because its complement is dense and M is integral. The theorem makes no
extra finite-dimensionality, field, projectivity, or coefficient assumptions.

Searches for an existing statement/interface:

- msearch.py leanfinder: "A tame finite group action on a log regular scheme
  admits a proper birational log regular modification of its quotient" returned
  eight hits, concerning normalization and finite Galois-category quotients,
  none with the log regular modification statement.
- msearch.py loogle: "Scheme, IsProper, IsIntegral" gave zero hits with unknown
  identifier Scheme. The fully qualified retry
  "AlgebraicGeometry.IsProper, AlgebraicGeometry.IsIntegral" was recorded as
  UNAVAILABLE by msearch.py (the curl service timed out after 40 seconds); no
  mathematical verdict is inferred from that unavailable search.
- msearch.py grep: "logRegular|LogRegular|[Tt]ame.*[Qq]uotient" in AlgebraicGeometry
  returned zero Mathlib hits.
- rg in upstream WeilConjectures, the side project's lean/Sheaf, and the upstream
  declaration-name index found no item id or theorem name match. Searches for
  generic freeness, admissible scheme action, scheme quotient, and very tame
  action found no existing interfaces. Existing divisorial log regularity,
  excellence, and partial isomorphisms were used as recorded above.

Source checked in the local ILO PDF: printed p. 85 (VIII 1.1), pp. 73--75
(VI 3.2), and printed p. 134 (IX 2.3--2.4). The latter gives the equivariant
modification/quotient diagram and the boundary inclusion used by this node.
No statement correction, new definition node, dependency repair, or dispute.

Compilation: the prescribed scompile.py wrapper compiled both the sandbox and
library form successfully, with no errors or warnings (2.5 s and 2.1 s).

## Second reading by Q111

Author self-check, not an independent reader: reopened the node and the final
module, and checked every hypothesis and conclusion as listed above. In
particular, the invariant sheaf uses the actual π section map, the equality of
opens has the correct contravariant direction, geometric freeness uses Ω-points,
and the PartialIso is explicitly compatible with ρ. Dense open complements
encode arbitrary nowhere dense closed subsets without choosing scheme structures
on boundaries. All definitions are the recorded interfaces; no data is postponed.
The maintainer supplies the independent reading under the dispatcher's brief.
