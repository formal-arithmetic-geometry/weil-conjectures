## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGroupRelativeNeutralOpen` states
`AlgebraicGeometry.GrpObj.smoothGroup_relativeNeutralOpen`. Its sole theorem has
proof `sorry`; no definitions, axioms or auxiliary postponed results are introduced.
The node is unchanged outside `lean`.

The source was read in BLR, Néron Models, §6.4, printed p. 154 (PDF p. 160),
paragraph following Proposition 2, in the primary scan linked by the node:
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf .
That paragraph identifies the open by the union of the fibre identity components
and states geometric connectedness. The arbitrary-base-change identification was
also read in Stacks `more-morphisms.tex`, Situation `situation-connected-along-section`
and Lemma `lemma-base-change-connected-along-section` (055M); openness was read
in `lemma-connected-along-section-open` (055R).

Hypothesis and clause correspondence:

- The discrete valuation ring is `(C : Type u) [CommRing C] [IsDomain C]
  [IsDiscreteValuationRing C]`. This includes the nonfield condition of the node's
  recorded DVR notion. The base is literally `Spec (.of C)`.
- The scheme over this base is `(G : Over (Spec (.of C)))`; its structure map is
  `G.hom`. `[GrpObj G]` supplies the multiplication, identity, inverse and group
  diagrams over this base. The recorded `CategoryTheory.GrpObj` is general in its
  cartesian monoidal category, so its use over this ring rather than over a field
  needs no replacement of the dependency's definition.
- Smoothness and separatedness are `[Smooth G.hom] [IsSeparated G.hom]`.
  `IsSeparated` means exactly a closed-immersion diagonal. Finite type is
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, as recorded by the dependency.
- The open subscheme is `∃ U : G.left.Opens`. Its scheme and inclusion are the
  existing `U.toScheme` and `U.ι`. Thus the inclusion is an open immersion without
  adding a hypothesis or giving the open a different scheme structure.
- The first four conjuncts state smoothness, separatedness, local finite type and
  quasi-compactness of `U.ι ≫ G.hom`, exactly smooth separated finite type over S.
- `GeometricallyConnected (U.ι ≫ G.hom)` states connectedness of every fibre after
  every residue-field extension. This existing Mathlib predicate quantifies over
  field-valued base changes. In particular it includes nonemptiness, rather than
  mere preconnectedness.
- For arbitrary `(T : Scheme.{u}) (t : T ⟶ Spec (.of C))`, the inverse-image open
  under `pullback.fst G.hom t` equals the fibrewise connected-component locus of
  the pulled-back identity section `η[(Over.pullback t).obj G].left`. The fibre
  subspace is `((pullback.snd G.hom t) ⁻¹' {(pullback.snd G.hom t) x})` and
  `connectedComponentIn` selects the component through that section. Scheme fibres
  have this underlying subspace via `Scheme.Hom.fiberHomeo`, as in the recorded
  section-component dependency. Consequently the base-changed open is precisely
  the neutral open of the base-changed group. Equality of opens determines their
  restricted structure sheaves and open subschemes, not just an abstract isomorphism.
  Unique restriction of the group operations makes this a group identification.
  No finite-type, Noetherian, reducedness or other restriction is imposed on T.
- For every `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and geometric point
  `s : Spec (.of Ω) ⟶ Spec (.of C)`, the inverse-image open equals
  `connectedComponent (GrpObj.onePoint ((Over.pullback s).obj G))` in the actual
  fibre product. This states the geometric-fibre identity-component clause.
- In that same geometric fibre, `Set.range` of the subsets
  `(GrpObj.mulRight ((Over.pullback s).obj G) g).left '' preimage(U)` as g runs over
  all Ω-rational points equals `Set.range (fun x => connectedComponent x)` as x
  runs over every scheme point. The left-multiplication orbit through g is G⁰g,
  hence it is RIGHT translation of G⁰ by g. The formula equates the family of all
  these orbit opens with the family of all components, including components
  represented by nonclosed scheme points. It uses the entire translated open,
  not just its rational points. Right translation is an existing automorphism, so
  these are the translated open subschemes with their full restricted sheaves.
- Finally `∃ gU : GrpObj (Over.mk (U.ι ≫ G.hom))` supplies the subgroup's actual
  group structure, and the explicit `@IsMonHom ... gU.toMonObj ...` says its
  inclusion is a homomorphism. An open immersion is a monomorphism, so this is
  precisely an open subgroup. No `IsCommMonObj` or `ConnectedSpace G.left` binder
  is present; no commutativity or connectedness of G is required.

All variables and universes are explicitly bound, with `autoImplicit false`.
The base, group, field-valued points and test schemes use the same arbitrary
scheme universe u, as in the project's base-change and group-scheme interfaces.
There is no separate smaller test universe which could make a condition vacuous.
The scoped CategoryTheory.Obj instance transports the given group object through
`Over.pullback`; it introduces neither an arbitrary group law nor a new definition.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (through the public imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the same existing
  group-object interface supplies `IsMonHom`, `MonObj.one`, and pullback group laws.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and the canonical open-subscheme interface `Scheme.Opens.ι`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `...Separated`:
  `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsSeparated`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent` and
  `connectedComponentIn`; `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.GeometricallyConnected`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  `def-pc-base-change` interface, explicitly documenting scheme base change as
  `Over.pullback`/`Limits.pullback` and its projections (rather than the module-only
  `Scheme.Modules.moduleBaseChange`, which is irrelevant here).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint` and
  `GrpObj.mulRight`. These are the existing identity and translation constructions.

Every already stated proof dependency is imported, with proof-only imports plain:
`SectionComponentPullback` (section-component pullback theorem), `Morphisms.SlicingFlat`
(quasi-compactness of the section-component locus), `Morphisms.SmoothFiber` (smoothness
criterion), `Geometrically.Reduced` (smooth geometrically reduced fibres),
`FlatReducedSectionComponentOpen`, `LocallyAlgebraicGroupIdentityComponent`, and
`GroupNeutralComponentTranslates`. The proof's finite-presentation, smooth restriction,
quasi-separatedness and closed-immersion base-change Mathlib modules are available
through the public imports. There are no omitted proof-dependency imports or known cycles.
The theorem docstring reproduces all six proof steps and names their DAG inputs.

Edge cases checked before writing:

- An empty group over this nonempty trait is excluded by the identity section,
  rather than by an extra nonemptiness hypothesis; the trivial group is included.
- Disconnected and noncommutative groups are included, e.g. constant finite
  nonabelian groups: the relative open is their identity copy of the base and
  the translates give all singleton geometric components.
- Positive and mixed characteristic are allowed; Ω is not assumed characteristic
  zero. No properness, affineness or connectedness hypothesis on G is present.
- For geometrically connected fibres, U can be all of G and the orbit family has
  one member. For varying components the assertion does not incorrectly require
  U to be closed in the total scheme.
- Empty T is included; both sides of its base-change equality are empty. Identity
  base change, geometric points, nonreduced T and arbitrary non-Noetherian T are
  included without additional assumptions.
- The component family ranges over every underlying scheme point, not only closed
  points. Rational translating points suffice because the geometric fibre is of
  finite type over an algebraically closed field, as in the recorded translation
  dependency. The side of translation is chosen for LEFT subgroup multiplication.

Searches for an existing statement:

1. `msearch.py leanfinder`, query "For a smooth separated finite type group scheme
   over a discrete valuation ring the fibrewise identity components form an open
   subgroup, commute with base change, and its geometric orbits are connected
   components": 8 hits, on Galois-category open subgroups, Galois fixing subgroups,
   and finite-morphism fibres; no statement of this theorem.
2. `msearch.py loogle`, query `CategoryTheory.GrpObj, connectedComponent`: 0 hits.
3. `msearch.py grep`, query `neutral|identityComponent|connectedComponent`, restricted
   to Mathlib/AlgebraicGeometry: 8 hits, constant-sheaf connected components and
   `Scheme.Hom.connectedComponentsHomeomorph`; no relative neutral subgroup theorem.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for relative neutral/identity opens,
   fibrewise identity, and the proposed name: no matching relative statement.
   `grep -rn` for this exact node id in `lean/WeilConjectures`: no hits. Broader
   group-component searches found the existing field-only identity components and
   translation interfaces, which are reused here, and the two recorded field
   theorem modules imported for the proof.
5. The example CompactObject node was read: its old Sheaf example is now withdrawn,
   so its recorded upstream module was read for the current header conventions.

No statement correction, dependency replacement or new definition node is needed.
No statement is disputed.

Validation: `scompile.py` accepted the complete module against current server sources
in 5.4 seconds, with no errors or warnings other than the permitted postponed proof.
An initial elaboration failure was repaired by writing `↥(pullback ...)` explicitly
for point types; otherwise Lean inferred the categorical pullback in `Type`.
The wrapper reported local ENOSPC and successfully used its prescribed server fallback.

## Retry validation, 2026-10-24

The resumed worker retained the saved packet and ran the required
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push` twice.
Both attempts exited 1 during server compilation of
`Sheaf.AlgebraicGeometry.SmoothGroupRelativeNeutralOpen` with
`resource exhausted (error code: 28, no space left on device)`. Nothing was pushed.
The current-node comparison confirms that only `lean` differs; the recorded
signature matches the module verbatim, its maximum line width is 94, and it
contains exactly one postponed theorem proof. The delivery remains preserved
for retry after server storage is available; no launcher or shared files were edited.

## Dispatcher retry validation, 2026-10-24

This resumed attempt inspected the retained report and packet, then ran the
required `deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push`
twice. Both exited 1 with the same server-side diagnostic:

```text
COMPILE FAILED on the server, nothing pushed:
sandbox Sheaf.Stage2.Sandbox0

[3.6 s]
library Sheaf.AlgebraicGeometry.SmoothGroupRelativeNeutralOpen
resource exhausted (error code: 28, no space left on device)

[4.1 s]
```

The consistency check against current local sources again found that only `lean`
differs in the saved node, the signature matches verbatim, every line is at most
94 characters, `autoImplicit` is disabled, and there is exactly one postponed
theorem proof. No Lean source changes were indicated by these diagnostics.
The packet is retained; no push was attempted, and no shared repository or
launcher file was edited. Delivery is blocked by server storage exhaustion.

## Final dispatcher retry, 2026-10-24

The retained packet was inspected and the prescribed dry run was run twice.
Both attempts exited 1 while compiling the library module on the server:
`resource exhausted (error code: 28, no space left on device)`.
The failure occurred after the sandbox probe and before a successful compile or push.
No source repair is indicated by this infrastructure diagnostic.
The saved node still differs from the current read clone only in `lean`; its
recorded signature matches the module, all lines are at most 94 characters,
`autoImplicit` is disabled, and its sole postponed proof is `sorry`.
The source packet remains intact for another retry. No shared repository or
launcher files were modified, and nothing was pushed.


## Second reading by Q148

On resumption on 2026-10-24, I reopened the saved node and the complete Lean
module. The DVR and affine base are `C`, `IsDiscreteValuationRing C` and
`Spec (.of C)`; the group scheme is `G : Over (Spec (.of C))` with `GrpObj G`.
The four structure-map assumptions express smoothness, separatedness and finite
type (local finite type plus quasi-compactness). The existential open `U`, its
canonical inclusion, and the final group-object structure with `IsMonHom`
express the open subgroup. The first four conjuncts repeat the required
properties for its structure map. `GeometricallyConnected` expresses the
geometrically connected fibres. The unrestricted `T, t` equality expresses
base change by the fibrewise identity-section component locus. The equality
for each algebraically closed field point identifies the geometric fibre with
the identity component; the equality of the two ranges identifies the right
translates, which are left-multiplication orbits, with all connected components.
There are no commutativity or connectedness assumptions on G. No statement or
source changes were made. The recorded signature was checked verbatim, every
line has at most 94 characters, automatic implicits are disabled, and the only
postponed proof is the theorem's `sorry`.

## Current retry outcome, 2026-10-24

This attempt ran the prescribed `deliver2.py Q148
lem-sfb-smooth-group-relative-neutral-open --no-push` twice. Both exited 1
after the sandbox probe, while compiling the library module, with:
`resource exhausted (error code: 28, no space left on device)`.
Neither attempt reached a successful compile or push. This is a server storage
failure; no source repair is indicated. The packet is preserved, and only this
sandbox report was updated. No shared repository or launcher files were edited.


## Saved-packet retry, 2026-10-24

This resumed worker inspected the saved report and module and ran the prescribed
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push` twice.
Both exited 1 during server compilation of
`Sheaf.AlgebraicGeometry.SmoothGroupRelativeNeutralOpen`, after the sandbox probe,
with `resource exhausted (error code: 28, no space left on device)`.
The second run reproduced the first failure; no source diagnostic was reported.
The packet remains intact: only `lean` differs from the current read-clone node,
the signature matches verbatim, maximum line width is 94, automatic implicits
are disabled, and the only postponed proof is the named theorem's `sorry`.
No repair note exists for this item. No shared repository or launcher files were
modified. Nothing was pushed; the failure is server storage exhaustion.

## Resumed server-storage check, 2026-10-24

Inspected the retained report, node and complete module. Two prescribed
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push`
runs both exited 1 after the sandbox probe, during server compilation of
`Sheaf.AlgebraicGeometry.SmoothGroupRelativeNeutralOpen`, with
`resource exhausted (error code: 28, no space left on device)`.
No Lean diagnostic was emitted and nothing was pushed. The saved node differs
from the current read clone only in `lean`; the recorded signature matches
the module verbatim, maximum line width is 94, `autoImplicit` is disabled,
and exactly one postponed theorem proof remains. No repair note is present.
The packet is retained without source changes; only this sandbox report was
updated. The server storage failure persists.

## Latest prescribed retry, 2026-10-24

Inspected the retained report, complete module and node, then ran the prescribed
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push` twice.
Both exited 1 during server compilation of the library module, after the sandbox
probe, with `resource exhausted (error code: 28, no space left on device)`.
No Lean source diagnostic appeared and nothing was pushed. The current read-clone
comparison confirms only `lean` differs; its signature matches the module verbatim,
maximum line width is 94, `autoImplicit` is disabled, and exactly one named theorem
has a postponed proof. No source repair is indicated by the server storage failure.
The packet is preserved; only this sandbox report was updated.

## Prescribed retry, 2026-10-24 11:03 UTC

Inspected the retained report, node and complete Lean module, then ran the
prescribed `deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open
--no-push` twice. Both exited 1 during server compilation of
`Sheaf.AlgebraicGeometry.SmoothGroupRelativeNeutralOpen`, after the sandbox
probe, with `resource exhausted (error code: 28, no space left on device)`.
No Lean source diagnostic appeared and nothing was pushed. The consistency
check found only `lean` differs from the current read-clone node; the recorded
signature matches verbatim, maximum line width is 94, automatic implicits are
disabled, and the sole postponed proof is the named theorem. No repair note
was found. The packet is retained; only this sandbox report was updated.

## Retained-packet dry run, 2026-10-24 11:05 UTC

Inspected the retained report, complete module and node. Both prescribed
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push`
attempts exited 1 during server compilation of the library module, after the
sandbox probe, with `resource exhausted (error code: 28, no space left on device)`.
No Lean source diagnostic appeared and nothing was pushed. The self-check confirms
that only `lean` differs from the current read-clone node, its signature matches
the module verbatim, maximum line width is 94, `autoImplicit` is disabled, and
the sole postponed proof belongs to the named theorem. No repair note is present.
The packet is preserved; only this sandbox report was updated. The persistent
server storage failure prevents completing the dry run and delivery.

## Resumed dry-run result, 2026-10-24 11:08 UTC

Inspected the retained report, module and node and ran the prescribed
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push` twice.
Both exited 1 during server compilation of the library module, after the sandbox
probe, with `resource exhausted (error code: 28, no space left on device)`.
No Lean source error was reported and nothing was pushed. The saved node differs
from the current read-clone node only in `lean`; the signature matches verbatim,
maximum line width is 94, automatic implicits are disabled, and the only postponed
proof is the named theorem's `sorry`. No repair note exists for this item.
The packet is retained without source changes. Only this sandbox report changed;
no shared repository or launcher files were edited. Server storage exhaustion
prevents completing the required dry run and delivery.

## Retained-packet infrastructure retry, 2026-10-24 11:10 UTC

Inspected the saved report, complete module and node, and ran the prescribed
`deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open --no-push` twice.
Both exited 1 during server compilation of the library module, after the
sandbox probe, with `resource exhausted (error code: 28, no space left on device)`.
No Lean source diagnostic appeared; neither attempt pushed anything.
Self-check: only `lean` differs from the current read-clone node, the recorded
signature matches verbatim, maximum line width is 94, `autoImplicit` is disabled,
and the sole postponed proof is the named theorem's `sorry`. No return entry
names this item. The packet is retained without source changes; only this
sandbox report was updated. The repeated server storage failure prevents
completion of the required dry run and delivery.

## Successful retained-packet validation, 2026-10-24

The prescribed `deliver2.py Q148 lem-sfb-smooth-group-relative-neutral-open
--no-push` passed: commit `599674651a9` passed server preflight and the
per-file compile. The earlier server storage failure did not recur.
The saved module and statement were retained. The node differs from the
current read-clone node only in `lean`; its recorded signature matches the
file verbatim up to the theorem body delimiter (including the named argument
`V := G`). Maximum line width is 94, automatic implicits are disabled,
and the sole postponed proof is the named theorem. No repair note is present.
The existing second reading was checked against the open node and module:
the DVR base, group structure, smooth separated finite-type hypotheses,
open subgroup structure, geometric identity-component fibres, geometrically
connected fibres, arbitrary base change and left-multiplication orbit clauses
all have the renderings recorded above. No source or statement repair was needed.
