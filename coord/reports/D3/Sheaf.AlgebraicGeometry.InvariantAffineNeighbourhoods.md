## What changed

Repair of the returned delivery: removed both identical private
`transport_left_naturality` declarations. The single proved declaration now lives in
`Sheaf.AlgebraicGeometry.TransportLeftNaturality`; both the orbit and neighbourhood
modules import it as a private proof import. This avoids an import cycle between those
modules and uses the existing source-library `transport_homMk_comp` field. Added a
node for this shared theorem and updated both users' proof dependencies. No new hole,
statement change, definition change, or public-import change is introduced.

Proved the unchanged `exists_invariant_affine_neighbourhood` signature from one new
geometric shrinking theorem. Added `DescentOrbitSaturated.lean` with a complete proof
of orbit saturation, and `DescentNormAffineShrinking.lean` with the remaining norm
construction. Updated the item's proof route and recorded both new nodes. All
additional imports are private proof imports; the item's public imports stay unchanged.

The proof constructs the universal transport target on V ×_Y X, proves orbit finiteness,
point membership via the identity section, containment over an affine base open, and
finite-set affine shrinking using the existing source-library prime-avoidance theorem.
It finally proves arbitrary-test-scheme invariance directly by pullback lifting and
transport naturality. The orbit module constructs composition and inversion from the
cartesian square and cocycle, then lifts pairs of compatible points using Mathlib's
scheme pullback point theorem. No geometric-point or separability assumption is added.

## Proved and sorry left

- `CategoryTheory.Over.DescentDatum.exists_invariant_affine_neighbourhood`: original
  hole removed, with the original signature preserved. This is a decomposition,
  not yet an axiom-free proof, because it depends on the one theorem below.
- `CategoryTheory.Over.DescentDatum.descent_orbit_saturated`: completely proved;
  node `lem-pd-descent-orbit-saturated`. The shared naturality theorem is proved too.
- `CategoryTheory.Over.DescentDatum.transport_left_naturality`: fully proved once
  in its shared module, node `lem-pd-transport-left-naturality`.
- The only remaining sorry in the delivery is
  `CategoryTheory.Over.DescentDatum.exists_descent_norm_affine_shrinking`, node
  `lem-pd-descent-norm-affine-shrinking` in its own new module. It is strictly part
  of the argument: it assumes a finite saturated set already placed in an affine
  open, and neither constructs an orbit, uses the finite-subset affine hypothesis,
  chooses an affine base neighbourhood, nor proves test-scheme transport invariance.

Hole accounting: one original hole closed
(`CategoryTheory.Over.DescentDatum.exists_invariant_affine_neighbourhood`), one hole
added (`CategoryTheory.Over.DescentDatum.exists_descent_norm_affine_shrinking`),
net zero before any import-closure pruning. The new orbit theorem adds no hole.
The original theorem is not yet axiom-free; this delivery is a decomposition.

All four modules compiled cleanly in import order. The orbit theorem uses only
standard axioms (verified by the compiler axiom print). The upper theorem retains
sorryAx through the explicitly reported norm theorem.

## No longer needed

The duplicated private naturality proofs in `InvariantAffineNeighbourhoods` and
`DescentOrbitSaturated` are no longer needed; each uses the shared theorem.

Removed proof imports `Sheaf.AlgebraicGeometry.BaseChangeConventions` and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`. No geometric-fibre,
fibre-degree, globally bounded degree or auxiliary base-change convention is used.
The direct proof-dependency edge to `def-pc-base-change` is replaced by
`def-pc-fibre-product`; the former's convention module is unnecessary here.
`def-pc-finite-locally-free` remains relevant to the norm lemma, but its FiberDegree
class wrapper is unnecessary. Prime avoidance is retained through the already proved
`IsAffineOpen.exists_basicOpen_le_of_finite`, rather than re-proved in a new module.
No unit statement or unit proof step is bypassed; this is the original 03JE route.
No claim is made that either removed module is globally unreachable from other targets.
Of the old direct proof dependencies, `def-pc-base-change` is no longer used and
`def-pc-finite-locally-free` now occurs through the norm-shrinking node rather than
as a direct proof step; `def-pd-descent-datum` and
`lem-weil-pbc-prime-avoidance` remain direct dependencies.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified the repeated private helper: private visibility did
not justify proving the same fact in two modules. This repair extracts the helper
into one common dependency instead of importing the upper theorem and creating a
cycle. The earlier second reading below describes the pre-repair version only.

The original DAG's second step referred to the norm construction but had no theorem
stating it. Its existing dependencies were definitions and prime avoidance, which
cannot alone supply that construction. The new norm node states precisely that missing
part. There is no statement dispute and no existing signature or definition change.
The source was read at Stacks Tags 03JE and 0H8K; 03JE's construction works for any
finite saturated set in an affine open, not only one orbit. The original affine-base
localization is performed using the proved prime-avoidance interface.

Searches: LeanSearch returned Internal Server Error (recorded as unavailable).
LeanFinder returned affine-cover/finite-morphism interfaces, with no groupoid theorem;
Loogle's unqualified IsAffineOpen query was unrecognized. Grep of Mathlib and both
project roots found no matching groupoid norm theorem. Source-library searching found
the usable finite-set prime-avoidance theorem. Blueprint searches for invariant affine,
norm and orbit found no existing node stating either new lemma. The ancestor helper
returned None because the original node's created.item is a module name; the new
blueprint links follow that node's existing thm-pd-effective-descent ancestor instead.

Edge cases: saturation is proved for every scheme point, including nonclosed points,
using scheme pullback lifting. No finiteness or flatness is needed for that theorem.
For the norm lemma, S empty permits the empty affine open, and varying finite local
ranks are allowed; p need not be surjective. For p the identity the groupoid transports
are identities and the shrinking can be A itself. Nonreduced finite flat fibres are
covered by the norm's residue-algebra unit criterion. Empty V makes the original
point-quantified theorem vacuous. These checks do not change any hypotheses.

## New nodes

`lem-pd-transport-left-naturality` /
`Sheaf.AlgebraicGeometry.TransportLeftNaturality`: the single shared, fully proved
wrapper of the source-library naturality field, with explicit binders. Both users
import it. No hole is added, and no existing library interface changes.

`lem-pd-descent-orbit-saturated` / `Sheaf.AlgebraicGeometry.DescentOrbitSaturated`:
fully proved orbit saturation for the cartesian transport groupoid, independent of
finite-flat assumptions. The proof includes composition, inversion and point lifting.

`lem-pd-descent-norm-affine-shrinking` /
`Sheaf.AlgebraicGeometry.DescentNormAffineShrinking`: the sole remaining geometric
construction, following 03JE's complement-of-saturation, prime-avoidance and norm
argument. Its docstring and DAG provide the construction and the norm unit criterion.
No change records are needed.


## Earlier second reading (a previous round; superseded)

1. Compared the existing module with the read-only repository using `diff`, then
   checked the existing theorem signature programmatically: byte-for-byte identical.
   Its docstring and public imports are unchanged. No existing definition, instance,
   target statement or other module is modified. Verdict: pass; no change record needed.
2. Read every proof and compiled all three modules locally in import order with
   `lcompile.py`: no errors or warnings. Scanned for forbidden declarations and
   attributes, and for holes: the sole `sorry` is the named norm theorem. A scratch
   `#print axioms` check gives exactly `propext`, `Classical.choice`, `Quot.sound`
   for `descent_orbit_saturated`; the norm theorem and the original theorem also
   have `sorryAx`, as reported. No definition has a hole. Verdict: pass as a
   decomposition, not an axiom-free proof of the original theorem.
3. Independently read Stacks 03JE and 0H8K. The norm statement is the geometric
   shrinking step for an already finite saturated set in an affine open; it does
   not duplicate the original point-neighbourhood statement. Saturation supplies
   the full orbit condition needed by the norm construction. Checked empty S,
   empty schemes, identity p, nonsurjective p, varying ranks, nonclosed points and
   nonreduced finite fibres. Identity arrows make s surjective even without
   surjectivity of p. The docstring gives the closed-complement construction,
   residue-algebra norm criterion and affineness argument. Both new nodes match
   their Lean signatures verbatim. Fresh LeanFinder search for finite flat
   equivalence relations and invariant affine opens returned only flatness and
   finite-presentation interfaces. Loogle `Algebra.norm` returned ring norm
   definitions and identities, including the basis-dependent determinant formula,
   but no scheme-level gluing or shrinking theorem. Grep searches using groupoid,
   saturation, invariant affine and norm terminology in Mathlib and both project
   roots found no replacement. Verdict: true, needed, strictly partial statements;
   no norm proof available to close in a few minutes.
4. Read from the upper theorem downward: finite orbit, identity membership,
   saturation, affine-base localization by the proved prime-avoidance theorem,
   norm shrinking, and arbitrary-test-scheme transport via a pullback lift.
   All four added private proof imports are used. The new modules' public imports
   supply their statement vocabulary; PullbackCarrier is a private proof import.
   The removed imports and all removed old direct proof edges are listed above.
   Inspected `dag/units/sk-prop-jacobian-descent.json`: `realized` has no assigned
   nodes; no unit realization or step is bypassed or altered. The effective-descent
   route still uses this invariant-affine-neighbourhood step. Verdict: pass.
5. Checked every node's proof steps against the Lean reduction and checked that
   each `proof_deps` is exactly the union of the steps' `uses`. Inspected source,
   origin, creation, blueprint, unit/chapter and search fields of both new nodes.
   The remaining norm hole has its own complete node; the orbit node records
   composition, inversion and Mathlib point lifting. Verdict: pass.

Second reading changed only trailing whitespace in the upper proof and this report:
made the one-closed/one-added hole accounting and the removed direct DAG edges explicit,
and recorded the independent review and axiom checks. No mathematical repair was needed.


## Second reading by D3

Independent reading of the repaired four-module delivery, 2026-10-12.

1. Compared the item against the read-only repository with diff and checked its
   theorem signature programmatically: byte-for-byte identical. Its docstring and
   public imports are unchanged. The other three modules are new, not adaptations
   of existing declarations. The existing node changes only proof, proof_deps and
   proof_origin. No definition or statement change requires a change record. Pass.
2. Read the upper proof, orbit composition and inversion, point lifting, and the
   extracted naturality proof. Compiled all four modules in import order through
   lcompile.py, cleanly. A scratch copy printed axioms of all four public theorems:
   orbit saturation and naturality use only propext, Classical.choice, Quot.sound;
   the upper theorem and norm theorem additionally use sorryAx. The sole sorry is
   exactly the named norm theorem. No forbidden declaration or holed definition
   occurs; no data is defined by choosing an arbitrary unproved witness. Pass as
   a decomposition: one original hole closed and one hole added, net zero.
3. Read Stacks 03JE and 0H8K independently. The remaining norm lemma generalizes
   the shrinking portion of 03JE from one orbit to a finite saturated set; its
   docstring supplies the closed-complement, norm criterion, invariance and affine
   basic-open argument. Checked empty S (empty affine open), identity p (U=A),
   nonsurjective p (identity arrows still give surjective source), varying rank,
   nonclosed points and nonreduced fibres. It is true and strictly partial: orbit
   construction, base localization and arbitrary-test-scheme invariance remain
   in the upper proof. Fresh LeanFinder search using equivalence relation and
   determinant terminology returned only flatness/finite morphism interfaces;
   Loogle Algebra.norm returned algebraic determinants, not scheme shrinking.
   Remote grep with saturated/invariant/Norm was too broad to establish absence;
   targeted local rg in both library roots and Mathlib algebraic geometry found
   no replacement. In particular inspected BaseChangeNorm.normAt and
   mem_basicOpen_normAt, and ProjectiveSpace.CoordinateCoverDescent: the proved
   criterion and restriction compatibility there require a pullback of a finite
   field extension, not an arbitrary finite locally free morphism. Thus these
   are useful future ingredients but do not close this hole in a few minutes.
   The shared naturality lemma is a proved underlying-map wrapper of the existing
   transport_homMk_comp field, with changed-map equalities needed by both users;
   it introduces no second definition of transport. Pass.
4. Read downward from the unchanged target: finite orbit and identity membership,
   proved saturation, affine-base localization using existing prime avoidance,
   norm shrinking, then pullback lifting and naturality on every test scheme.
   All added private proof imports are used; public imports supply statement
   vocabulary. No simpler general scheme norm theorem was found. The report's
   No longer needed section accounts for both removed imports and both removed
   old direct proof dependencies. Inspected the unit's realized fields (empty)
   and effective-descent usage: the existing invariant-neighbourhood step and
   original 03JE route are retained. Pass.
5. Checked the four nodes against the Lean proofs and remaining hole. Each
   proof_deps equals the union of the proof steps' uses, and all three new Lean
   statement records match their signatures verbatim. Source, creation, search,
   blueprint, chapter and unit records are present. The new naturality edge is
   recorded in both users, avoiding a cycle or duplicated private proof. Pass.

Second reading changed only this report: recorded the independent review of the
shared-helper repair, fresh axiom and compilation checks, and the precise limitation
of the upstream finite-field norm interfaces. No mathematical repair was needed.
