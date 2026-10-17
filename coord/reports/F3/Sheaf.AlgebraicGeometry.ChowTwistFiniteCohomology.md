## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_chow_twist_finite_cohomology` in
`lean/Sheaf/AlgebraicGeometry/ChowTwistFiniteCohomology.lean`, preserving its signature
and all public imports. Put `p := π ≫ i`, choose a graph-twist vanishing threshold,
and lift the given projective embedding to projective space over `X`. Independent
projective pushforward finite type, quasi-coherent pushforward, and the locally
Noetherian coherence criterion give coherence of the nested pushforward.
Projective affine cohomology finiteness and the base-linear Leray equivalence give
finite cohomology with the required restricted scalar action.

Added proof-only imports for Noetherian transfer, Grothendieck enough injectives,
sheaf-module Grothendieck abelianness and finite local freeness, and invertible tensor
powers. The projective twist import is retained to supply invertibility. Removed
four unused proof imports, listed below. Updated only `proof`, `proof_deps`, and
`proof_origin` of the existing node; no signature or definition change record is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_chow_twist_finite_cohomology`
(node `lem-pc-q2-chow-twist-finite-cohomology`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the delivered
module. This is a proof from existing dependencies, not a new decomposition.
Existing imported statements remain open, including
`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_graph_twist`.
The scratch-copy `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`; the last comes from existing imported holes. No claim
is made that the theorem's transitive dependencies are now sorry-free.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`

Removed the sole unused old proof dependency
`lem-weil-pbc-quasi-coherent-finite-type-affine`. Finite type is supplied directly
by `lem-pc-m1-projective-pushforward-finite-type-independent`. The source
quasi-coherent pushforward and coherence criterion are retained. These are import
and dependency removals; whole-library reachability pruning is left to the maintainer.

The second reading also removed the first worker's newly added
`WeilConjectures.AlgebraicGeometry.Modules.Ext` and
`WeilConjectures.AlgebraicGeometry.Seesaw` imports, replacing their support facts
with direct lower-level imports. The original
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` import was restored.

## Where the brief, the DAG or earlier work was wrong

The planned affine finite-type dependency was unnecessary. Pushforward along
`π ≫ i` is definitionally the nested pushforward, so no separate pushforward
composition isomorphism or cohomology transport is used. The original DAG's last
step described two linear equivalences; the actual proof uses one, with its scalar
action rewritten using `hjp`.

The first worker's report omitted removal of the Sheaf coherence-criterion import
and described the projective twist import as redundant. Removing its broad Seesaw
import exposed the need for the twist's invertibility instance, so the explicit
twist import is retained. Its theorem proof also contained an unused `hq'` fact
and an unnecessary `haveI`/`letI` linter suppression.

## Second reading by F3

1. **Interface: pass.** Compared the sole delivered Lean module with the shared
   repository using `diff`. The existing theorem signature is byte-for-byte
   identical, including all four schemes, properness of `f` and `π`, closedness of
   `i` and `j`, arbitrary finite coordinate type, the compatibility equality,
   the specified pulled-back twist, coherence, and every degree with scalars
   restricted along `f.appTop`. All public imports and existing docstrings are
   unchanged. There are no added declarations or definitions, or forced adaptations.

2. **Proof: pass with existing open dependencies.** Both the final module and a
   scratch copy with `#print axioms` compiled through `lcompile.py` without errors
   or warnings. The axiom list is recorded above. Read every application: properness
   makes `X` Noetherian and the graph lift closed; invertible tensor powers are
   quasi-coherent and finitely presented; the projective pushforward and source
   coherence criterion give the exact required coherence predicate. `change` checks
   definitional composition. Leray uses precisely the chosen threshold's positive
   vanishing, and rewriting by `hjp` aligns the base-ring actions before transporting
   finiteness through `e.symm`. No forbidden declarations or data definitions occur.

3. **Split statements: pass, none added.** No new node or holed theorem was split
   off, so no relabelled target or unproved data construction is introduced.
   Checked the existing dependency statements for all hypotheses, including the
   finite coordinate type without a nonemptiness assumption. Empty coordinates
   force `Y` empty; degree zero, tensor exponent zero, and the empty-base case
   require no extra hypothesis and are covered by the cited declarations.

4. **Route and pruning: pass after repair.** Read Stacks Tag 02O5, especially its
   graph embedding, relative ampleness, Leray, and projective-finiteness paragraphs:
   <https://stacks.math.columbia.edu/tag/02O5>. The proof uses this analytic part
   without invoking general proper coherence. Searched `lean/Sheaf` and upstream
   `lean/WeilConjectures/AlgebraicGeometry` by Chow twist, projective finite
   cohomology, and proper cohomology names. Existing field-valued proper-finiteness
   results do not replace this argument over an arbitrary affine Noetherian base.
   Read `dag/units/sk-thm-picard-coherence.json`: its `realized` statement and step
   arrays are empty, and this delivery changes neither its statement nor route.
   All six retained old proof dependencies are used; the seventh is listed above.
   Removed broad Ext/Seesaw proof imports in favor of direct support results,
   restored the twist import, and removed unused `hq'` and the linter suppression.

5. **DAG agreement: pass after repair.** Opened the existing node and the six
   dependencies' recorded declarations. Its `proof_deps` equals the union of
   the steps' `uses`, and matches graph vanishing, independent projective finite
   type, source quasi-coherent pushforward, source locally Noetherian coherence,
   independent projective affine finiteness, and base-linear Leray used in Lean.
   Corrected the final step to the single equivalence and definitional composition;
   updated `proof_origin` accordingly. JSON comparison confirms that only
   `proof`, `proof_deps`, and `proof_origin` changed. There are no new nodes.
