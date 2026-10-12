## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.fibre_cartier_local` in
`lean/Sheaf/AlgebraicGeometry/FibreCartierLocal.lean`, preserving its full signature and
visibility. The proof follows both steps of `lem-pc-recd-fibre-cartier-local` directly,
using the existing algebraic theorem
`Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber`.

Choose a principal affine chart inside both supplied neighbourhoods and over an affine
base chart. The tensor-product chart of the fibre factors through its Cartier
neighbourhood; open pullback preserves invertibility, giving the algebraic criterion's
hypothesis at every prime of the tensor product. Its basic-open conclusion gives a
regular principal ideal and flat quotient. Transport the former through `topIso` and
the latter through `resLE` and the canonical pullback/restriction isomorphism to obtain
the relative effective Cartier property. No global condition on other fibres is used.

Removed the unused proof import `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`.
No new imports, declarations, nodes, definitions, interface changes or adaptations.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.IdealSheafData.fibre_cartier_local`
(node `lem-pc-recd-fibre-cartier-local`). No holes remain in the item, and no holes were
added. This is a proof, not a decomposition. The local compiler checks the complete proof;
the delivery dry run additionally checks the axioms.

## No longer needed

Removed import/module `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`: the affine
argument uses no Riemann--Roch or curve results. This removes that import edge; whether the
module is still reached elsewhere is for the global closure computation.

No planned proof-dependency node is pruned: `def-weil-scheme-morphism-properties`,
`def-sc-effective-cartier-divisor`, `def-pc-relative-effective-cartier` and
`lem-pc-algebra-fibre-cartier-local` are all used. Their existing declarations are already
available through the retained public import. The original two-step DAG route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The original Riemann--Roch proof import was
unnecessary. The hypothesis `hx : x ∈ J.support` is unnecessary for the argument, but its
binder is preserved exactly as required; the proof retains it in a local proof binding. No statement,
definition or unit route was changed.


## Second reading by S3

1. **Interfaces: pass.** Read the full repository and sandbox modules and their diff.
   The only declaration, `AlgebraicGeometry.Scheme.IdealSheafData.fibre_cartier_local`,
   has a byte-identical signature, visibility and docstring. The universe, flatness and
   local finite presentation instances, support hypothesis, the two neighbourhood
   hypotheses, and the full relative-Cartier conclusion are preserved. The only
   non-proof edit removes the private Riemann--Roch import. No definitions, public
   imports, other modules or change records are altered. Checked the existing change
   records naming this module; none requires a further adaptation here.

2. **Proof and axioms: pass.** Compiled the delivered module with
   `python3 /home/ubuntu/weil-launcher/lcompile.py --all
   /home/ubuntu/weil-sandbox/S3/Sheaf.AlgebraicGeometry.FibreCartierLocal`:
   exit 0, no warnings. An independent scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.IdealSheafData.fibre_cartier_local` also compiled and
   reported exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
   Scanned the source for forbidden declarations and proof escapes: none. No
   `sorry` remains and every source line is at most 100 characters. All choices
   in this proof are existential eliminations inside a theorem, not data definitions.

3. **Split statements: pass (none).** There are no split-off statements, new nodes or
   added holes. Checked the actual algebraic criterion in
   `WeilConjectures/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`:
   it assumes the ideal is principal and concludes both regular principality and
   flatness of the quotient; it does not require that quotient to be flat already.
   Its field, prime contraction, flatness and finite presentation hypotheses are
   supplied by the residue-field sections, `ker_appLE_fromSpecResidueField`, and
   the affine-chart properties of `π`. The fibre hypothesis is obtained at every
   tensor-product prime by an open immersion into the supplied fibre neighbourhood.
   Thus no condition on any other fibre, or outside that neighbourhood, is used.

4. **Route and pruning: pass.** Read [Stacks Tag 062Y(3)]
   (https://stacks.math.columbia.edu/tag/062Y), the item's two proof steps, the
   algebraic dependency, the upstream global `IsLocallyPrincipal.isInvertible_and_flat`,
   and `dag/units/sk-prop-av-cube.json`. Independently searched with LeanFinder for
   “locally principal ideal invertible fibre flat morphism open neighbourhood effective
   Cartier divisor” and with `rg` for `IsRelativeEffectiveCartier`,
   `isInvertible_and_flat`, and Cartier results in Mathlib's algebraic geometry.
   No applicable shorter theorem was found: the upstream global theorem requires
   invertibility on every whole fibre, which the local hypothesis does not supply.
   The proof uses the existing algebraic criterion directly. Checked both transports
   at the end: `topIso` identifies the restricted ideal with its affine sections;
   `resLE` gives flatness over the affine base, and `comapIso` with the pullback
   restriction isomorphism identifies the closed subscheme being restricted.
   Flatness then composes with the open base inclusion. There is one retained import,
   necessary for the public statement, and the removed Riemann--Roch import is fully
   listed above. All four old proof dependencies are still used. No unit step is
   bypassed. The unit's already-empty `realized` arrays are unchanged; this proof
   does not claim to repair that pre-existing unit bookkeeping.

5. **DAG agreement: pass.** The existing node
   `lem-pc-recd-fibre-cartier-local` already records exactly this affine reduction
   and application of `lem-pc-algebra-fibre-cartier-local`. Its `proof_deps` are the
   morphism properties, effective Cartier and relative effective Cartier definitions,
   and the algebraic criterion, all used in the proof. Its document `proof_origin`
   remains accurate. No node update or new node is necessary.

Second reading changed only this report, adding the independent checks and verdicts.
No mathematical or Lean repair was needed. Holes closed: the sole original
`AlgebraicGeometry.Scheme.IdealSheafData.fibre_cartier_local`; holes added: none.
