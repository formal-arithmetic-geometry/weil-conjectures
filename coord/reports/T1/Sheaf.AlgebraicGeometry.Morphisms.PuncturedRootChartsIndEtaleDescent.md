## What changed

Proved `AlgebraicGeometry.Scheme.punctured_root_charts_descend_indEtale` with its
signature and public imports unchanged. Added two proof-only imports and two
fully proved supporting modules:
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootProductBaseChange` and
`Sheaf.AlgebraicGeometry.Morphisms.AffineFpIsoIndEtaleDescent`.

The first constructs the root-product tensor equivalence and pastes its Spec
pullback square with the restriction square. Mathlib's finite-product and
AdjoinRoot finite-presentation instances supply local finite presentation.
The second uses `RingHom.IndEtale.iff_exists` for the filtered etale presentation.
Its proved private helper `finite_units_stage` factors the localization at the
product of the finitely many prescribed elements through a stage, so all the
unit conditions hold together. Applying Spec gives a cofiltered affine limit;
`AlgebraicGeometry.exists_iso_of_isPullback` supplies eventual isomorphism.
Canonical pullback maps and naturality carry the isomorphism and units to that
later stage. The main theorem takes the image of x under Spec(psi) as z, proves
its image equation by functoriality, and composes the chart isomorphisms.

Sources read: Stacks Tags 0EYG (the displayed-isomorphism descent paragraph)
and 05N9 (parts (2), (3)), Mathlib's ring finite-presentation factorization and
root/tensor/pullback APIs, and the proved affine-transition-limit source library.
The unit record `sk-prop-input-spreading` has empty realized lists and no fixed
unit step is bypassed. The closed spreading-out result is used as a tool; its
unit's route is not substituted for this unit's statement.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.punctured_root_charts_descend_indEtale`
(node `lem-sbc-punctured-root-charts-ind-etale-descent`).

Also proved, without adding any holes:
`AlgebraicGeometry.Scheme.punctured_root_product_base_change`
(node `lem-sbc-punctured-root-product-base-change`), and
`AlgebraicGeometry.Scheme.affine_fp_iso_descend_indEtale`
(node `lem-sbc-affine-fp-iso-ind-etale-descent`).
`finite_units_stage` is a private proved helper. All three chart abbreviations
are explicit constructions. No sorry remains in any delivered module and no
new sorry was introduced. This is a proof, not a decomposition.

## No longer needed

None. The original node has no proof dependencies to prune, and the original
module has only public statement imports, retained to preserve its interface.
No punctured-root strict-henselization presentation or single-root continuity
module is imported: those existing statements specialize to a strict
henselization or one root and do not provide this arbitrary-ind-etale,
finite-product descent. No modules can be claimed to leave the target closure
from this delivery alone.

## Where the brief, the DAG or earlier work was wrong

The original node's two non-elementary steps had no named proof dependencies.
The missing glue can be fully proved from existing Mathlib and source-library
results. The new nodes record that assembly and the explicit base-change
calculation; their docstrings include the complete arguments. No statement or
definition from the repository was changed, and no forced adaptation is needed.

Edge cases checked: m=0 uses the empty product ring and the empty product of
units (1); the localization factorization argument still applies. Exponent 0
is allowed in the base-change helper, although the main theorem retains its
positive exponents. g=0 yields empty punctures, handled by the same pullback
squares. No injectivity, regularity or nonzerodivisor condition is introduced.

## New nodes

`lem-sbc-punctured-root-product-base-change`: the affine/local-finite-presentation
and arbitrary-base-change calculation for the explicit punctured finite root
product; entirely proved. The three abbreviations expose the original ring,
basic open and structural map without selecting any witness.

`lem-sbc-affine-fp-iso-ind-etale-descent`: relative isomorphism and finite-unit
descent for arbitrary fixed finitely presented affine R-models; entirely proved.
Uses the existing finite-presentation factorization, Spec-limit and closed
spreading-out nodes. Blueprint searches for punctured root and isomorphism
finite presentation found no imported blueprint statement to reuse. Mathlib
searches are recorded in searches.jsonl, including LeanSearch's actual service
failure. There are no change records.


## Second reading by T1

1. Compared the item module against the repository version. The existing theorem
   signature is byte for byte unchanged after restoring its single space before
   `:=`; its original docstring and public imports are unchanged. The only other
   modules are new supporting modules; there are no changes to existing definitions,
   targets, or other modules and no change records are needed. Verdict: pass.
2. Read all three modules and compiled them in import order with lcompile.py.
   No sorry or forbidden declaration occurs anywhere in the delivered Lean files.
   The delivery tool's declaration-by-declaration axiom probe passed. The chart
   abbreviations construct actual rings, basic opens and maps; no arbitrary witness
   is chosen from an unproved existence theorem. Verdict: pass.
3. There are no split-off holes. Both supporting statements are fully proved and
   strictly separate parts of the argument. Checked empty products, zero exponents,
   g=0, zero rings, and the empty unit family. The localization at the product of
   the prescribed elements handles all unit conditions simultaneously. Searched
   the library for relative-isomorphism descent and root base change, and Mathlib
   through msearch with different terms. The existing single-root theorem does
   not supply finite-product base change; the existing exists_iso_of_isPullback
   is used directly rather than restated with sorry. Verdict: pass.
4. Read the top proof first, then its two helpers and the upstream isomorphism
   descent theorem. The reduction uses the explicit R-chart, relative isomorphism
   descent, and z=Spec(psi)(x); it retains both the coefficient and exponents.
   The original proof_deps is empty, so there are no old nodes to list as pruned.
   The unit sk-prop-input-spreading has empty realized lists; no realized unit
   step is bypassed. Narrowed the two new modules' public Limits imports to
   Pullbacks, which supplies the vocabulary their signatures need. All other
   proof-only imports remain plain imports. Verdict: pass.
5. Checked each node against the Lean signatures, source, proof steps and used
   declarations. The main node records both supporting nodes; the affine helper
   records the finite-presentation factorization, Spec limit and proved spreading
   result; the base-change helper uses proved Mathlib tensor/pullback APIs. New
   nodes contain their creation, blueprint, source, searches and Lean records.
   Verdict: pass.

Changes by the second reader: restored signature whitespace, narrowed the two
new public imports from Limits to Pullbacks, removed trailing whitespace, and
made the new affine helper's docstring describe the actual simultaneous-unit
localization argument. No proof, statement, definition or dependency route was
changed; no holes were added.
