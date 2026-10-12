## What changed

Filled the proof of `AlgebraicGeometry.unramified_fibre_point_isolated` in
`lean/Sheaf/AlgebraicGeometry/UnramifiedFibrePointIsolated.lean`, without changing its
signature or imports. The proof follows all four steps of the existing DAG plan.
It chooses the unramified open neighbourhood, applies
`unramified_baseChange_restrict_open` to its residue-field fibre, and applies
`discreteTopology_of_unramified_over_field`. The canonical `pullback.map` is an
open immersion by Mathlib's `Scheme.pullback_map_isOpenImmersion` instance. Its
range contains `f.asFiber x` by `Scheme.Pullback.range_map`. The image of an open
singleton is open; injectivity of `fiberι` proves uniqueness; `fiberHomeo` transfers
the open singleton to the set-theoretic fibre. A declaration-local transparency
option makes the definitional identification of the fibre with the pullback
available during rewriting. No new declaration, node, or interface change.

Local compilation completed without errors or warnings. The proof works for any
chosen open neighbourhood containing x, including the whole scheme; it uses no
nonemptiness assumption beyond the given point.

## Proved and sorry left

Proved `AlgebraicGeometry.unramified_fibre_point_isolated`: 1 of 1 original sorries
removed. No sorry remains in the delivered module, and no new sorry is added.
The proof intentionally uses the existing named statements
`AlgebraicGeometry.unramified_baseChange_restrict_open`
(`lem-weil-pbc-unramified-base-change-open`) and
`AlgebraicGeometry.discreteTopology_of_unramified_over_field`
(`lem-weil-pbc-unramified-over-field-discrete`), whose proofs remain separate items.

## No longer needed

None. Both existing proof imports are used, and all existing proof dependencies
remain needed. The open-fibre-product Mathlib leaf is realized directly by
`Scheme.pullback_map_isOpenImmersion` and `Scheme.Pullback.range_map`; it has no
separate Sheaf module to import. No module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing statement and four-step plan fit. Searches found Mathlib's
`quasiFiniteAt_iff_isOpen_singleton_asFiber`, but the existing project's unramified
quasi-finiteness lemma concludes its own affine-neighbourhood predicate rather
than Mathlib's `QuasiFiniteAt`; the delivered proof therefore keeps the original
fibre route. No change to the DAG is needed because the final proof follows it.

## Second reading by C2

1. **Visible declarations unchanged: PASS.** Compared the only delivered module
   against the repository using `diff -u`. The existing theorem signature and
   docstring are byte-for-byte unchanged; the only edits are the proof and its
   declaration-local definitional-transparency option. No definition, public
   import, declaration, or target statement is changed. No change record is needed.
2. **Proof and axioms: PASS.** Compiled the module using `lcompile.py`, without
   errors or warnings (2.7 seconds). It contains no sorry and no forbidden axiom,
   unsafe declaration, opaque declaration, implementation override, or external
   code. Compiled a scratch copy with `#print axioms` for the theorem: exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected
   from the two existing open dependency theorems named above; this delivery
   closes the item's own proof, not those dependencies. The local transparency
   option affects elaboration, not kernel checking.
3. **Split statements: PASS (none).** No new theorem, module, or node is added.
   Independently read both imported dependency statements. Base change applies
   to the chosen restriction, and the discreteness theorem applies over the
   residue field. The range argument uses the point hypothesis precisely; empty
   schemes introduce no counterexample since there is no x, and U equal to the
   whole scheme is allowed. No extra finiteness or nonemptiness assumption enters.
4. **Shortest route, imports, pruning, and unit: PASS.** Independently searched
   Mathlib for unramified morphisms and open fibre singletons, and searched the
   project and upstream Lean for the isolation conclusion. Mathlib's
   `quasiFiniteAt_iff_isOpen_singleton_asFiber` requires its stalk-based
   `QuasiFiniteAt`; the project's unramified quasi-finiteness theorem instead
   supplies `IsLocallyQuasiFinite`, so it gives no direct shorter application.
   Inspected the pullback open-immersion instance and range theorem. Both private
   proof imports are used, and the three public imports provide notions in the
   existing signature. All six old proof dependencies remain represented in the
   argument, so `## No longer needed` is complete. Checked
   `dag/units/sk-thm-p1.json` and its `realized` entries: the proof changes no unit
   realization or route.
5. **Nodes agree with Lean: PASS.** Read
   `lem-weil-pbc-unramified-fibre-point-isolated` and the open-fibre-product
   Mathlib leaf. The existing four proof steps, `proof_deps`, and document-based
   `proof_origin` describe the delivered proof: unramified base change,
   discreteness over the residue field, open pullback map and its range, then
   singleton image, injectivity, and fibre homeomorphism. No DAG edits are needed.

Second reading changed only this report by adding the independent review and
explicit axiom-check result. The Lean proof was correct and is unchanged.
