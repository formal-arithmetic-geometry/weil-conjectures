## What changed

Replaced the target proof with a componentwise proof using the existing
`AlgebraicGeometry.Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder`
theorem from `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived`. For
`N = addOrderOf (1 : Λ)`, the nonzero case uses `N • 1 = 0`, `of_natCast_eq_zero`,
and the hypothesis that `N` is a unit on `Y`. If `N = 0`, the same hypothesis
makes `0` a unit in `Γ(Y, ⊤)`, so `Y` and then `X` are empty; the torsion condition
is vacuous. `NatIso.isIso_of_isIso_app` combines the component isomorphisms.
The proof-only imports were reduced to the source smooth-derived theorem and the
base-change morphism definitions. The import change is recorded in
`coord/changes/etale-smooth-ring-imports.md`.

## Proved and sorry left

The target declaration `AlgebraicGeometry.Etale.isIso_baseChange_of_smooth_of_ring_order_invertible`
is proved. Closed holes: 1, namely that declaration. Added holes: 0.
No statements were split off, no `sorry` remains in the delivered module, and no
other module is delivered. A scratch-copy `#print axioms` check of the target and
of the source component theorem lists exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`

The following planned proof nodes are no longer direct dependencies of this target:
`lem-weil-pbc-etale-constant-ring-module-equivalence`,
`def-weil-pbc-derived-categories`, `def-weil-pbc-direct-image`,
`def-weil-pbc-inverse-image`, `def-weil-pbc-derived-exchange`,
`def-weil-pbc-derived-inverse-image`, `lem-weil-pbc-exchange-forget-coefficients`,
`def-weil-pbc-geometric-stalks`, `def-pc-scheme`,
`sbc-def-derived-categories-with-allowable-torsion`,
`sbc-thm-bounded-below-derived-smooth-base-change`, and
`sbc-def-base-change-map`.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expanded coefficient equivalence, derived exchange, and
allowable-torsion transport. The existing source theorem already packages the
needed bounded-below module smooth-base-change argument, so those steps are
redundant for this target. The target statement is unchanged.

## Second reading by A2

1. Compared every delivered Lean declaration with the repository version.
   There is one theorem, and its signature from `theorem` to `:=` is byte for
   byte identical. There are no added hypotheses, weakened conclusions, changed
   definitions, new declarations, or adaptations. The public-import change is
   declared with exact old/new import blocks and downstream users in
   `coord/changes/etale-smooth-ring-imports.md`. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`, and compiled a scratch copy
   with `#print axioms` for the target and the upstream component theorem.
   Both use only `propext`, `Classical.choice`, and `Quot.sound`.
   Inspected the proof term's source route and the torsion definition: there is
   no `sorry`, new axiom, unsafe escape, opaque declaration, hollow definition,
   or choice of arbitrary data from an unproved existence theorem. Verdict: pass.
3. No statements are split off and no new nodes or holes are introduced.
   Checked the arithmetic and geometric edge cases: positive additive order of
   1 annihilates every module; order 1 includes the zero coefficient ring;
   order 0 forces the global-section ring to be trivial and hence the base
   scheme to be empty. A geometric point of X would then map its closed point
   through X to the empty base, a contradiction. The empty scheme case is
   therefore valid without imposing a nontriviality hypothesis. Verdict: pass.
4. Read the source component theorem, its bounded-below devissage proof,
   `of_natCast_eq_zero`, and `Scheme.isEmpty_of_subsingleton_Γ`; searched
   `lean/WeilConjectures` and `lean/Sheaf` for alternate ring-order base-change
   results. Independently queried `msearch.py` with LeanFinder for the derived
   torsion theorem, Loogle for `addOrderOf, IsUnit`, and grep for the torsion,
   subsingleton, and natural-isomorphism helpers. No shorter complete theorem
   was found. Replaced the hand-written ring-subsingleton calculation by
   Mathlib's `subsingleton_of_zero_eq_one`, removed the unused `IsEmpty X`
   instance, and used modern local instance declarations so the global linter
   suppression could be removed. Checked every old proof dependency against
   the report's no-longer-needed list (all 12 removed dependencies are listed),
   including the direct `BaseChange.Derived` import omitted by the first reader.
   The retained source theorem reduces to the existing smooth-base-change
   theorem. `dag/units/sk-rem-rest.json` has empty `realized.statement` and
   `realized.steps`; its classical smooth/derived route is kept and no unit
   statement or required step is bypassed. Only direct dependency pruning is
   claimed here; global closure pruning is the maintainer's ledger result.
   Verdict: pass.
5. Compared the node statement and Lean record with the unchanged signature;
   checked `proof`, `proof_deps`, and `proof_origin` against the actual proof.
   The recorded source theorem and ring-order case split are correct. Clarified
   that the packaged derived theorem reduces to the retained
   `sbc-thm-smooth-base-change` dependency through devissage and truncation.
   Restored the existing node's historical `created` and `lean` metadata, so
   only the three proof fields change. There are no new-node records to check.
   Verdict: pass.

Second-reading changes: simplified the zero-order proof using a Mathlib lemma,
removed an unused local instance and an unnecessary linter option, restored
historical node metadata, clarified the DAG dependency provenance, completed
the removed-import list and hole counts, and replaced the incomplete import
change record with exact imports and its downstream-user table.
