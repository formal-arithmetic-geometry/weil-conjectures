## What changed

Proved `AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_compatibility_aux`
without changing its signature or the public imports. Added a proof-only
`import all Sheaf.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare` to reuse its
proved private generic composition-factorization and cancellation lemmas. These helpers
have no affine-scheme hypotheses. The affine-spectrum theorem itself is not applied.

Added proved private helpers for the counit normalization of one arbitrary open immersion,
the composition square, the degreewise inverse tensor-square formula, and categorical glue.
The final proof combines these with counit naturality. It inverts comparison isomorphisms
only and works for arbitrary complexes, including zero complexes and empty opens.
Local transparency attributes keep the selected tensor and derived constructions abstract.
A private abbreviation and local instance reuse the supplied derived-category instances under
Mathlib's definitionally equal `Scheme.Modules` spelling; no new localization is selected.
Single-file compilation completed without warnings in 57.5 seconds (the 60-second limit
is unchanged).
Updated the item's node proof and proof dependencies to describe this calculation.
The preflight-required record for the local proof commands is
`coord/changes/openRestrictedCounitProofTransparency.md`; no consumer adaptation is needed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_compatibility_aux`
(node `new-open-restricted-counit-compatibility-aux`).
No holes added; no `sorry` remains in any delivered Lean file.
The private helpers are proved, not new deferred obligations. Existing dependencies may
still contain their own holes; this delivery proves the requested equation from their
recorded constructions and universal properties.

## No longer needed

None. Both original public imports are required by the unchanged statement and construction.
No original proof dependency is bypassed. No K-flat resolution or K-flatness lemma is needed
in this auxiliary calculation: the existing composition comparison's factorization is used
for an arbitrary complex.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped before implementing the generic left-derived factorization.
The bridge is provided by Mathlib's `Functor.leftDerivedNatTrans_app` and
`Functor.mapDerivedCategoryNatIso_fac`; the composition calculation already has proved
private generic helpers in `AffineSpectrumCompositionCounitSquare`.
The original one-step node proof omitted these explicit normalization and naturality steps;
they are now recorded and implemented. The statement is unchanged and no new node is needed.
Preflight conservatively treats added local attribute commands as an interface change;
the accompanying change record documents their scope and the unchanged public API.

## Second reading by T3

1. **Unchanged interface — pass.** Compared the only delivered Lean module with
   the repository using `diff`, then checked the existing theorem signature
   byte for byte through `:= by`. Its signature and both public imports are
   identical. All six added helpers are private; the abbreviation returns the
   supplied derived-category instance, rather than choosing a localization.
   Reducibility and instance attributes are local. The transparency change record
   accurately explains the conservative interface classification.
2. **Proof and axioms — pass.**
   Read every helper and the final proof. The open restriction normalization uses
   the inverse of the same `leftDerivedUnique` used by the existing construction.
   The two composition factorizations use the pinned composition comparisons and
   the pullback equality in the correct direction. The tensor-square inverse is
   checked degreewise. The final glue cancels a representative isomorphism, never
   a counit. No `sorry`, axiom, unsafe declaration, opaque declaration, external
   implementation, or hollow definition occurs in the delivered source.
   The imported generic helpers were read in
   `AffineSpectrumCompositionCounitSquare`: they are proved and have no affine
   hypotheses. Their selected comparison is the already pinned comparison whose
   hom is determined by the left-derived universal property; no arbitrary witness
   is introduced by this delivery.
3. **Split statements and edge cases — pass.** There are no split-off statements
   or new deferred obligations. Checked zero complexes, top and empty opens,
   and identity pullback: the argument requires no nonzero object, nonempty open,
   flatness of the complex, or invertibility of its arbitrary pullback counit.
   All cancellations concern supplied isomorphisms.
4. **Shortest route, imports and unit — pass.** Independently searched with
   `msearch.py ... loogle '"leftDerivedUnique"'` and `rg` for counit compatibility,
   restriction normalization and composition factorization. The matching generic
   Mathlib factorization is already used. The similarly shaped public
   `openRestricted_counit_compatibility` depends on this item through
   `OpenRestrictedCounitFactorization`, so cannot replace this proof. Both public
   imports occur in the unchanged signature; the additional `import all` is
   proof-only and supplies the reused private generic helpers. Every original
   proof dependency remains used: the old-minus-new dependency set is empty,
   agreeing with `## No longer needed`. Read
   `dag/units/sk-thm-picard-semicon.json`: this auxiliary calculation is below the
   unit route and changes none of its existing `realized` entries.
5. **DAG agreement — pass.** Compared the node JSON records: only `proof`,
   `proof_deps`, and `proof_origin` changed. The three proof steps match the
   composition square, restriction normalization, and naturality/tensor-square
   cancellation in Lean. The affine-spectrum dependency records reuse of its
   generic private helpers, not application of its affine theorem. No new nodes
   or statement changes are needed.

Second reading changed only this report, adding the independent review and
validation evidence; the proof, imports, node and change record needed no repair.

Validation: the delivered module compiled without warnings in 56.5 seconds.
`deliver3.py T3 Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux --no-push`
printed OK for commit `eb22fd9a1c`: compilation, the all-declaration axiom probe,
and preflight passed. Its CODEX classification comes from the existing node edit
and the conservative classification of local proof commands documented in the
change record. Scratch copies requesting explicit `#print axioms` exceeded the
60-second limit locally; they are not delivered source changes.
