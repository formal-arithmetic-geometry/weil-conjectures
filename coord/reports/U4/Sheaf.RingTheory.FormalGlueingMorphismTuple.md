## What changed

Proved `FormalGlueing.canonical_tuple_compatible` in
`Sheaf.RingTheory.FormalGlueingMorphismTuple`, without changing its signature.
Added the proof-only import `Sheaf.Paper.FormalGlueingCanonicalMaps` for the already
proved comparison formulas and injectivity. Both existing public imports remain
necessary for the statement: formal glueing data and the divisor-unit theorem
that types the canonical maps into product localizations.

Five proved private helpers handle restriction of canonical chart scalars,
transport of prime compatibility, transport of chart compatibility, comparison
of the localized tensor-unit map, and passage from swap compatibility to equality
in the product localization. The last helper replaces denominator clearing by
uniqueness of two successive localization lifts. The main proof evaluates the
transported morphism equations on denominator-one elements and combines the resulting
zero differences using product and function extensionality.

Updated the existing node's proof and proof origin to match the Lean argument.
Added the cover-module node to its overlap proof dependencies because the proof
uses that module's proved divisor-unit theorem, not its cover exactness conclusion.
The fixed blueprint unit route is unchanged: this node realizes no unit statement
or unit proof step, and the canonical comparison and swap route remains in use.

Validation: the entire module compiles through `lcompile.py` without warnings.
No nonzero denominator, flatness, covering, or quotient-isomorphism assumption
was introduced. Empty chart families are handled by function extensionality;
zero denominators and zero modules are handled by localization universal properties.
No arbitrary witness or new definition was introduced.

## Proved and sorry left

Closed the only original hole:
`FormalGlueing.canonical_tuple_compatible`
(node `lem-weil-pbc-formal-glueing-morphism-tuple`).
All five private helpers are proved. No `sorry` remains in the item, and no new
hole or module was added. This is a proof, not a decomposition.

## No longer needed

No imports or dependency nodes are pruned. The original denominator-clearing
argument (fraction representatives, two annihilating powers, and the common
product-localization numerator) is unnecessary: successive universal-property
uniqueness proves the overlap comparison directly. No separate modules or nodes
were assigned to these arithmetic steps, so no module becomes prunable from this
change. `RingTheory.coverModuleExact` itself is not invoked, but its module remains
necessary for `RingTheory.localizationAway_map_units_of_dvd` in the signature
and in the overlap proof.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and its supplied hypotheses are correct. The original
DAG chose a longer overlap calculation than needed and omitted the cover-module
node as a proof dependency of the divisor-unit theorem. Both points are reflected
in the updated proof fields. The canonical-map node is implemented in
`Sheaf.Paper.FormalGlueingCanonicalMaps`, rather than in the RingTheory directory.
There were no tool failures or forced adaptations.

## Second reading by U4

1. **Interface and statements.** Compared the delivered module with the repository version. The
   public theorem signature is byte-for-byte unchanged; only its proof and a proof-only import
   were added. Verdict: pass.
2. **Proof correctness.** Compiled the module with `lcompile.py`; it has no errors or warnings,
   no `sorry`, forbidden declarations, or hollow definitions. The proof uses only the stated
   canonical comparison, swap, and localization universal-property results. Verdict: pass.
3. **Split statements and dependencies.** No split-off theorem or new node was added. The
   existing node's proof and proof dependencies match the declarations actually used, including
   the divisor-unit theorem's cover-module dependency. Verdict: pass.
4. **Pruning and imports.** The added `Sheaf.Paper.FormalGlueingCanonicalMaps` import is needed
   by the proof and is private to this module; both public imports remain required by the
   statement or proof. No old dependency can be removed without changing the route. Verdict:
   pass.
5. **Unit route and mathematical scope.** The canonical comparison and swap route remains the
   planned route, with the overlap calculation shortened via localization uniqueness. No
   hypothesis, conclusion, or definition was changed, and edge cases such as empty families and
   zero denominators remain covered. Verdict: pass.

I changed only the report by adding this second-reading record; no Lean source or DAG statement
was changed during review.
