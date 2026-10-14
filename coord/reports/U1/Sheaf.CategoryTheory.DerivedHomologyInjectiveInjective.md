## What changed

Proved CategoryTheory.derived_homology_injective_injective in
Sheaf.CategoryTheory.DerivedHomologyInjectiveInjective without changing its signature,
visibility, or existing docstring. Added a proved private helper
CategoryTheory.injective_single_from_upper_eq_zero.

Added proof-only imports Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
and WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure. Both are used:
the first supplies vanishing into an injective single object from a strictly positive
complex; the second supplies the homology comparison for maps from <=0 to >=0 objects.
Updated the existing node's proof and proof_origin to the actual truncation argument.
The unit sk-prop-sf-cbc has empty realized statement/steps lists; this generic tool
argument changes no unit route.

## Proved and sorry left

Closed the sole original hole, CategoryTheory.derived_homology_injective_injective
(node new-stage3-derived-homology-injective-injective). Added zero holes.
No sorry remains in the delivered module. The private helper is also fully proved.
This is a proof, not a decomposition. Single-file compilation passes without warnings;
the delivery dry run also checks the axioms of every delivered declaration.

## No longer needed

No existing import, node, or module is removed: the original proof_deps was empty.
The explicit chain-map/cycle-factorization/null-homotopy construction in the old plan
is unnecessary in this module. Its role is supplied by Mathlib's proved vanishing
lemma and exactness of the canonical truncation triangle. No new K-injective,
chain-map factorization, or localization comparison items are needed.
Both new proof imports are used. Existing public statement imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The node offered a long chain-level plan with no proof dependencies, but existing
proved generic library results give a complete truncation proof. No statement or
interface correction was required. The original informal sentence about factoring
through the preceding differential is not used: for a cochain null homotopy into
I[0], the relevant factorization of the degree-zero component would involve the
outgoing differential d^0. The delivered proof avoids that chain-level issue.

Zero source, zero injective target, unbounded source, and arbitrary permitted
universes are all covered by the unchanged categorical hypotheses. No enough-injectives
assumption is introduced. No new nodes or forced adaptations were needed.

## Second reading by U1

1. I compared the delivered module with the repository version. The theorem signature,
visibility, statement docstring, and public imports are unchanged; only proof-only imports,
the private helper, and the proof body differ. No unrelated files are delivered.

2. I compiled the module with `lcompile.py`; it succeeds without errors or warnings. A
scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
`CategoryTheory.derived_homology_injective_injective`. There are no `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by` declarations.

3. The target statement is unchanged and the private helper is fully proved. The
truncation argument establishes injectivity by first proving maps from a strictly positive
object to the injective single object vanish, then applying triangle exactness and the
existing homology comparison. The helper is not a duplicate library declaration; the
existing comparison lemma is imported and used directly.

4. The proof follows a shorter valid route through the canonical truncation triangle and
the existing Mathlib vanishing lemma. Both added imports are proof-only and used. The
original node had no proof dependencies, so none are removed. The unit route is unchanged;
its `realized` lists are empty.

5. The node proof steps and proof origin now describe the truncation proof actually present
in Lean, with no new split-off statements. The node's target statement and unit/chapter
metadata remain unchanged.

I changed only the proof-only imports, private helper/proof, node proof metadata, and this
second-reading report section; no statement or definition was changed.
