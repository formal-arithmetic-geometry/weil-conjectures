## What changed

Proved both declarations of `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
with their original signatures. The general theorem composes three isomorphisms:
the derived-adjunction comparison of presheaves, the sheafification of the local
comparison with degree-zero homology, and the homology shift comparison. The sheaf
theorem specializes the general theorem to `singleFunctor 0 F`.

The private local comparison adapts the already proved module-coefficient argument in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf`
(`DerivedSections` and `higherDirectImagePresheafIso`) to free abelian sheaves.
The free-forgetful and sheafification adjunctions corepresent sections. A cohomology
section locally lifts to a cycle, giving local surjectivity. A derived morphism with
zero cohomology locally lifts through the differential from degree -1; an explicit
single-complex homotopy kills it, giving local injectivity. K-injective representatives
and naturality extend this to every bounded below derived object. This is the
cycles-and-boundaries proof of Stacks 072W/0BKV/03Q8, expressed through derived Hom.

The site comparison and the additive-adjunction comparison are generic private helpers;
this avoids repeatedly expanding the concrete etale category during elaboration.
Explicit functor-associativity rewrites in the final theorem prevent a costly
definitional conversion; the complete file compiled locally in 39.5 seconds on this resumed attempt.
Added proof imports for K-injective single-complex comparisons, bounded below derived
shift compatibility, and the local-surjectivity/epimorphism criterion. Public imports
are unchanged. Updated the node's proof, proof dependencies and proof origin to match.
No new module, node, public helper, definition change, or statement change is required.
Recovered and checked the earlier sandbox proof. The declaration comparison confirms
both original signatures are unchanged, both original sorries are closed, and no new
sorry is introduced. Removed the inherited second-reading section so that the assigned
second reader can write an independent review.

The conservative interface check flags the proof-local `open`, `variable`, and `omit`
commands. Their scope and the unchanged downstream statements are documented in
`coord/changes/abelian-higher-direct-image-proof-scope.md`.

## Proved and sorry left

Proved, in node `sbc-lem-higher-direct-image-presheaf`:

- `AlgebraicGeometry.Etale.nonempty_higherDirectImage_iso_sheafification_abelian`.
- `AlgebraicGeometry.Etale.nonempty_higherDirectImage_iso_sheafification_abelian_single`.

No `sorry` remains in the item and none is added elsewhere. Every private helper is
proved. The statements allow arbitrary morphisms and integer degrees; no quasi-compact,
quasi-separated, nonempty-site, or nonnegative-degree hypothesis was introduced.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`
  (second reading: supplied by `DerivabilityStructureInjectives`).

- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already available transitively).

Removed from this node's proof dependencies:

- `prop-weil-pbc-inverse-image-exact`: the exactness instances needed for the derived
  adjunction already come from the existing source library, without this Sheaf theorem.
- `lem-weil-pbc-etale-restriction-injectives`: no restriction of injectives to an etale
  object is needed; the local argument works on the original site.
- `lem-weil-pbc-etale-inverse-image-restriction`: sections are corepresented directly by
  free abelian representables and the derived adjunction.
- `def-weil-pbc-etale-cohomology`: retained as a statement dependency, but the proof uses
  the derived-Hom presheaf that is already literally in the statement.
- `lem-weil-pbc-sheafification-exact` and
  `lem-weil-pbc-exact-functor-complex-cohomology`: the local-bijection sheafification
  criterion replaces the termwise-complex sheafification comparison.

This records pruning of this proof's needs, not a claim that other targets never use
these nodes or that every removed direct import disappears from the transitive closure.

## Where the brief, the DAG or earlier work was wrong

Checked the sources online at [Stacks 072W](https://stacks.math.columbia.edu/tag/072W),
[Stacks 0BKV](https://stacks.math.columbia.edu/tag/0BKV), and
[Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8); their TeX copies are absent
from this machine. Tag 0BKV supplies the K-injective complex version explicitly.

No statement error was found. The original restriction-of-injectives plan is
mathematically valid, but is unnecessary for the derived-Hom formulation that the
Lean statement actually uses. The existing proved module-coefficient argument supplies
a shorter route to adapt; its theorem cannot simply be applied to abelian coefficients.
The generic `Adjunction.derivedPlus` supplies the required adjunction without the extra
monoidal hypotheses on the etale-specific wrapper.

The additional closed source dependencies are
`prop-weil-pbc-derived-inverse-image-adjunction`,
`def-weil-pbc-derived-inverse-image`, `lem-weil-pbc-kinjective-hom-derived`, and
`lem-weil-pbc-derived-direct-image-triangulated`. These are general derived-category
tools. They do not replace any statement or step realized by this unit: the unit record
`sk-lem-failure-field` has no realized statement or proof-step nodes to bypass.

## Second reading by A3

1. Compared the delivered module with the repository version. The two public theorem signatures are byte for byte unchanged; only proof bodies, proof-local commands, proof imports, and the node proof metadata differ. Verdict: pass.
2. Compiled the module locally, including an axiom probe for both public theorems. Compilation succeeds; both theorem declarations use only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.
3. Read the private helper proofs and checked the local cycles-and-boundaries argument against the cited Stacks 0BKV/03Q8 route. No new split-off statement or hollow definition is present, and the two target statements remain exactly as strong as before. The recorded searches include Mathlib sheafification and locally-bijective results; no existing theorem duplicates this item. Verdict: pass.
4. Checked pruning against the imports and node metadata. The proof uses the derived-category injective comparison, right-derived-functor-plus support, site epi/mono support, and existing upper/lower-star coherence. The direct imports removed from the old route are listed above, and the node's `proof_deps` is exactly the union of the three proof-step `uses` lists. Verdict: pass.
5. Checked the unit route and DAG agreement. The unit `sk-lem-failure-field` has no realized statement or proof-step nodes for this item, so no unit step is bypassed. The node proof text, dependencies, and origin describe the delivered Lean route. Verdict: pass.

Changed during second reading: removed the redundant proof-only import `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`; it is already available transitively through `DerivabilityStructureInjectives`. Added this independent review section. No theorem or definition was changed.
