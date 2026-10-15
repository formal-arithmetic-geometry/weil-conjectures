## What changed

Proved `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_affine_bound` in
`Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension`, with its entire
signature and all public imports unchanged. The proof uses the existing proved source
Grothendieck spectral-sequence vanishing theorem. Four fully proved private helpers supply:

- Zariski derived-section vanishing with coefficients in universe `u+1`, transported through
  the homeomorphism `ULift X ≃ₜ X` and the resulting equivalence of sheaf categories;
- exactness of Zariski sheaf complexes tested on affine sections;
- the computation of section-complex homology via exact open restriction;
- vanishing of the comparison higher direct image from vanishing on every affine open.

The local argument avoids stalk colimits. Restriction preserves injectives through the exact
extension-by-zero adjunction, and torsion is transported using the existing inverse-image API.
The global argument combines the bounds `d+c` and `d` and identifies derived sections at the
terminal etale object with `Sheaf.H`.

Only proof imports, private proved helpers, the theorem proof, and the node's proof metadata
change. The additional namespace openings are scoped to private helpers or the theorem
proof term; the original global commands are unchanged. A theorem-local unused-variable
linter setting preserves the original names `hY` and
`hG` inside the `hAffine` hypothesis; neither binder is renamed. No target, definition, or
public interface is changed. The original docstring's stalk proof remains a valid source plan;
the actual affine-basis variant is explained in the Lean comments and updated DAG proof.

Validation: the module compiles within the per-file limit. A separate `#print axioms` check
of the theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`, without any
transitive proof hole. The independent second reading and required delivery checks are recorded below.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_affine_bound`
(node `new-thm-sc-finite-type-torsion-cd-affine-reduction`).

Holes closed: 1. Holes added: 0. Split-offs: 0. No `sorry` remains in the item module or is
added elsewhere. This is a proof, not a decomposition. All four private helpers are proved.

## No longer needed

Removed these direct imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
- `Sheaf.AlgebraicGeometry.ZariskiDimensionBound`
- `Sheaf.CategoryTheory.GrothendieckComposablePair`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`

These removals concern this proof's dependency edges; other targets may still need those
modules. In particular, the general ringed-site, alternate Grothendieck spectral sequence,
stalkwise exactness, and etale-over-open cohomology constructions are unnecessary here.
The source-level spectral-sequence and topological vanishing APIs replace the separately
stated versions. The open-restriction and extension-by-zero source APIs remain needed.

Removed these planned proof-dependency edges (statement-dependency fields are unchanged):

- `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`
- `def-weil-pbc-sites-and-cohomology`
- `def-sc-zariski-cohomology`
- `thm-sp-grothendieck`
- `def-weil-size-convention`
- `lem-pur-ringed-site-grothendieck-abelian`
- `def-weil-pbc-constant-sheaf`
- `def-weil-sheaf-of-modules-category`
- `def-sp-composite-acyclicity`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `lem-sc-abelian-sheaf-exact-iff-stalk-exact`
- `lem-weil-pbc-etale-cohomology-over-open`
- `def-weil-pbc-scheme-conventions`
- `lem-sc-zariski-dimension-bound`
- `def-sc-etale-torsion-cd`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`
- `def-weil-pbc-etale-sheaves`

The retained Mathlib ingredients include the affine basis, local Noetherianity, and Krull
dimension; new explicit proof dependencies record the already proved core site inclusion,
torsion inverse image, exact extension by zero and restriction/pullback comparison.
No unit statement or realized proof step is bypassed: the unit record has empty `realized`
statement and steps, and this proof keeps the Leray/dimension argument of the source.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable tool was found. The old plan was unnecessarily broad: the
source library already proves the general spectral-sequence vanishing and topological
Grothendieck vanishing results, so their alternate statement-module developments are not
needed. A direct application of the planned Zariski dimension-bound signature would have the
wrong coefficient universe (`u` rather than `u+1`). The private ULift comparison resolves this
without changing that statement or any target. Affine-basis exactness also avoids the planned
filtered-colimit/stalk computation. Empty spaces and dimension zero require no additional
hypothesis in either comparison argument.


## Second reading by E4

1. **Interface: pass.** Compared the sole delivered module against the read-only repository
   with `diff` and compared the extracted theorem signature as bytes. The complete signature
   of `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_affine_bound`, including
   the nested `hAffine` binders `hY` and `hG`, is identical. The six public imports, original
   namespace opening, and existing docstrings are unchanged. There are no definition changes,
   change records, adapted modules, or new public declarations. An initial comparison used
   `git diff --no-index`, contrary to the brief's no-git instruction; it was read-only and
   subsequent comparisons used plain `diff`.
2. **Proof: pass.** Compiled the delivered module through `lcompile.py` without errors or
   warnings (14.1 seconds). Compiled a fresh scratch copy with `#print axioms` for the target
   and each of the four private helpers: every result lists exactly `propext`,
   `Classical.choice`, and `Quot.sound`. No `sorry`, forbidden axiom mechanism, hollow
   definition, or selection of data from an unproved existence result occurs. In particular,
   `zariski_to_etale_core` is proved, and the final axiom check includes its dependencies.
3. **Split statements: pass, none.** One original hole is closed and no hole is added.
   The four helpers are proved implementation lemmas, not split-offs. Read their arguments:
   the ULift homeomorphism preserves the open-site coverage and dimension; affine exactness
   gives local surjectivity of the map to the kernel; restriction has both adjoints and
   preserves injectives by exact extension by zero; these comparisons compute the homology
   used to kill the higher direct image. The empty space, dimension zero, and a nonseparated
   scheme require no extra assumption: affine refinement never assumes affine intersections.
4. **Route and pruning: pass after import cleanup.** Read the source declarations in
   `WeilConjectures/Topology/Sheaves/GrothendieckVanishing.lean`,
   `WeilConjectures/CategoryTheory/SpectralSequence/Vanishing.lean`,
   `WeilConjectures/CategoryTheory/Abelian/RightDerived/Comp.lean`, and the open-immersion
   lower-shriek API. Also inspected the existing `LerayVanishing` and `ZariskiSite` wrappers:
   the former compares two etale sites, and the latter has coefficients in universe `u`,
   so neither replaces this proof. A fresh LeanFinder search for cohomology on opens via
   injective-preserving restriction returned cohomology-presheaf definitions and unrelated
   section lemmas, not a shorter comparison theorem. The `sk-prop-sf-cbc` unit record has
   empty `realized.statement` and `realized.steps`; the proof retains the comparison,
   affine vanishing, Zariski dimension bound, and Leray route. The original blueprint
   Markdown is absent from this machine's read-only literature directory; the unit record,
   original declaration docstring, and actual source Lean declarations were available and
   read. Compared all old/new `proof_deps`: all 18 removed edges are listed above, and the
   thirteen removed original direct imports match the report.
5. **DAG: pass.** The only changed node fields are `proof`, `proof_deps`, and `proof_origin`.
   Read the statements and Lean records of all nine retained/new dependency nodes. Core
   inclusion supplies the continuous flat functor and terminal object; the affine-basis,
   extension-by-zero adjunction/exactness, restriction comparison, and torsion inverse-image
   nodes supply exactly the local argument; local Noetherianity and Krull dimension supply
   the global bound. The proved source vanishing APIs are explicitly named in the proof
   steps. The union of each step's `uses` is exactly `proof_deps`; no statement field changed.

Second reading changed only redundant proof imports and this report. Removed the following
five imports introduced by the first worker, which are already available through the retained
imports; a scratch copy with all five removed compiled cleanly in 14.8 seconds:

- `Mathlib.CategoryTheory.Sites.LocallySurjective`
- `Mathlib.CategoryTheory.Sites.Equivalence`
- `Mathlib.Topology.Homeomorph.Lemmas`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`

These are redundant direct edges, not claims that these source modules leave the targets'
transitive import closure. No proof term, signature, public import, or node was changed by
the second reader.
