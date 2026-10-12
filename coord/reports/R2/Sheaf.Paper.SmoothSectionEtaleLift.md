## What changed

Proved the unchanged declaration `AlgebraicGeometry.exists_etale_lift_of_smooth`
in `Sheaf.Paper.SmoothSectionEtaleLift` from the kernel-neighbourhood construction,
the existing global localization theorem, and a fully proved quotient-cutout helper.
The proof explicitly extends the section across the first localization, constructs
an inverse quotient equivalence, composes the algebra maps and proves the lift equation
by applying the injective quotient equivalence. No definition or existing statement changed.

Added `Sheaf.AlgebraicGeometry.EtaleSectionQuotientCutout`, with a complete proof
from the existing idempotent-splitting theorem and Mathlib. It descends the section,
base changes étaleness, lifts the quotient idempotent as an element (without asserting
that its lift is idempotent), identifies the localized quotient and proves the formula
on every element of the original algebra.

Added `Sheaf.AlgebraicGeometry.SmoothSectionEtaleNeighbourhoods`, isolating the
conormal/stabilization/basis-quotient construction preceding the global localization.
This remaining construction neither supplies a globally étale algebra nor asserts the
required quotient isomorphism. The parent proves both remaining steps. Its docstring and
node carry the complete source argument and existing dependencies for the next worker.
The construction's existing proof imports moved into its own module.

Updated the item's node to its compiled proof route, and added a node for each new helper.
Read Stacks Tag 07M7 online because the remote checkout has only literature lists;
the source route agrees with the existing ten-step node. The unit `sk-thm-p1` and its
`realized` declarations and steps were not changed or bypassed.

Local compilation of the three modules in import order passes without warnings.

## Proved and sorry left

- Proved (as a reduction): `AlgebraicGeometry.exists_etale_lift_of_smooth`
  (`lem-weil-pbc-smooth-section-etale-lift`). No sorry remains in the item.
- Proved: `AlgebraicGeometry.exists_localization_quotient_equiv_of_etale_section`
  (`lem-weil-pbc-etale-section-quotient-cutout`). No sorry in this helper.
- Exactly one delivered sorry remains:
  `AlgebraicGeometry.exists_etale_neighbourhoods_of_smooth_section`
  (`lem-weil-pbc-smooth-section-etale-neighbourhoods`), with body exactly `by sorry`.
  The existing `exists_etale_localization_of_prime_mem` dependency still has its
  pre-existing sorry. The complete theorem is consequently not yet axiom-free.

## No longer needed

Removed these six direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing`
- `Sheaf.AlgebraicGeometry.LiftProjectiveModuleEtale`
- `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`
- `Sheaf.RingTheory.SmoothConormalSequenceExact`
- `Sheaf.RingTheory.SymmetricAlgebraSmooth`
- `Sheaf.RingTheory.EtaleSectionIdempotentSplitting`

The first five are still required by the new construction's planned proof and are
imported there. The last is used by the proved cutout helper and is imported there.
`Sheaf.AlgebraicGeometry.EtaleLocalizeUpstairs` stays a direct proof import.
The item's direct proof dependencies are now its two new helpers, global localization,
the localization universal property and étale composition. These are proof-only imports.
The old `lem-weil-pbc-lift-invertible-element` node is not used by this route:
principal-localization étaleness is provided by Mathlib and composition. The other
old mathematical ingredients have been assigned to the helper that needs them.
No module is claimed to leave the whole library's target closure.

Complete list of old direct `proof_deps` no longer used directly by the parent
(the construction and cutout nodes retain their corresponding ingredients):

- `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`
- `def-sbc-smooth-morphisms`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-smooth-conormal-sequence-exact`
- `def-weil-pbc-kahler-differentials`
- `lem-weil-pbc-jacobi-zariski-quotient-smooth`
- `lem-weil-pbc-finite-projective-rank-locally-constant`
- `lem-weil-pbc-nakayama-local-generators`
- `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`
- `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing`
- `def-weil-etale-morphism`
- `lem-weil-pbc-etale-quotient-base-change`
- `lem-weil-pbc-etale-section-idempotent-splitting`
- `lem-weil-pbc-lift-invertible-element`
- `lem-weil-pbc-symmetric-algebra-universal-property`
- `lem-weil-pbc-symmetric-algebra-finite-projective-smooth`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-lift-projective-module-etale`
- `lem-weil-pbc-kahler-differentials-base-change`

The smooth/étale definition nodes remain in statement dependencies; removing them
from the parent's proof list does not remove those notions.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The source literature file is absent locally;
read https://stacks.math.columbia.edu/tag/07M7 instead. LeanSearch returned an internal
server error on both new statements, recorded as unavailable in the actual search log.
LeanFinder and source grep succeeded and found ingredients, not these constructions.
Blueprint searches for `07M7`, `smooth section` and `etale section`, and repository
searches by statement/name found no duplicate of either new helper.

Edge cases checked mathematically before stating the helpers: if `J = top`, the
section target is the zero ring and the construction may use the zero algebra; its
spectrum is empty, so the prime-neighbourhood condition is vacuous. The cutout can
invert a lift of the zero idempotent, giving a zero quotient. If `J = bot`, the section
is already an A-algebra map to A, and the stabilization construction still applies.
The zero ring and the rank-zero free conormal case introduce no nontriviality or
positive-rank hypothesis. For `C = A` and the quotient section, the cutout can use `g = 1`.
For a product étale algebra, the quotient idempotent separates the chosen factor; the
initial algebra need not have quotient isomorphic to A/J. These checks confirm why the
remaining construction is strictly less than the item and why the cutout is necessary.

## New nodes

`lem-weil-pbc-smooth-section-etale-neighbourhoods`:
`lean/Sheaf/AlgebraicGeometry/SmoothSectionEtaleNeighbourhoods.lean`, declaration
`AlgebraicGeometry.exists_etale_neighbourhoods_of_smooth_section`. It packages original
steps 1–5, 8–9 and the primewise part of step 6, before Tag 07M0. Its dependency list
preserves the source's conormal, projective lifting, symmetric algebra, rank, Nakayama,
Jacobi-Zariski and cotangent criterion arguments.

`lem-weil-pbc-etale-section-quotient-cutout`:
`lean/Sheaf/AlgebraicGeometry/EtaleSectionQuotientCutout.lean`, declaration
`AlgebraicGeometry.exists_localization_quotient_equiv_of_etale_section`. This proves the
idempotent cutout and quotient-compatibility portion of original step 7, for an arbitrary
étale algebra with a section modulo an ideal. It has no sorry. Its proof uses the existing
quotient base-change, idempotent splitting and localization-quotient-commutation nodes.

No change records are needed: all existing signatures and public imports are unchanged.

## Second reading by R2

1. **Visible contract: pass.** Compared the existing module against the repository
   with `diff`; the complete signature of `exists_etale_lift_of_smooth`, including
   universes, hypotheses, algebra structures, bijectivity and lift equation, is
   byte-for-byte unchanged. All four existing public imports are unchanged.
   Only proof imports, the proof and its explanatory docstring changed. The two
   other delivered modules are new; no definition or existing signature changed.
2. **Kernel proof: pass as a reduction.** Recompiled all three files locally in
   import order without errors or warnings. A scratch copy printed the axioms of
   all three declarations: the quotient cutout has exactly `propext`,
   `Classical.choice`, `Quot.sound`; the parent and construction also have
   `sorryAx`. The only delivered sorry is the named neighbourhood construction,
   with body exactly `by sorry`. There is no definition with sorry and no axiom,
   unsafe, opaque, extern or implemented_by declaration. Read the descent of tau,
   quotient base-change instance, localization equivalence, ideal-map equality,
   and final compatibility calculation; all use the actual structural maps.
3. **Split statements: pass.** Read Stacks [Tag 07M7](https://stacks.math.columbia.edu/tag/07M7)
   against the new statements and their docstrings. The neighbourhood statement
   stops before the global denominator and quotient-isomorphism arguments; the
   parent genuinely proves these remaining steps. It is not the parent renamed.
   The cutout is fully proved for an already etale algebra, without assuming its
   quotient equals the base quotient. Checked J=top (zero quotient, vacuous
   prime condition), J=bot, rank zero, C=A and a product etale algebra. No
   nontriviality, positive rank or idempotent-lift assumption is introduced.
   New searches used “unramified along the kernel” and “principal localization
   and reduction”, plus repository searches for retractions and localization
   equivalences. LeanFinder found nilpotent-ideal formal lifting and standard
   etale ingredients, not either helper; source grep confirmed no duplicate.
   Loogle rejected the queried quotient identifier, so that attempt is not
   evidence of absence. The hard conormal/stabilization construction cannot be
   closed by these existing special-case lemmas in a few minutes.
4. **Route and pruning: pass after correction.** Read the unit sk-thm-p1 and its
   realized statement and four steps; this subsidiary Tag 07M7 reduction changes
   none of them. The parent uses the shortest existing localization and
   idempotent-splitting route, and the helpers retain the construction plan.
   The six removed direct Sheaf imports move to their proper helpers. Corrected
   the pruning report to list every removed old direct proof dependency and
   acknowledge that lift-invertible-element is no longer used. Changed the new
   cutout's quotient Operations import to a proof import, keeping only Defs
   public for its signature. All other imports supply signature vocabulary,
   actual proof ingredients, or the open construction's stated proof plan.
5. **DAG agreement: pass after correction.** Checked all three nodes against
   their Lean signatures, sources, chapter/unit, proof-dependency unions,
   origin records and new-node metadata. The parent's changed fields are only
   proof, proof_deps, proof_origin and lean (the unchanged signature is now
   recorded verbatim rather than collapsed onto one line). The construction node had copied an
   opening claim of the full parent theorem and stale step references: replaced
   that claim with its primewise factorization goal, corrected the basis and
   exact-sequence references, and made its proof-origin description accurate.
   Its docstring now specifies the direction of precomposition from B into the
   enlarged algebra. No statement was altered by these documentation repairs.

Second reading changed the parent-node signature formatting, construction-node
proof narrative, step references and origin description, one new-helper docstring sentence, the new cutout's
proof-only import scope, and the completeness of the pruning report. The Lean
proof bodies were sound and were retained.
