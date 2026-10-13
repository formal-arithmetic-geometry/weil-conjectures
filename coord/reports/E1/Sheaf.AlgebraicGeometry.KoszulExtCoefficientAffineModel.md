## What changed

Reduced `AlgebraicGeometry.koszulExtCoefficient_affine_model` to two independent,
strictly lower comparison statements, preserving its entire signature and existing
docstring. This is a decomposition, not a sorry-free proof of the mathematical result.

The proof uses `ExteriorAlgebra.exists_koszul_projective_resolution`, transports
its augmentation along the equality of chain complexes, extends to integer cochain
degrees, and composes with the extension-single isomorphism. The existing
`affine_koszul_finite_free_resolution` supplies the sheafified augmentation, upper
bound, and finite free terms. The proof establishes the lower bound `-n` directly:
for exterior degree greater than n, the exterior basis is indexed by an empty
powerset type, so the module and its associated sheaf vanish.

The first new theorem gives a coefficient-natural local derived comparison for
an arbitrary bounded finite free resolution. The second gives the underived
Koszul Hom coefficient square, without regularity, generation, resolutions, or
a derived category. The original proof composes their isomorphisms and uses the
naturality equation at the specified coefficient morphism. No data definition
or existing statement was changed. The parent node now records this actual route.

New modules:

- `Sheaf.AlgebraicGeometry.LocalFiniteFreeHomologyNatural`.
- `Sheaf.AlgebraicGeometry.AffineKoszulCoefficientHomCoordinates`.

Added proof imports in the item are the two new modules,
`Sheaf.AlgebraicGeometry.AffineKoszulFiniteFreeResolution`, and
`Mathlib.Algebra.Homology.Embedding.ExtendHomology`. The original exterior basis
import is retained for the explicit lower-bound proof. All public imports stay
unchanged. No modules held by other groups were adapted.

## Proved and sorry left

Original hole closed by decomposition:

- `AlgebraicGeometry.koszulExtCoefficient_affine_model`
  (`new-k1-koszul-ext-coefficient-affine-model`). Its body contains no sorry.

New holes added, each in its own module, with a full proof in words and DAG node:

- `AlgebraicGeometry.local_finite_free_homology_natural`
  (`lem-sc-local-finite-free-homology-natural`). This is the derived comparison,
  natural in all coefficient sheaves, for a supplied bounded finite free resolution.
- `AlgebraicGeometry.affine_koszul_coefficient_hom_coordinates`
  (`lem-sc-affine-koszul-coefficient-hom-coordinates`). This is solely an underived
  Hom-complex calculation for an arbitrary sequence and the actual quotient
  coefficient map.

Counts: one original hole closed, two holes added, no sorry left in the original
module. The lower exterior-power vanishing and composition of the comparison
squares are proved directly. The delivery does not claim net hole reduction.

Edge cases checked in the new statements: rank zero free terms, the zero
resolution, empty opens/charts, the zero ring, n=0, and m>n. The underived statement
requires neither generation nor regularity; those hypotheses are used only to
obtain the resolution in the original proof. No open derived-category instance
in the supplied universe has been added.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`: its
  natural-number chain resolution theorem and node
  `lem-sc-affine-quotient-resolution-sheafification` are not used in this route.
  The existing integer-indexed `AffineKoszulFiniteFreeResolution` does the needed
  sheafification and finite free calculation directly.
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`: no longer directly used by the
  original theorem; it remains a proof dependency of the new natural comparison.
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`: likewise moved below the
  new natural comparison, so its node is still needed there.
- `Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits`: no longer directly used
  by the original proof; retained below the finite free resolution and the
  underived coordinate comparison.

For completeness, the old `proof_deps` divide as follows. The projective-resolution
node `new-j3-koszul-projective-resolution` and exterior-basis node
`lem-weil-pbc-exterior-power-free-basis` remain direct proof dependencies. The node
`lem-sc-affine-quotient-resolution-sheafification` is removed from this route.
The nodes `lem-sc-derived-internal-hom-restrict-open` and
`lem-sc-derived-hom-finite-free-model` move below the new natural comparison;
`lem-sc-tilde-preserves-finite-limits` remains below the existing finite free
resolution and the underived comparison. The node
`new-j3-koszul-quotient-coefficient-complex` remains a statement dependency and
is used below the underived comparison. None of these latter four is claimed
as pruned from the full targets' import closure. No unit statement or
unit proof step was bypassed. The unit record's realized lists are empty; the
changes refine only this node's local argument.

The scalar-only `AffineKoszulHomCoordinates`, `AffineKoszulHomComplexIso`, and
`LocalFiniteFreeScalarHomology` are not imported: objectwise scalar comparisons
do not provide this coefficient square. The broad
`KoszulRegularSequenceDualComplex` module is also unnecessary: the integer
augmentation is obtained directly from the smaller projective-resolution module
and Mathlib's extension API. These are avoided routes, not claims of newly
unreachable modules in the whole target closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's restriction and finite free model declarations give
`Nonempty` isomorphisms separately for individual objects. Their Lean signatures
do not assert compatibility with a coefficient map. Similarly the existing
associated quotient sheaf isomorphism does not assert compatibility with the
adjunction-unit map. One cannot infer the desired commuting square from those
objectwise isomorphisms alone. The two new statements make these missing
compatibilities explicit, and split derived naturality from underived quotient
coordinates.

The generic comparison is intentionally restricted to bounded resolutions:
the original Koszul complex has this stronger property, proved here. This
matches the strictly perfect calculation in Stacks Tag 08DM, without needing
a boundedness claim for a functorial K-injective resolution. Existing references
to Tag 0GM8 describe a stalk comparison; Tag 08DM is the direct source for the
bounded finite free Hom computation used in the new statement.

No mathematical dispute, signature change, hollow definition, forced adaptation,
or tool workaround was introduced. The original theorem needs a documented local
heartbeat increase to elaborate the coefficient functor comparison; its single-file
compile remains within the required wall-clock limit.

## New nodes

`lem-sc-local-finite-free-homology-natural`, in
`dag/nodes/sec-picard-framework/`, states the natural comparison on arbitrary
coefficient sheaves for a supplied bounded finite free resolution on an open.
It has no Koszul, affine, or closed-immersion hypotheses; its role is only the
derived part of the original argument. Source: Stacks Tags 08DL and 08DM.

`lem-sc-affine-koszul-coefficient-hom-coordinates`, in the same directory, states
the square for ordinary sheaf Hom cohomology of the explicit sheafified Koszul
complex. It has no regularity or generation hypotheses and no derived-category
binder. Source: Stacks Tag 0BQZ, the map between the two displayed Hom complexes,
and Tag 01HV for exact sheafification. No change record is needed.


## Second reading by E1

1. **Existing interfaces: pass.** Compared every delivered module to the repository.
   The two auxiliary modules are new; the entire existing signature of
   `AlgebraicGeometry.koszulExtCoefficient_affine_model` is byte-for-byte unchanged.
   Its original docstring and all public imports are unchanged. No definitions,
   existing statements, or modules belonging to another group were adapted.

2. **Proof and compilation: pass.** Compiled all three modules in import order with
   `lcompile.py --all`; there were no errors or warnings. Read the augmentation
   transport, integer extension, finite free sheafified augmentation, exterior-power
   vanishing below `-n`, and the final composition of naturality squares. Only the
   two reported public theorems contain `sorry`, each exactly `:= by sorry`.
   There are no data definitions or forbidden declarations in the delivery.
   A scratch copy with `#print axioms` for all three declarations compiled:
   each uses only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
   The latter is expected from the documented open comparisons and their
   dependencies; this delivery does not claim axiom-free target closure.
   The scratch copy was removed before delivery.

3. **New lower statements: pass.** Read both complete proof docstrings and their
   nodes against Stacks Tags 08DL, 08DM, 0BQZ and 01HV. The generic comparison has
   an arbitrary coefficient variable and a supplied bounded finite free resolution;
   the underived square has no regularity, ideal generation, augmentation or derived
   category. Thus neither simply restates the original theorem. Checked rank-zero
   terms, zero complexes with a quasi-isomorphism, empty opens, the zero ring,
   `n=0`, `m>n`, and `n=1` with an arbitrary sequence not contained in the ideal:
   in the last case both degree-zero differentials are negative precomposition,
   and reduction still commutes with them. For `n=0`, the underived square is
   precisely the quotient coefficient map, even for a nonzero ideal; in the original
   theorem the generation hypothesis forces the ideal to be zero. Independent
   LeanFinder, Loogle and Mathlib/local-source grep searches, using perfect-complex
   restriction, coefficient morphisms and free-Hom naturality, found component APIs
   but no existing theorem giving either complete natural comparison. Existing
   scalar-only affine comparisons do not assert the needed coefficient square.
   Neither hole can be closed by a short application of those objectwise statements.

4. **Route and pruning: pass.** The proof uses the existing Koszul resolution and
   finite free sheafification before invoking the two missing comparisons. Its
   direct exterior-basis lower-bound argument and square composition are genuine
   reductions. All new proof-only imports are plain `import`; public imports of
   the new modules supply types or definitions occurring in their signatures.
   Checked every old `proof_deps` entry against the revised proof. Clarified their
   disposition in `No longer needed`, distinguishing removed direct dependencies
   from nodes still needed lower down. The unit `sk-thm-picard-duality` has empty
   realized lists; no realized unit statement or proof step is bypassed or edited.
   This remains a decomposition: one original hole closed, two new holes added,
   net minus one, with no claim that an entire comparison is sorry-free.

5. **DAG agreement: pass.** The parent node changes only `proof`, `proof_deps` and
   `proof_origin`. Its steps match the augmentation, lower-bound argument and
   comparison-square composition. Both new nodes have matching verbatim Lean
   signatures, sources, proof steps, dependency unions, search records, creation
   metadata, ancestry, chapter, unit and Lean records required by the brief.

Second reading changed only this report: made the disposition of every old proof
node explicit and recorded the independent checks. No correct Lean proof or
statement was rewritten.
