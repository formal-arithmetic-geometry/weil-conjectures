## What changed

Completed `AlgebraicGeometry.Etale.proper_ambient_double_dual_compatibility` using the
existing braided adjunction and closed-category dual-comparison API. The proper support,
compactification mate, trace, evaluation and product constructions are retained. Normalized
the double-dual and exchange maps to their canonical closed-category forms and packaged
the same four predicate clauses generically; the change record gives the normalization
argument and exact old/new definitions. Updated the node to the proof actually used.

Change record: `coord/changes/delta-proper-canonical-closed-api.md`.
No downstream importing modules or forced adaptations were found.

Repair of return C-abbd2 (head abbd26fb1): compared the retained packet with the
current restored library source. The theorem signature and the evaluation, product,
proper support comparison, composition mate, dualizing isomorphism and trace are
verbatim unchanged. The packet reapplies the reviewed canonical presentation and
complete proof to that source. The node preserves all current metadata except the
permitted proof, Lean attachment and pruning fields. There is no rework row for this
item and no archive or module is withdrawn.

Repeated the three downstream-use checks against the current library: zero external
consumers of the changed definitions, so no consumer adaptation is needed. The
sandbox contains exactly one Lean module, one existing node update and the change
record. No new theorem holes or modules are introduced.

The preceding retry's delivery was interrupted with exit 143. This retry runs the
unchanged tools again. The local compile mirror initially lacked Mathlib.olean;
the supported server route compiled the complete module successfully in 15.2 seconds
with no warnings. The delivery tool performs the final compile and preflight checks.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.proper_ambient_double_dual_compatibility`
(node `lem-weil-delta-proper-pushforward`). Proved 1 of 1 original sorries; zero sorries
remain in the item, zero added, zero split off. The private normalization, naturality,
and assembly lemmas are all proved. Existing dependency holes are not claimed closed.

## No longer needed

Removed imports from the current source:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `Sheaf.Paper.DualityPairing`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`
- `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`
- `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Mathlib.Topology.Defs.Filter`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `WeilConjectures.Algebra.Homology.RhomGlobalSections`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition`
- `Sheaf.SixFunctors.TensorProjectionAdjunct`
- `Sheaf.SmoothPurity.InternalAdjunctionEvaluation`

The route no longer needs these direct proof dependencies:

- `pqf-lem-locnoeth-lft`, `def-weil-finite-type-morphism`, and
  `def-asd-compactifiable`: the existing compactification/adjoint API synthesizes the
  needed instances without the separate Noetherian or over-field assertions.
- `lem-sf-unbounded-compact-support-proper-composition`: the explicit existing composition
  isomorphism is retained directly; its separate normalization theorem is unnecessary.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`, `lem-pur-rhom-global-sections`, and
  `def-pur-derived-internal-hom`: the already constructed monoidal closed derived category
  supplies the adjunction and its formal identities.
- `lem-weil-duality-pairing`: its triangle and shift theorem is unnecessary; the canonical
  double-dual map and its formal comparison square are already proved in the source library.
- `prop-asd-internal-adjunction`, `lem-asd-internal-adjunction-evaluation`, and
  `lem-amb-tensor-projection-adjunct`: DoubleDualProper already proves the generic canonical
  comparison isomorphism by the same adjunction/projection argument.
- `lem-amb-proper-coproducts-projection` and module
  `Sheaf.AlgebraicGeometry.ProperProjectionFormula`: use the underlying unbounded finite
  proper projection theorem directly, with no reordered projection or Noetherian hypotheses.

The removed modules are not needed by this proof; this does not assert that other parents
in the project cease to need them. The unit has no realized statement or numbered steps;
its route is preserved. No item module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned separate internal-adjunction/evaluation argument already exists as proved
source-library declarations in DoubleDualProper and DoubleDual. Repeating it is unnecessary.
The earlier development had several naive specializations that unfolded large
closed-category instances and timed out. On the current build the previous `simpa` also
expanded the predicate unnecessarily. Direct application of the generic theorem compiles
without this normalization tactic and without raising the compiler limit.
The draft node cited def-weil-derived-pullback-tensor-hom for the formal closed-category
identities. That node concerns adic pro-etale operations and is not used: removed the citation;
the formal identities are the already proved DoubleDual source-library API named in proof_origin.
The original target theorem signature is unchanged. The changed definitions require semantic
review, as recorded above; no mathematical weakening or new assumptions are intended.

The returned delivery was accepted mathematically but could not land because the item was
restored and changed after its old base. This packet reapplies the actual proof and
normalization to the current restored source; it is not an unchanged re-push. The current
source uses `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
`WeilConjectures.Algebra.Homology.RhomGlobalSections`; the removed-import list now uses those
current module names.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
