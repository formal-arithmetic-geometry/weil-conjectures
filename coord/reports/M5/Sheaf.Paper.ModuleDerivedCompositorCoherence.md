## What changed

Proved all four theorems of `Sheaf.Paper.ModuleDerivedCompositorCoherence`, preserving
all public signatures, definitions, public imports, and existing docstrings.
The proof specializes the already proved generic unbounded derived-composition
associativity and unit laws in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp` to
module-object pushforwards. Three proved private helpers establish postcomposition compatibility, agreement of
the two canonical derived identity constructions, and identity normalization on
K-injectives. Composition normalization reuses the existing
`CategoryTheory.UnboundedSectionsLocalization.compIso_objQ`, made public in its original
unclaimed module with its statement and proof unchanged.
The complex/homotopy/derived localization comparison is retained explicitly.
Three private proof imports supply the existing normalization theorem, the generic
coherence API, and naturality of derived
transformations on K-injective complexes. Local elaboration transparency options
allow the canonical mapped-complex identifications to be recognized. The retained
commutative-ring and admissibility parameters are unchanged, although these formal
coherence calculations do not require the admissibility hypothesis.

Updated the node's proof, proof dependencies, proof origin, and obsolete tool-use
entries to describe the shorter proof. The compactification unit's statement and
steps are preserved; this only replaces the internal argument for its compositor tool.
No new module or theorem statement is introduced. The existing compIso_objQ becomes
public in place. Its `Comp` import becomes public because its signature needs
PreservesKInjectiveComplexes. Its node attachment records the exposed helper; the
item node records this additional proof dependency.

## Proved and sorry left

Closed four existing holes (retained from the returned proof), all on node
`lem-sfb-module-derived-compositor-coherence`:

- `AlgebraicGeometry.ProEtale.CondensedRing.module_derived_compositor_normalization`
- `AlgebraicGeometry.ProEtale.CondensedRing.module_derived_compositor_coherence`
- `AlgebraicGeometry.ProEtale.CondensedRing.module_derived_identity_normalization`
- `AlgebraicGeometry.ProEtale.CondensedRing.module_derived_compositor_units`

Holes added: none. Holes left in the delivered module: zero. This is a proof,
not a decomposition. The delivery compile includes the tool's independent axiom probe.

## No longer needed

Removed the duplicate private helper compIso_objQ and its proof; the existing lemma
in Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization is now imported and used.
No module is withdrawn for this repair.

Removed these private proof imports:

- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`

The final import was also unnecessary for the existing definitions: the adopted
module-object API already supplies exact inverse image and its adjunction.

The old proof dependencies `lem-sfb-module-section-derived-comparison-square`,
`lem-sfb-compositor-equivalence-conjugation`, and
`lem-pur-ringed-derived-composition-cocycle` are unnecessary for this node.
Their modules `Sheaf.Paper.ModuleSectionDerivedComparisonSquare`,
`Sheaf.CategoryTheory.CompositorEquivalenceConjugation`, and
`Sheaf.CategoryTheory.RingedDerivedCompositionCocycle` are not imported by this proof.
The module/section equivalence, its coefficient-action square, and the ringed-topos
comparison do not need to be reproved to establish coherence of the already defined
universal module compositor. No module is withdrawn; these results may have other users.

Removed obsolete top-level tool-use approvals for
`lem-sfb-internal-module-operations-transport`,
`lem-sfb-section-ring-lax-pushforward-coherence`, `lem-sfb-eta-comp`,
`det-prop-sfb-module-pullback-exact-main`,
`lem-pd-section-derived-pushpull-normalization`,
`lem-pur-ringed-derived-composition-cocycle`, and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
Kept the K-injective-preservation tool. The new route uses the existing proved
source composition construction recorded as `lem-fin-kinjective-derived-composition`;
its generic coherence API is in the adopted finite-coefficient composition module.

## Where the brief, the DAG or earlier work was wrong

The planned section-module transport argument is valid but longer than necessary.
The adopted source already contains generic, unbounded associativity and both unit
laws, despite the finite-coefficient path of their containing module. They apply to
arbitrary additive functors between the abelian categories used here. Ordinary
module-object compositor coherence and preservation of K-injectives meet all their
hypotheses. This removes the need to instantiate the much larger section-module
comparison-square and equivalence-conjugation statements.

No false statement, changed target, hollow definition, forced consumer adaptation,
or new proof obligation was required. Searches through leanfinder, loogle, and the
local sources were performed; the exact usable coherence API was found in the
adopted source rather than Mathlib's search index.

Preflight requested a visible-command change record for the local elaboration/linter
options. It is `coord/changes/M5-module-derived-compositor-proof-options.md` and lists
all downstream modules and current holders. No consumer adaptation is required.

The return correctly identified a duplicate generic normalization lemma. It was private
in the existing module, so importing alone could not expose it. This repair exposes it
in place, imports that module privately, and uses its fully qualified declaration;
there is now only one proof of that statement. The exposure and signature dependency
are recorded in coord/changes/M5-reuse-existing-composition-normalization.md. All seven
public signatures and all three definition bodies of the item are unchanged from the
current main source. No forced consumer adaptation or new hole is needed.

Repair verification: `lcompile.py --all` compiled both delivered modules successfully.
The current, unmodified `Sheaf.Paper.IdentityOpenDerivedRestriction` also compiled
against the sandbox dependencies; its temporary source copy was removed before delivery.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
