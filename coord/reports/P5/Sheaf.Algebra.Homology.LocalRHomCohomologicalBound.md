## What changed

Repair of return at 40fc7aa56: removed the duplicate
homObjMap_section_component from LocalRHomCanonicalNaturality. The existing
private lemma in the unclaimed HomComplexSectionsHomotopyNaturalityOfUniverses
module is now public with the same binders, statement and proof. The new
naturality module imports that module privately and reuses the existing lemma.
See coord/changes/local-rhom-component-lemma-reuse.md for consumer checks.


Constructed the resolved local cohomology presheaf, its additive comparison with
slice-derived morphisms, and its natural sheafification comparison with internal
Hom cohomology. The additive cocycle comparison is proved with its component and
localized-class formulas. A sheaf cycle now gives an explicit local chain map.
The K-injective representative isomorphism and its augmentation equation are
proved. The normalized internal-Hom target shift gives the coherent shift sequence,
additivity and homologicality. The assigned theorem assembles these constructions,
constructs the boundary from the presheaf shift, and proves the strict lower bound
using exact restriction and t-structure orthogonality.

The existing local normalization definitions are moved verbatim to
LocalRHomDefinitions and publicly reexported. No original signature, universe,
attribute or definition body changes. The change record is
coord/changes/local-rhom-normalization-interface.md. The downstream check found no
current Lean importers; the DAG parent still requires the retained theorem.

## Proved and sorry left

The original hole is CategoryTheory.LocalRHom.local_cohomological_bound. Its
assembly proof has no sorry. The following named results currently retain one
sorry each, so this is a decomposition with one upper hole closed and three
lower holes added, not a net proof closure:

- CategoryTheory.LocalRHom.section_actions:
  lem-per-local-rhom-section-actions.
- CategoryTheory.LocalRHom.target_shift_comparison:
  lem-per-local-rhom-target-shift-comparison.
- CategoryTheory.LocalRHom.cycle_unit_normalization:
  lem-per-local-rhom-cycle-unit-normalization.

All other new declarations have complete proofs or concrete construction bodies.
The new cyclesEquiv and cohomologyEquiv definitions are irreducible after their
proved characterization lemmas, to avoid elaborating the full construction while
checking component equations. The repaired eleven-module packet passed the import-ordered sandbox compile
(result 4077ae6c1e967b30d8c2091b). Every module compiled within 60 seconds;
the assigned module took 19.6 seconds, the reused component lemma module took
38.2 seconds, and the new naturality consumer took 43.7 seconds. No whole-library build or local Lean
executable is used. The delivery gate performs the remaining checks.
In particular the presheaf, section equivalences, normalized shift sequence,
representative comparison and local chain map are constructed independently of
those open results. No data are chosen from an unproved existence theorem. The
component formula uniquely determines the cycle equivalence; surjectivity of the
homology projection uniquely determines its cohomology equivalence.

## No longer needed

The direct Hom-into-triangle argument is replaced by the proved normalized
triangulated structure of internal Hom and Mathlib's homological functor instance.
Thus the original proof no longer directly needs
lem-weil-pbc-hom-into-triangle-exact or its module. This is only a direct-dependency
pruning claim: any use inside the normalized triangulated structure remains.
The new proof uses the independent-universe section comparison chain rather than
the specialized lem-pur-rhom-into-kinjective-local and lem-weil-pbc-kinjective-shift
as separate direct imports. The following old private imports are removed from
the relocated definition interface: RhomIntoKInjectiveLocal,
HomotopyCategory.KInjective, HomotopyCategory.ShiftSequence,
ModuleCat.Presheaf.Sheafification, ShortComplex.PreservesHomology,
Triangulated.Pretriangulated, FiniteTypeRestrictionExact,
DerivedCategory.KInjective, ShortComplex.ExactFunctor and
Triangulated.TStructure.Basic. Required instances and definitions are available
through the retained public interfaces; compilation checks that removal.

The additive comparison constructs its complex isomorphism directly from the
cochain and differential lemmas, so it does not import
HomComplexSectionsCanonicalComparisonOfUniverses. It retains the same canonical
component formula and proves additivity and uniqueness. Redundant private
presheaf-abelian, preserves-homology and sheafification imports are removed from
the cocycle module; the section-equivalence module also removes redundant
HomComplexSectionsQuasiIsoOfUniverses and sheafification imports.

The original node's following direct dependencies are now supplied through the
new model/comparison modules rather than cited separately by the assembly:
prop-pur-kinjective-resolutions-exist, def-pur-derived-internal-hom,
def-pur-hom-complex, def-pur-localized-ringed-site,
lem-weil-pbc-ringed-site-module-sheafification-exact,
lem-weil-pbc-exact-functor-complex-cohomology,
def-weil-presheaf-modules-sheafification,
lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-exact-functor-derived-factorization,
def-weil-triangulated-category and def-sp-homological-functor.
These are dependency relocations, not claims that their mathematics is unused.
The obsolete direct tool_uses approval for lem-pur-rhom-into-kinjective-local is
removed; the finite-type restriction approval stays.

The canonical naturality module has no direct RGammaDerivedLimit,
RhomIntoKInjectiveLocal or HomComplexSectionsCanonicalComparisonOfUniverses
imports. The repair replaces its direct HomComplexProjections import with the
existing HomComplexSectionsHomotopyNaturalityOfUniverses module to reuse the
component lemma. Those earlier modules remain in that module's dependency chain;
this is removal of redundant direct imports, not a transitive pruning claim.
The duplicate private component helper is removed.

No module is withdrawn. No adopted source-library declaration is removed.
The unit route through local internal Hom and its lower cohomological bound stays.

## Where the brief, the DAG or earlier work was wrong

The returned packet repeated an existing private component lemma. The repair
exposes and reuses it at its existing home, and adds that dependency to the
canonical-naturality node. No new sorry is added by this repair.


This resumed dispatch uses sandbox reference clock 1792773514.8115075
(2026-10-23), budget 7200 seconds and session limit 86400 seconds. Earlier search
records in the unchanged sandbox begin at 10:09 UTC. The launcher paused and
resumed this same item; no budget metadata was edited by this worker.

The supplied local statement is retained unchanged. Its section comparison needs
an additive equivalence with a fixed cocycle normalization: a bare existential
comparison in the existing naturality lemma does not by itself establish the
naturality of that fixed equivalence. The new component-characterized proof
addresses that distinction.

Taking sections of sheaves need not preserve cohomology. The concrete cycle map
uses the kernel of the section differential, not a nonexistent exactness instance
for taking sections. Cohomology is computed in module presheaves first, and exact
sheafification is applied afterward.

## New nodes

All new statements retain arbitrary integers, unbounded complexes, separate object
and morphism universes, and independent main and slice derived-category
universes. The local shift comparison is an isomorphism of functors before taking
sections, with both the representative formula and sheafification normalization.

- def-per-local-rhom-normalization-interface: verbatim relocation of the existing
  public definitions, required to avoid an import cycle among their proofs.
- lem-per-local-rhom-presheaf-model: concrete localization and sheafification,
  including the normalized K-injective representative comparison.
- lem-per-local-rhom-additive-cocycle-comparison: additive section cocycles,
  homotopy and derived classes, and the concrete local chain map.
- lem-per-local-rhom-canonical-naturality: the component-characterized comparison
  commutes with arbitrary maps of complexes into K-injective targets.
- lem-per-local-rhom-section-equivalence: concrete additive sections of the
  localized presheaf and its evaluation factorization.
- lem-per-local-rhom-shift-sequence: coherent normalized shifts and homologicality.
- lem-per-local-rhom-section-actions: compatibility with derived maps, scalars
  and restrictions for the fixed section equivalence.
- lem-per-local-rhom-target-shift-comparison: target reindexing at presheaf level
  with its section and sheafification equations.
- lem-per-local-rhom-cycle-unit-normalization: the cycle quotient/sheafification
  unit equation for arbitrary representatives.

The three open results are genuine separate parts of the local comparison
argument. The final boundary construction and orthogonality proof combine them
with the independently constructed objects. Searches and exact Lean attachments
are recorded in each node. The interface change record is named above.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
