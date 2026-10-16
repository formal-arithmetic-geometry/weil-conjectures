## What changed

The common coefficient equivalence is constructed explicitly, using a single point-ring
identification and a single sectionwise internal-module encoding on every scheme. The
constructive helpers of ConstantInternalModuleSheafEquivalence are exposed in their own
namespace; its existing existence theorem keeps its signature. The coefficient realization
statement itself keeps its signature.

The ordinary pro-etale constructible-origin theorem replaces the planned detour through
external SheafOfModules. A separate finite-presentation transport theorem isolates what is
needed to apply that existing result. The derived comparison obligation is reduced to
coherent pullback isomorphisms and invertibility of their canonical right mates. The unit
and counit equations are proved from Mathlib's mate identities. An explicit categorical
three-step theorem constructs the four vertex isomorphisms and proves the three commuting
squares by naturality.

The duplicate older pro-etale functor modules reexport the finite-coefficient implementation.
This is necessary to combine the ordinary constructible-origin/comparison API with the
internal-module exchange API: the two previous import paths exported duplicate declarations
with the same fully qualified names. The two differently stated coherence formulas retain
separate names; the old iso-equality names are preserved by aliases in the canonical
finite-coefficient coherence module. The compatibility coherence re-export therefore
contains no duplicate alias declarations.

A separate general formal transport theorem isolates the remaining restriction of the
ambient three-factor comparison to the specified restricted exchange. It assumes coherent
comparison data for the continuous-function coefficient of the finite discrete
ell-torsion ring B and an arbitrary family of functors; it contains neither the
canonical finite-ring construction nor the underived origin assertion. The second
reader restricted this new statement to the coefficient hypotheses of its application,
because unrestricted coefficients use an already disputed constructible-pushforward API.
This is a decomposition into strictly separate underived, derived-comparison and formal
transport steps. The formal theorem assumes actual pullback and pushforward comparisons,
not the original theorem under a new name.
The root proof constructs the common family, derives the mate equations, and combines
the constructible-origin and exchange parts.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchange_coefficientRealization.
This is a decomposition, not an axiom-free proof. Three holes are added, each in its own
module with a source, full proof in words, and a node:

- AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_constructible
  (lem-weil-pbc-finite-discrete-constructible-encoding).
- AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_derivedComparisonData
  (lem-weil-pbc-finite-discrete-derived-coefficient-data).
- AlgebraicGeometry.ProEtale.CondensedRing.coefficientComparisonData_exchangeSteps
  (lem-weil-pbc-coefficient-exchange-from-comparisons).

The item module has zero holes. Across the delivered Lean files, three named theorem
holes remain. No sorry is placed in a definition or a private declaration. The net hole
change in this reduction is 1 closed minus 3 added, namely -2, before accounting for
any pruned import closure. Existing upstream holes are not claimed as closed.

The common coefficient equivalence and its underlying-sheaf comparison are proved.
CoefficientPullbackData.toComparisonData is proved using unit_mateEquiv and mateEquiv_counit.
CategoryTheory.Adjunction.threeStepComparison is proved explicitly. These constructions
introduce no holes and choose no arbitrary data from a sorry-backed existence theorem.

Validation: the common encoding, categorical three-step construction, derived comparison
interface, and item module compile. Original consumers ComparisonDirectImage (2.9 s),
FiniteDiscreteExchangeRealization (5.4 s), IntegralFiniteExchangeComparison (10.8 s), and
ProEtale.ConstructibleSheaf (5.1 s) compile unchanged against the modified interfaces.
The canonical coherence module compiles in 51.9 s after deriving its associativity formula
from the existing legacy isomorphism equality and making the component simplification
explicit. All retained public statements have the same mathematical meaning. The
compatibility proof imports also give the local delivery compiler the ordering edges
needed to build the replacement old entry points before their precompiled consumers.
No compiler limit was increased and no theorem was split to bypass a compile limit.
The first dry run compiled the complete sandbox module set and ran their axiom probes without
reporting forbidden axioms. Its three metadata errors (one signature record and two new
consumer table entries) were corrected; the second-reader section remains for the
independent reader, as required by the brief.

Repair validation: rebuilt the canonical and compatibility coherence modules together,
then compiled an unchanged copy of WeilSheaf.StalkCharpoly against them. All three passed.
The legacy isomorphism aliases preserve the consumer's rewrite at line 168; aliases to the
morphism equalities do not. This repair adds or closes no further holes: the item still has
zero holes, with the same three split obligations listed above.

## No longer needed

The existing finiteDiscreteExchangeSteps definition is used directly.
FiniteDiscreteRealizationFunctor has no delivered change. The general categorical
comparison is specialized to the continuous-function coefficient in the formal transport
statement, so no predicate refactor or new coefficient-parametric predicate is needed.

Removed direct proof imports from the item module:
ConstantInternalModuleSheafEquivalence (now used through the constructive encoding module),
and the redundant FiniteDiscreteDerivedCoefficientData import (reexported by the formal
transport interface). Neither of these modules is pruned from the closure. Removed the
unused new finiteDiscreteAmbientSquare abbreviation; coefficientAmbientSquare is the
actual square used by the comparison data.

The external-module route through Sheaf.Paper.FiniteRingConstructibleSheafOrigin and
lem-weil-pbc-finite-ring-constructible-sheaf-origin is not needed by this proof. Its external
SheafOfModules encoding and descent infrastructure are not imported. Instead, use the
existing ordinary module-valued constructible-origin theorem
lem-sf-proetale-constructible-origin. The constructive constant internal-module encoding
remains needed; its node is not pruned. ComparisonDirectImage remains needed for the
canonical right-mate comparison.

The old direct proof dependencies
lem-weil-pbc-constant-internal-module-sheaf-equivalence and
prop-weil-pbc-comparison-direct-image are moved below the common encoding and the
derived comparison obligation, respectively; neither is pruned from the import closure.
Together with the unused external-module origin node named above, this accounts for
all three removed entries of the item's original proof_deps.

The second reader also removed the redundant new public import
WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod from
ConstantInternalModuleSheafEquivalence: ModuleObjects.MapMod already publicly imports it.
The six compatibility modules replace their original direct imports with reexports;
those original dependencies remain publicly available through the canonical modules.
No whole-module pruning or positive net hole reduction is claimed.

Exact direct imports replaced by compatibility reexports (all remain transitively
available; this is not closure pruning):

| Compatibility module | Former direct imports |
| --- | --- |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs | WeilConjectures.Compactification.Defs |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs | Mathlib.CategoryTheory.Adjunction.Additive<br>Mathlib.CategoryTheory.Adjunction.Triple<br>WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence | WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates<br>WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs | Mathlib.Algebra.Homology.ShortComplex.PreservesHomology<br>Mathlib.CategoryTheory.Adjunction.Additive<br>WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension<br>WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify<br>WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale<br>WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso | WeilConjectures.Mathlib.CategoryTheory.Equivalence<br>WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal | WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor<br>WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal |

## Where the brief, the DAG or earlier work was wrong

The initial import routes cannot be combined unchanged: old pro-etale functor files and
the finite-coefficient fork define the same names. The compatibility reexports repair that
interface, preserving the old coherence theorem statements under their original names. The
returned landing correctly identified that the first repair had removed those names from the
canonical module while consumers still referenced them. Restoring aliases there and removing
the now-duplicate aliases from the compatibility re-export fixes that interface without
changing either statement.

An arbitrary independently chosen equivalence on each scheme does not provide the coherent
pullback comparisons required for the square. The proof constructs one common family
instead. The supplied existence hypotheses remain in the original theorem signature.

The existing boundedConstructible_rightDerivedLowerStar_obj declaration is already marked
STATEMENT-DISPUTED for arbitrary condensed coefficients. This delivery does not repair or
use its claimed geometric proof: the named restricted functors in the assigned statement
already depend on it. The finite coefficient assumptions are the appropriate setting for
the desired application. No target statement is changed. 

## Forced adaptations

The returned landing failed in `import_prune_check.py` because
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence` removed
`AlgebraicGeometry.ProEtale.lowerStarComp_assoc` and
`AlgebraicGeometry.ProEtale.lowerStarComp_id_left`, while the unchanged consumers
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence` and
`WeilConjectures.WeilSheaf.StalkCharpoly` still used those names. The canonical finite
coefficient module now adds the aliases
`lowerStarComp_assoc := legacy_lowerStarComp_assoc` and
`lowerStarComp_id_left := legacy_lowerStarComp_id_left`. The compatibility module
had already declared those names and consequently failed with duplicate-declaration errors;
its two alias lines were removed. These are the only forced lines in that adapted module.
The landing checker does not index Lean's `alias` command, so the canonical compatibility
names are explicit public theorem wrappers, each proved by the corresponding legacy theorem.
Its declaration scanner now recognizes both restored names. No statement is reproved.
The exact import-pruning check named in the return passes for the repaired canonical module
(exit 0). The wrappers and compatibility re-export compile without diagnostics.

## New nodes

`def-weil-pbc-common-finite-discrete-encoding`: the explicit common encoding and its
underlying-sheaf comparison; proved, with no existence choice from an unproved theorem.

`lem-weil-pbc-finite-discrete-constructible-encoding`: transport finite local presentations
through that encoding. What remains is the finite-matrix/common-cover argument identifying
the encoded cokernel as a constant finite module on a refinement of each stratum.

`lem-weil-pbc-finite-discrete-derived-coefficient-data`: coherent inverse-image comparisons
for the common encoding, and invertibility of their canonical right mates on bounded-below
inputs for qcqs maps. What remains is the underived scalar-action/restriction construction,
its composition coherence, and the identification of its derived right mate with the
bounded-below direct-image comparison of Bhatt--Scholze Lemma 5.4.3.

`lem-weil-pbc-three-step-adjunction-comparison`: the fully proved abstract categorical
assembly from pullback coherence and the mate unit/counit equations.

`lem-weil-pbc-coefficient-exchange-from-comparisons`: the remaining formal passage from
coherent ambient comparisons to the specified restricted factors and factorizations.
The abstract four-vertex categorical construction is already proved. What remains is its
instantiation and the inclusion/component identifications for the square and the three
named transformations. Experiments prove the unit/counit and composition identifications,
and the unit-step component formulas; they expose repeated reduction of sheaf pullback
and derived-functor constructions during the final matching. These experimental helpers
are not delivered as additional holes or unused declarations.

Change records: coord/changes/H2-common-constant-encoding.md,
coord/changes/H2-proetale-duplicate-exports.md.

## Earlier second reading (a previous round; superseded)

1. **Signatures and visible changes.** Compared every sandbox module with the shared
   version using diff, and checked declaration signatures with the source scanner.
   finiteDiscreteExchange_coefficientRealization retains its exact signature, as does
   constantInternalModuleSheaf_equivalence. The only existing interface changes are
   the two declared change records. Checked the six old pro-etale files against their
   canonical FiniteCoefficient counterparts: Defs adds only overPullbackId, Iso,
   Monoidal and the two LowerShriek files have the same declaration bodies, and
   CoherenceLegacy is the old Coherence with two names changed. The compatibility
   aliases restore precisely those two old iso-equality signatures. The canonical
   morphism-equality lemmas receive distinct names and their internal users are
   adapted. No target statement or mathematical definition changes meaning. Verdict:
   pass with the declared compatibility repair, requiring interface review (CODEX).

2. **Proof, compilation and axioms.** Independently compiled all 15 sandbox modules
   with lcompile.py --all; all passed without diagnostics, including the canonical
   coherence module in 53.6 seconds. Scanned every declaration: exactly the three
   reported public named theorem holes remain, each with proof exactly by sorry;
   no forbidden declaration, hidden proof hole, or sorry in a definition was found.
   Scratch-copy #print axioms checks show only propext, Classical.choice and
   Quot.sound for sheafEncoding, finiteDiscreteCoefficientEquivalence,
   CoefficientPullbackData.toComparisonData, internalModuleAb_equivalence and
   finiteDiscreteCondensedRing_constant. The main theorem includes sorryAx because
   its reported dependencies remain open. Read the explicit sectionwise construction,
   its localization counit/unit argument and its forgetful isomorphism. Its inverse
   uses a proved equivalence, not arbitrary data from an unproved existence theorem.
   Read all three naturality calculations in threeStepComparison and both Mathlib
   mate identities used by toComparisonData. Verdict: valid decomposition, not an
   axiom-free proof of the original target.

3. **Remaining statements and searches.** Read each new node and its complete Lean
   statement. The constructibility obligation only transports local presentations
   through the fixed encoding; it does not assert etale origin. The derived obligation
   supplies individual pullback comparisons, their square coherence, and invertibility
   of right mates for qcqs maps on D+ inputs; it does not assert exchange. The formal
   obligation assumes those comparisons for arbitrary functors over finite discrete
   ell-torsion coefficients, and only transports
   their three factors to the already specified restricted exchange. Thus none is
   a renamed copy of the original existential theorem. Checked the zero ring, zero
   modules, empty schemes and empty strata: finite cokernels and refinements admit
   these cases; no nonzero coefficient or positive rank is used. Checked identity
   morphisms and non-Cartesian squares in the formal argument: it requires only
   coherence and the mate equations, not exchange invertibility. Finite type over a
   field supplies the qcqs hypotheses for f and f-prime. Read Bhatt--Scholze 5.4.1
   and 5.4.3 in the local PDF (page 39), including the bounded-below limitation in
   Remark 5.4.4, and checked the local constructible-origin and finite-presentation
   definitions. Tag 09AK assumes a Noetherian coefficient ring, as ensured here by
   finiteness of B. Fresh leanfinder search for finite presentation under module-sheaf
   equivalences found external SheafOfModules and condensed constant-module APIs;
   loogle on mateEquiv with comp found mateEquiv_vcomp and mateEquiv_hcomp; grep
   found the restriction unit/counit formulas. Local rg found the existing ordinary
   constructible-origin theorem and the generic exists_mem_forall_exists_linearMap
   in ConstantSheafSections (also listed in the cited node's lean.others), which
   applies to pro-etale sites as well as etale sites. None closes the coefficient
   transport obligations directly. The prior scratch proofs establish some restriction
   identities but leave the final factor matching unfinished; no additional hole or
   unneeded experimental helper was added. Found one overgeneralization: the formal obligation originally admitted arbitrary
   coefficients, despite the known failure of constructible pushforward for those
   coefficients. Restricted this new statement to [DiscreteTopology B], [Finite B]
   and hB : (ell : B) = 0, passed hB from the unchanged root statement, and updated
   its node and proof description. No extra hole was introduced. Verdict: true,
   separate remaining tasks with sources, proof descriptions and matching nodes.

4. **Route, imports and pruning.** The root constructs its common family, applies
   the ordinary pro-etale origin theorem to the encoded sheaf, maps its isomorphism
   through E and its counit, then applies the two comparison interfaces. This uses
   the existing ordinary origin theorem instead of rebuilding external-module
   descent. Inspected sk-thm-properbasechange.realized: none of its statement/step
   nodes is bypassed or changed. The old encoding and direct-image dependencies
   remain below the new interfaces; only the unused external-module origin route
   is removed from the proof plan. Removed one redundant import, described under
   No longer needed. Other public imports supply statement or definition data;
   proof imports are plain imports. Verdict: route preserved and pruning report
   complete; one original hole closed, three added, net -2 before closure pruning.

5. **DAG agreement.** Checked the seven direct proof dependencies of the item
   against its three proof blocks, the dependency unions in all five new nodes,
   their sources, origins, creation and blueprint records, and their Lean records,
   updating the formal transport node to its corrected coefficient scope.
   The new definition node records the actual common encoding; the categorical
   comparison node is fully proved; three separate nodes record the remaining
   holes. Existing item statement metadata is unchanged. Added the independent
   searches to the new nodes' search records. Verdict: metadata follows the code.

Changes by the second reader: restricted the new formal transport theorem to finite
discrete ell-torsion coefficients and passed hB from the root proof; removed the
redundant Monoidal.Mod import and synchronized its change record; corrected the
report's coefficient scope and dependency/pruning accounting; added independent search
evidence and this review. No existing Lean signature, definition body or hole count
changed. The newly added theorem's narrower scope matches exactly its application.

## Second reading by H2

This is the independent reading of the repaired delivery, after the earlier round
recorded above. I read the current sandbox and compared it with the shared sources.

1. **Visible statements and definitions — pass.** Diffed every existing delivered
   module. The assigned theorem's signature and the public
   constantInternalModuleSheaf_equivalence signature are byte-for-byte unchanged.
   The helper exposure and the seven compatibility/interface edits are declared in
   the two change records. Compared the old functor files with the canonical
   FiniteCoefficient implementations: their defining data agree; the old two
   coherence names denoted iso equalities, and the restored wrappers have those
   original types. The canonical hom equalities have separate coefficient_ names.
   These declared interface repairs do not weaken any mathematical statement.
   No target statement is edited.

2. **Proofs, compile and axioms — pass as a decomposition.** Independently ran
   lcompile.py --all on all 15 sandbox files: all compiled without diagnostics;
   canonical Coherence took 44.2 seconds. Independently compiled an unchanged copy
   of WeilSheaf.StalkCharpoly against the sandbox overlay: it passed in 52.4 seconds.
   Scanned the sources: exactly the three public named theorem holes reported under
   Proved and sorry left remain, with no forbidden declaration or definition hole.
   Fresh scratch #print axioms checks show only propext, Classical.choice and
   Quot.sound for sheafEncoding, finiteDiscreteCoefficientEquivalence, its forgetful
   comparison, CoefficientPullbackData.toComparisonData, threeStepComparison,
   internalModuleAb_equivalence and finiteDiscreteCondensedRing_constant. The root
   theorem also has sorryAx, as expected from its open dependencies. Read the
   sectionwise action construction, localization argument, both mate calculations
   and all three naturality calculations. The encoding inverse comes from a proved
   equivalence; no definition chooses arbitrary data from an unproved existence.

3. **Split statements and shortest routes — pass.** Read the three full statements,
   their proof docstrings and nodes. Constructibility transports finite local
   presentations through a fixed equivalence; derivedComparisonData supplies
   coherent individual inverse-image comparisons and invertible qcqs right mates;
   exchangeSteps assumes this comparison data and transports its factors to the
   restricted exchange. None merely renames the original existential conclusion.
   Checked zero coefficients/modules, zero presentation ranks, empty schemes and
   strata, identities and non-Cartesian commutative squares. No extra nonzero,
   properness, or Cartesian assumption is needed. Read the local paper's 5.3.2,
   5.4.1, 5.4.3 and bounded-below limitation 5.4.4, and the actual finite-presentation
   and constructibility definitions. Fresh leanfinder, loogle and Mathlib grep
   searches, followed by rg in both library roots, found constant condensed-module
   APIs and the already used mate/restriction formulas, with no theorem closing a
   remaining obligation directly. The residual scalar-action and restricted-factor
   identifications need substantial implementation; no additional split is made.

4. **Imports, pruning and unit route — pass.** Read the root proof from its common
   encoding through ordinary constructible origin to the mate and formal interfaces.
   Public imports support statement/definition data; the additional proof imports
   are plain imports. Compatibility imports retain the required local ordering
   edges for precompiled consumers. Checked sk-thm-properbasechange.realized:
   its statement and three step nodes are retained. The old direct dependencies
   are completely accounted for under No longer needed: constant encoding and
   direct image move below the new interfaces, while the external-module origin
   route is unused. No whole-module pruning or positive net progress is claimed.
   One original hole is closed and three are added: this is net -2 decomposition.

5. **Lean/DAG agreement — pass.** Checked all six delivered node records against
   their declarations (matching statement text modulo scanner whitespace), their
   dependency files, and the union of uses in each proof plan. Checked the new
   nodes' source, origin, creation and blueprint records. The main node follows
   its three actual proof blocks; the two proved construction nodes and three
   remaining theorem nodes have the correct roles. The restricted coefficient
   hypotheses in the formal node agree with its Lean statement and application.

Changes in this reading: appended this current review and recorded the fresh search
results on the three new obligation nodes. No Lean proof or signature required a
further repair, and no additional hole was closed or introduced in this reading.
