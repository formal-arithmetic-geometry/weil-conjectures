## What changed

The second reader rejected the first worker's reduction: the added
`finiteDiscreteCoefficient_pullbackData` was definitionally the whole target.
It and its undelivered node were removed. The original target statement is unchanged.

The replacement separates two independent geometric assertions, in their own modules:
`finiteDiscreteCoefficient_coherentPullbacks` provides the inverse-image family and its
square equation; `finiteDiscreteCoefficient_directImage_origin` asserts only that qcqs
internal derived direct image preserves the etale realization image. The target combines
them using the proved categorical theorem
`isIso_mateEquiv_of_fullyFaithful_of_essImage`. The proof derives full faithfulness from
the existing comparison Hom-bijection and the coefficient equivalence. It does not
choose data for any definition from an unproved existence statement.

The four existing cached derived-functor definitions were moved verbatim to
`Sheaf.Paper.CoefficientDerivedFunctorAPI` and publicly re-exported by the item. This lets
the independent geometric modules use their generic instance caches without importing
the target or repeatedly elaborating raw concrete derived functors. Every old declaration
keeps its exact signature, name, visibility, attributes and definition body.
The API also declares `CoefficientCoherentPullbackData` and
`FiniteDiscreteCoherentPullbacks`: real record types containing just the pullback
and square fields, with no right-mate assertion and no chosen data.
Change record: `coord/changes/E1-coefficient-derived-api-relocation.md`.

The coefficient interfaces share the named local instance
`coefficientProfiniteEssentiallySmall`. Independent anonymous smallness instances
caused repeated unfolding of the derived category construction; sharing the same
proof instance makes the reduction compile without changing its mathematical data.

The four unchanged repository copies in the original sandbox were omitted from the delivery.

## Proved and sorry left

Upper hole closed:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_derivedComparisonData`.

Holes added, both public named theorems with source, proof docstring and matching node:

- `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_coherentPullbacks`
  (`lem-weil-pbc-finite-discrete-coherent-pullbacks`).
- `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_directImage_origin`
  (`lem-weil-pbc-finite-discrete-direct-image-origin`).

The new categorical theorem
`CategoryTheory.isIso_mateEquiv_of_fullyFaithful_of_essImage` is proved without any sorry.
The four moved API definitions have their original constructed bodies and no sorry.
The item has no remaining direct sorry. This is a decomposition: one upper hole closed,
two strictly smaller geometric holes added, hence local net -1. It is not a completed
geometric proof or a claim of net progress in the ledger. Existing upstream comparison
injective-acyclicity holes remain dependencies of the Hom-bijection/fullness argument.
Global closure counts and pruning remain the maintainer's pinned-ledger calculation.

## No longer needed

Removed direct compatibility imports:
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal`,
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence`, and
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs`.
The direct `Sheaf.AlgebraicGeometry.ComparisonDirectImage` import moved from the item to
the direct-image-origin module, where it is the stated proof dependency.

No original proof-dependency node is pruned: common coefficient encoding and finite
coefficient direct-image comparison are retained below the respective geometric nodes.
No module is claimed pruned from the target closure. The rejected restatement theorem
and its new, unlanded node `lem-weil-pbc-finite-discrete-derived-pullback-data` are omitted.

## Where the brief, the DAG or earlier work was wrong

The initial report called `CoefficientPullbackData` a strictly smaller intermediate
than `FiniteDiscreteCoefficientComparisonData`. The latter is an abbreviation of the
former, so that was an equivalent restatement, despite its different spelling and the
`obtain`/repacking proof. Compilation did not make that a valid reduction.

The replacement mate proof uses preservation of the essential image and full
faithfulness. It therefore does not need to identify each chosen pullback's right mate
with the particular ordinary finite-coefficient comparison map. The generic Yoneda
argument proves invertibility for any such left comparison once both right-adjoint
objects are in the image. The qcqs bounded-below comparison is still required to prove
the direct-image-origin statement; no unit route is bypassed.

## New nodes

`lem-weil-pbc-finite-discrete-coherent-pullbacks`: only coherent derived inverse images,
without a right-mate or direct-image assertion. Its docstring explains scalar naturality
from the common G and the one point-ring isomorphism, then exact derivation.

`lem-weil-pbc-finite-discrete-direct-image-origin`: only essential-image membership of
the qcqs internal direct image of a bounded-below realized complex. The concrete
witness in its proof in words is R+ h_et,* K, using the finite-coefficient direct-image
comparison and the sectionwise coefficient transport.

`lem-weil-pbc-fully-faithful-mate-image`: proved categorical Hom/Yoneda criterion. It
uses objectwise image membership; it assumes neither essential surjectivity of the
embedding nor an already specified invertible right comparison.

`def-weil-pbc-coefficient-derived-functor-api`: records the four unchanged cached
wrappers relocated into a shared module, plus the smaller pullback-and-square
record and its finite-discrete abbreviation. No duplicate functor construction
is introduced. The relocation record is
`coord/changes/E1-coefficient-derived-api-relocation.md`.

## Second reading by E1

1. Compared all five original sandbox modules against the repository. Four are identical
   and were omitted from the delivery.
   Parsed and compared each old declaration's literal signature against the delivered
   item plus relocated API: all nine existing named declarations match byte for byte.
   All four moved definition bodies and attributes also match. Their re-export and all
   ten transitive users are documented in the relocation change record. No target
   statement or definition body changed.
2. The original files compiled, but their reduction was mathematically vacuous. Replaced
   it by the genuine reduction above. The categorical lemma compiles without sorry.
   Final delivered-set compilation and axiom verification are recorded below.
3. Removed the equivalent whole-item split. The two replacement statements are proper
   parts of the argument. Read Bhatt--Scholze Corollary 5.1.6 and section 5.4 in the local
   PDF, including the warning that direct-image comparison fails for unbounded complexes.
   Checked empty schemes, the zero ring, identity morphisms and arbitrary CommSq:
   inverse-image coherence needs no Cartesian hypothesis, and the direct-image claim
   retains qcqs and D+. Independent LeanSearch, LeanFinder, Loogle and Mathlib/source rg
   searches found no matching concrete encoding results. Existing generic restriction,
   Yoneda and ordinary site comparison APIs were inspected and reused.
4. Retained the existing common encoding and direct-image route through the new nodes;
   checked `dag/units/sk-thm-properbasechange.json` and its blueprint section. No unit's
   statement, realized nodes or proof steps change. The categorical argument removes
   the stronger task of identifying the specific right mate; compatibility imports are
   removed and all original proof dependencies remain transitively needed.
5. Rewrote the item's proof steps and proof_deps to match full faithfulness, coherent
   inverse images, preservation of etale origin and the proved mate criterion. Each new
   node has its complete source/proof/search/created/blueprint/Lean record and the item's
   chapter and unit. No maintainer-owned fields or unit records are changed.

Changes by the second reader: removed the invalid restatement; added the two independent
geometric obligations and proved the mate criterion; relocated the cached API verbatim;
shared the coefficient smallness instance; repaired the DAG and this report. This delivery is explicitly a decomposition.

Final verification: `lcompile.py --all` compiled all five delivered modules without
errors or warnings (the item took 18.5 seconds). Literal signature comparison found
all nine existing named declarations unchanged. The only direct sorry terms in the
delivered source are the two named geometric obligations listed above. No forbidden
declaration or implementation escape is present.

Axiom probes: the categorical mate theorem uses exactly `propext`,
`Classical.choice`, `Quot.sound`. The item theorem uses those plus `sorryAx`,
as expected from the two open geometric statements and existing upstream holes.
The unchanged direct importer `Sheaf.Paper.CoefficientExchangeFromComparisons`
compiled against the delivered overlay without adaptation (9.0 seconds).

The private full-faithfulness helper chooses only inverse images of morphisms under
a faithful functor: those inverse images are unique by the proved Hom-injectivity.
It introduces no arbitrary object or unproved data construction.

`deliver3.py E1 Sheaf.Paper.FiniteDiscreteDerivedCoefficientData --no-push`
printed OK: the delivered set compiles and passes preflight. Review class CODEX,
for the new nodes/modules, API relocation and shared local proof instance.
