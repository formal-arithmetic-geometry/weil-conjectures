## What changed

Proved `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule`
with its signature unchanged. For each point the proof constructs an integral stalk test,
factors it through a finite pushforward, and proves directly that its stalk map remains
injective. Classical choice assembles these finite data into a family indexed by the points
of X. Module-valued finite selection supplies a finite subfamily, whose biproduct lift is
the required monomorphism. No source-library embedding theorem is applied.

Added four modules, with non-public proof imports from the assigned module:

- `ConstructibleModuleIntegralStalkEmbedding`: the normalization/adjunction argument at one point.
- `IntegralConstantModulePushforwardColimit`: the filtered presentation of an integral constant
  pushforward, independent of the constructible source sheaf.
- `ConstructibleModuleIntegralMapFactorization`: a proved categorical factorization theorem.
  It converts the corrected finite-value constructibility data to the source-library predicate
  using `finite_locally_constant_module_values_iff` and `of_noetherianSpace`, applies
  `isFinitelyPresentable_of_isConstructibleSheaf`, and then uses Mathlib's
  `IsFinitelyPresentable.exists_hom_of_isColimit`. Two inverse isomorphisms cancel to establish
  the factorization equality.
- `ConstructibleModuleFiniteSelection`: the module-valued counterpart of the abelian
  finite-selection statement, allowing arbitrary target sheaves and any index universe.

Updated the assigned node's proof, proof dependencies and proof origin to match the Lean
reduction. Added matching nodes for all four new declarations. All five modules compile locally
in import order with no warnings. The existing public imports and all existing signatures
are unchanged. New module imports were narrowed to statement needs; no unused proof imports
remain. The unit's route is unchanged.

## Proved and sorry left

Proved the one original sorry:
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule`
(`lem-weil-pbc-constructible-module-finite-pushforward-noetherian`).

Also proved
`AlgebraicGeometry.Etale.exists_finite_lowerStar_factorization`
(`lem-weil-pbc-constructible-module-integral-map-factorization`).

The assigned module contains no sorry. Three new named public theorems remain sorry:

- `AlgebraicGeometry.Etale.exists_integral_lowerStar_stalk_injective`
  (`lem-weil-pbc-constructible-module-integral-stalk-embedding`).
- `AlgebraicGeometry.Etale.exists_filtered_colimit_finite_lowerStar_constant`
  (`lem-weil-pbc-integral-constant-module-pushforward-colimit`).
- `AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_module_stalk_injective`
  (`lem-weil-pbc-constructible-module-finite-selection`).

Each is strictly part of the original proof: a map need only be injective above one point;
the colimit statement has no constructible source or embedding conclusion; finite selection
has arbitrary target sheaves and assumes stalk tests already exist. Their full source proofs
are in the docstrings and nodes. The proved factorization also uses the existing sorries
`finite_locally_constant_module_values_iff` and
`isFinitelyPresentable_of_isConstructibleSheaf`, which remain with their existing items.

Edge cases checked against the statements: an empty X has no pointwise obligations and may
use n=0; a zero source admits the empty subfamily; M=0 and the zero coefficient ring are
allowed in the filtered presentation and factorization; an empty test index L can satisfy
stalk detection only when the source has zero stalks. The finite module values M are
unchanged throughout factorization and selection.

## No longer needed

No original imports removed. The second reader removed the redundant public import
`Mathlib.CategoryTheory.Presentable.Finite` from the new colimit module. No existing planned geometric or colimit argument is pruned:
it is retained in the new obligations' proof dependencies. The source module
`WeilConjectures.ConstructibleSheaf.FinitePushforward` remains necessary for its biproduct
instance and finite-presentability theorem; its existing Noetherian embedding declaration
is not used as a black box.

The dependency `def-weil-pbc-constructible-torsion` and its module
`Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf` are unnecessary for this argument.
Its curve-specific coefficient-pair predicate does not supply the underlying abelian
constructibility of a module sheaf on an arbitrary X. The module-valued selection obligation
now records the required forgetting comparison directly. Nothing else is newly pruned.

## Where the brief, the DAG or earlier work was wrong

The plan's finite-selection declaration is abelian-valued and does not apply directly to
ModuleCat sheaves or the corrected finite-value module predicate. The module-valued
comparison and finite selection have therefore been isolated as their own obligation.

The plan's finite-presentability declaration likewise expects the source constructibility
class. Its conversion from the corrected predicate is implemented, using the existing
finite-value equivalence on each stratum. Thus no assumption on constructible strata was
removed and no target signature changed.

The required LeanSearch calls returned Internal Server Error; LeanFinder, Loogle and
Mathlib grep were run and recorded separately.

The Stacks source file is absent from this machine's literature directory. Read the official
source at https://stacks.math.columbia.edu/tag/09Z6, which gives the pointwise normalization,
finite-stage factorization and partition alternative used here. The existing node's warning
about its ACC inference is retained; the new selection statement follows the partition
alternative, not an assertion of a descending chain condition.

## New nodes

`lem-weil-pbc-constructible-module-integral-stalk-embedding` is the first four steps of
09Z6: generic trivialization, normalization, adjunction and injectivity above x. Its new
module is `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding`.

`lem-weil-pbc-integral-constant-module-pushforward-colimit` isolates finite approximation
and the module-valued degree-zero relative-colimit argument. Its module is
`Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit`.

`lem-weil-pbc-constructible-module-integral-map-factorization` is proved from that colimit
presentation, the finite-value equivalence, finite presentability and Mathlib's factorization
lemma. Its module is `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization`.

`lem-weil-pbc-constructible-module-finite-selection` provides module-valued finite selection
by forgetting to the existing abelian lemma and reflecting the resulting mono. Its module
is `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelection`.

No change records: no existing definition or statement changed.

## Second reading by U1

1. Compared the assigned module with the repository using `diff -u`: the only existing
   declaration has its signature and docstring byte for byte unchanged. Its three new
   imports are non-public. There are no definition changes, adapted modules or change
   records. The existing node differs only in proof, proof_deps and proof_origin. Verdict:
   no accidental interface change.
2. Compiled all five delivered modules in import order through lcompile.py, with no
   errors or warnings. Inspected every declaration and searched the files for forbidden
   constructs: the only remaining sorries are the three reported public theorems, with
   no definition or anonymous sorry. A scratch copy with explicit proof imports and
   `#print axioms` for all five theorems compiled; each lists only propext, Classical.choice,
   Quot.sound and sorryAx. Thus the two proofs are genuine reductions, still conditional
   on the listed open obligations and existing open dependencies, not axiom-free closures.
3. Read Stacks https://stacks.math.columbia.edu/tag/09Z6 and the abelian selection and
   generic-kernel modules. The integral detector retains Noetherian X, finite Lambda and
   finite-value constructibility, and requires injectivity only over the chosen x. The
   finite separable extension embeds into each algebraically closed geometric field over x;
   the adjunction square gives an injective composite. The colimit statement has no source
   F and no embedding conclusion: finite approximation plus the degree-zero relative
   colimit supplies its filtered cocone. The factorization uses the actual finite-value
   equivalence on each stratum, finite presentability, and cancellation of e.hom/e.inv.
   Selection allows arbitrary targets: a kernel inside a lisse source with zero generic
   stalk is zero by LisseGenericKernel, so target constructibility is unnecessary. The
   empty scheme, zero source, zero ring/module and empty index cases introduce no false
   obligations. The new obligations are distinct proper steps, not restatements of the
   embedding. Independent LeanFinder and Mathlib grep queries used generic-stalk and
   integral-colimit wording; rg of lean/ and the upstream constructible-sheaf files found
   the abelian selection interface and the existing open embedding, neither an exact
   proved replacement for these module-valued statements. Verdict: valid split; no quick
   closure found without additional comparison theorems.
4. The Lean argument directly proves injectivity of psi from psi followed by kappa = phi,
   then assembles pointwise tests and applies finite selection. No source embedding is
   used to rename the whole goal. Public imports of the original module are preserved;
   proof-only additions are private. Removed the redundant Presentable.Finite import from
   the new colimit module and recompiled it successfully. Compared all old proof_deps
   against the union of the new reduction and its four helper nodes: the sole absent node
   is def-weil-pbc-constructible-torsion, already listed under No longer needed. All other
   old dependencies move into the helpers and remain required. Read sk-thm-p1.json realized:
   this item is below its realized statement/steps, and the same normalization, finite
   approximation, finite presentability and partition route is retained. Verdict: pruning
   complete and unit route preserved.
5. Opened all five node files. Each helper's lean.statement matches its declaration;
   chapter/unit, source, creation, search and Lean records are present. Each proof_deps
   equals the union of the steps' uses. The assigned node records the actual detector,
   factorization, stalk functor, selection and reindexing operations; the factorization
   node records both finite-value conversion and colimit factorization. The open nodes
   have sourced full docstring proofs. Verdict: DAG and Lean agree.

Second-reading changes: removed one redundant public Mathlib import from
IntegralConstantModulePushforwardColimit; clarified the pruning record and recorded this
independent review. No mathematical statement, definition or proof was rewritten.
