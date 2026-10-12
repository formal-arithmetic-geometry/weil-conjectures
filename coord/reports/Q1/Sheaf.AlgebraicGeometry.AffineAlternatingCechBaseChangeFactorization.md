## What changed

Replaced the earlier attempted restatement with a real two-step decomposition of
AlgebraicGeometry.affineAlternatingCech_baseChange_factorization. Its signature and
visibility are unchanged. The proof obtains the fixed-counit Čech calculation, constructs
its comparison c₀, compares c₀ with the supplied comparison c, and replaces the target
isomorphism t by its composite with the derived direct image of the target-module
automorphism. Functoriality and associativity prove the requested equation.

Two new modules contain the two remaining public statements, each with its source and
complete proof in words: AffineAlternatingCechPinnedMate and
ModulePullbackComparisonTargetAutomorphism. No definition, existing statement or other
module's interface was changed. The existing node's proof and proof_deps now follow the
Lean combination. No arbitrary object is constructed from an unproved existence theorem:
the proof only eliminates propositions and uses the already fixed counit family defining
the canonical mate. Its ordinary tensor-pullback functor is the actual constructed functor.

The earlier sandbox copy of AffineAlternatingCechModel was unchanged and is excluded from
the delivery. The rejected factorization_core and the unrelated cech_data placeholder
were discarded; neither is a declaration of the repository.

## Proved and sorry left

Closed one original hole:
AlgebraicGeometry.affineAlternatingCech_baseChange_factorization
(node lem-pc-affine-alternating-cech-base-change-factorization).
The item's module has no sorry left.

Added two holes, a decomposition rather than a completed proof of the geometric result:

- AlgebraicGeometry.affineAlternatingCech_pinned_mate
  (node lem-pc-affine-alternating-cech-pinned-mate).
  This is only Steps 1--3: the calculation for the specific counit family used in the
  definition of the canonical derived mate. It does not accept an arbitrary comparison.
- AlgebraicGeometry.modulePullbackComparison_target_automorphism
  (node lem-pc-module-pullback-comparison-target-automorphism).
  This is only Step 4: comparing two derived-to-ordinary maps on one module. Its
  statement has no base-change square, cover, Čech complex, or derived direct image.

The main proof combines the two statements in Lean, including the equation obtained by
postcomposing the target isomorphism. The hole count is 1 closed, 2 added, net -1; this is
not claimed as net sorry elimination. Every remaining hole is an entire public theorem
proof in its own new module.

Edge cases checked in the arguments: r = 0 forces X empty and yields zero complexes;
r = 1 reduces to the ordinary affine section formula; a zero module yields zero objects;
nonflat G is allowed (the intermediate counit need not be invertible); the target
comparison lemma concerns arbitrary modules, not just quasi-coherent ones.

## No longer needed

Removed from the item's direct proof imports:
Sheaf.AlgebraicGeometry.CechResolution and
Sheaf.AlgebraicGeometry.ModulePullbackAffineSections.
Their roles move to the new fixed-counit Čech lemma, whose planned proof still needs them.
Thus no existing node or module is claimed to leave the full target import closure.
All original public statement imports remain. The rejected factorization_core and
cech_data declarations are absent from the delivery.

The complete difference from the old direct proof_deps is:
def-pc-affine-alternating-cech-model, def-pc-derived-base-change-map,
def-pc-derived-pullback, lem-pc-cech-resolution, and
lem-weil-pbc-module-pullback-affine-sections. The first three remain in stmt_deps
and in the statement's public imports; they are not pruned from the library.
The last two move to the pinned-mate node's proof_deps. No module is pruned from
the targets' full import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier factorization_core duplicated the original theorem's hypotheses and
conclusion, and the earlier main proof was one application of it. The cech_data hole
was unused. This did not decompose the argument. Both are replaced by the two strictly
separate stages above and a real composition proof. No attempt was made to bypass the
restatement check.

The old report described a missing published AffineAlternatingCechModel object file;
that file is now present and the delivery compiles against it. No repository dependency
was modified to repair the baseline.

CechResolution computes the all-tuples complex. Its current signature does not identify
the explicit increasing-tuple model, so the new fixed-counit lemma explicitly includes
constructing the alternating resolution and proving its local contraction. Likewise,
baseChangeMap_cech omits the Čech comparison equation; its literal statement cannot close
this theorem. No redundant import of BaseChangeMapCech was added.

The delivery scanner splits a theorem signature at the first local let assignment,
so the fixed-counit theorem is written with its counit and comparison expressions
expanded rather than using local let binders. This preserves its mathematical content
and lets the scanner recognize its single whole-proof sorry.

The fixed family of counits in the new lemma is precisely the family selected by
exists_derivedPullbackComposition and used in schemeDerivedBaseChangeMap. It is not an
arbitrary compatible family. Local additive instance choices are propositions and hence
agree by proof irrelevance. The ordinary g-pullback functor is explicitly typed over the
shared SheafOfModules categories to avoid selecting Scheme.Modules' distinct Category
instances.

Searches were run with msearch.py and recorded in searches.jsonl. LeanFinder returned
cotangent-complex base-change results for the geometric query, and ordinary pullback
counit identities for the automorphism query; neither is an exact match. Loogle found
Functor.leftDerivedUnique, which compares derived counits but does not alone give the
ordinary target automorphism. Mathlib grep found no exact result; local rg confirmed
the limitations of CechResolution and BaseChangeMapCech. LeanSearch returned an internal
server error and is recorded as unavailable, not as absence of a theorem.

The blueprint source and Stacks checkout are absent locally. The referenced
[Stacks 02KH](https://stacks.math.columbia.edu/tag/02KH),
[08HY](https://stacks.math.columbia.edu/tag/08HY),
[06YJ](https://stacks.math.columbia.edu/tag/06YJ), and
[0A1D](https://stacks.math.columbia.edu/tag/0A1D) were read online.
02KH supplies the termwise Čech tensor calculation before flatness is used to take
cohomology; 08HY defines the derived mate; 06YJ supplies the K-flat model of derived
pullback. 0A1D is a relative-flat derived base-change theorem, not the explicit Čech
identification. The counit-independence truncation argument is written by Q1 following
Step 4 of the item's node, and is marked as agent-written in the new node.
WANTED: the local blueprint document named in the original node, Steps 2--5, for both
new nodes. No literature or repository file was written outside the sandbox.

The blueprint ancestor script returns None because the existing created.item chain
uses module names rather than node ids. The new nodes retain the explicit ancestor
lem-pc-rf-base-change-flat-module already recorded in the parent's blueprint.from, and
add the parent to its via chain. Searches across the imported blueprint for counit and
alternating found no duplicate of either new statement. The unit's realized statement
and steps are untouched; this is a decomposition below that level.

## New nodes

lem-pc-affine-alternating-cech-pinned-mate:
lean/Sheaf/AlgebraicGeometry/AffineAlternatingCechPinnedMate.lean.
It isolates the fixed-counit increasing-tuple Čech calculation (Steps 1--3), leaving out
the comparison-independence step. Its source is the parent's affine Čech calculation,
with Stacks 02KH and 08HY, and its docstring spells out the construction and mate equation.

lem-pc-module-pullback-comparison-target-automorphism:
lean/Sheaf/AlgebraicGeometry/ModulePullbackComparisonTargetAutomorphism.lean.
It isolates the degree-zero truncation argument (Step 4), independently of the geometry
of the cover. The docstring explains right Kan extension uniqueness, nonpositivity,
H⁰ of ordinary pullback, truncation orthogonality, and reconstruction of the automorphism.

Both nodes are in sec-picard-framework and inherit sk-thm-picard-f-representable from
the item's node. No change record is necessary: no existing signature, definition or
public import changed.

## Second reading by Q1

1. **Interfaces — pass.** Diffed every delivered existing module against the
repository. The main theorem's signature is byte-for-byte identical; its docstring,
visibility, definitions and public imports are unchanged. The only other Lean
modules are the two genuinely new theorem modules. The existing node changes only
proof, proof_deps and proof_origin. No change record is required.

2. **Lean proof and axioms — pass as a decomposition.** Compiled all three modules
in import order with lcompile.py: 17.2 s, 4.0 s and 24.9 s, without errors or
warnings. The main proof checks the comparison equation by functoriality and
postcomposes t with the derived image of alpha[0]. Source inspection found exactly
the two reported whole-theorem sorries, no definitions containing holes and no
forbidden declarations or attributes. A scratch module printed axioms for all
three declarations: only propext, Classical.choice, Quot.sound and sorryAx.
The latter remains because the two split-off statements are not proved; this is
not a completed geometric proof. The ordinary pullback functor is constructed,
and no new definition chooses an arbitrary witness from an existence hole.

3. **Split statements — pass.** Read both complete docstring arguments and their
nodes. The pinned-mate statement fixes the same counit family used by the actual
schemeDerivedBaseChangeMap definition; exists_schemeDerivedAdjunction pins its
Hom equivalence to that family. It isolates Steps 1--3, with no arbitrary caller
comparison. The automorphism statement isolates Step 4 and has no square, cover,
Cech model or direct image. Its truncation argument has the correct direction:
for E in degrees at most zero, both tau_le_minus_one(E) and its cochain shift by
one have no maps to a single module in degree zero. The two H0 comparisons are
invertible even when the comparisons themselves are not. Checked the empty
cover, one-member cover, zero module and nonflat module cases in these arguments;
these are mathematical checks, not additional formal proofs. Neither statement
merely renames the original theorem.

Independent searches used different queries: Loogle singleFunctor/homologyFunctor,
LeanFinder morphisms from nonpositive objects to the heart, Mathlib grep for
counit/homology and Cech/tensor, and local rg over both library roots. Loogle found
singleFunctorCompHomologyFunctorIso; LeanFinder found orthogonality and fractions
lemmas. Upstream homologyFunctor_map_bijective_of_isLE_of_isGE supplies the
truncation factorization ingredient, but does not establish nonpositivity and the
H0 counit isomorphism for tensor pullback. DerivedPullbackSingleCohomology and
FlatModuleCanonicalDerivedPullback require flatness and do not cover the arbitrary
module here. No exact replacement was found, and neither remaining hole can be
closed by a short application of these results. Re-read Stacks 02KH, 08HY and
06YJ: the termwise Cech tensor identification precedes the use of flatness on
cohomology, and the derived mate and K-flat models match the stated arguments.

4. **Route and pruning — pass, report repaired.** The proof genuinely combines
two strictly separate stages. Public imports supply the unchanged statement;
private imports supply the two proof lemmas. The new pinned-mate module retains
the two original geometric proof imports for its pending calculation. Expanded
No longer needed to enumerate every old proof_dep omitted from the new direct
list and distinguish direct dependency changes from pruning the full closure.
No full-closure module is pruned. The unit sk-thm-picard-f-representable has empty
realized lists in this checkout; these remain untouched. This delivery changes
only a decomposition below the unit, retaining its geometric route.

5. **DAG — pass.** Checked the new nodes' required fields, sources, blueprint
ancestry, chapter/unit, creation records and search records. Their lean.statement
strings exactly match their Lean signatures. Their proof_deps equal the unions
of uses in their proof steps. The existing node describes precisely the fixed
comparison construction, target automorphism and final composition written in
Lean. The counts remain one original hole closed and two new holes added, net -1.

Second reading changed only this report: completed the old-dependency accounting
and recorded the independent review and search findings. The Lean proofs and
statements required no repair.
