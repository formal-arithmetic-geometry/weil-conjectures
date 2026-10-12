## What changed

Proved AlgebraicGeometry.Etale.exists_constantModule_limit_fiber_rep with its exact
signature unchanged. Its proof represents a fiber element on an etale object, uses
Mathlib affine-etale cover density and the point covering property to refine through
an affine object, applies affine section descent, and closes the equality using
Point.toPresheafFiber_naturality_apply and Point.toPresheafFiber_w_apply.

Added ConstantModuleLimitAffineSectionDescent, whose theorem is proved: explicitly
construct the base-changed scheme diagram and cone; prove its limit using
isLimitOfIsPullbackOfIsConnected; establish compactness, quasi-separatedness and
affine transitions; apply existing globalSections_limit_comparison; transfer its
representative through additive section comparisons. This avoids a derived
higher-direct-image diagram and the degree-zero derived-to-underived bridge.

Added ConstantModulePullbackSectionComparison, isolating the still-unproved
coefficient and section comparison for a SINGLE cartesian square. It contains no
limit, cofiltered category, stage representative or germ assertion. Its source,
full proof plan and existing inputs are recorded in its docstring and node.
All data definitions are actual constructions; equivalences are obtained locally
in theorem proofs and never used to define an arbitrary object from existence.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.Etale.exists_constantModule_limit_fiber_rep
(lem-weil-pbc-constant-module-limit-fiber-descent).

Also proved the new theorem
AlgebraicGeometry.Etale.exists_constantModule_limit_affine_section_rep
(lem-weil-pbc-constant-module-limit-affine-section-descent).

Added exactly one hole, and it is the only sorry in the three delivered modules:
AlgebraicGeometry.Etale.exists_constantModule_pullback_section_comparison
(lem-weil-pbc-constant-module-pullback-section-comparison).
Its proof is exactly `by sorry`. Thus this is a decomposition, with one original
hole closed and one strictly smaller independent comparison hole added, net zero.
No claim of an axiom-free target proof is made while that comparison and existing
continuity dependencies remain open. All three modules compile without warnings.

## No longer needed

Removed from the original module:
- Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem;
- Mathlib.CategoryTheory.Presentable.Directed;
- Mathlib.CategoryTheory.Limits.Connected;
- WeilConjectures.ConstructibleSheaf.Defs (redundant direct proof import);
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs (redundant direct proof import).

Its old proof dependencies sbc-lem-higher-direct-image-limit,
lem-weil-pbc-filtered-category-exists-directed-final,
lem-weil-pbc-colimit-constant-connected-diagram,
lemma-constructible-pullback-constant,
lem-weil-pbc-constant-module-pushforward-functoriality, and
 def-weil-pbc-direct-image are not directly used by its new proof; its sole
proof dependency is affine section descent. The last three remain needed as
statement dependencies or by the single-square comparison below, so they are
not globally pruned. Directed reindexing and the constant-diagram colimit are
handled inside the existing globalSections_limit_comparison route if needed,
rather than repeated here. No claim is made that other consumers cease to reach
the removed modules. HigherDirectImageLimitClassDescent,
HigherDirectImageLimitClassVanishing and their presheaf-class auxiliary modules
are not used by this route; other targets may still need them.

The second reader also removed redundant proof imports from the new affine-section
module: Mathlib.CategoryTheory.Filtered.Connected and
Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated. Their declarations and instances
are already available from the retained imports; the reduced file compiles.

## Where the brief, the DAG or earlier work was wrong

The original node's continuity statement alone does not provide the explicit
module/abelian, degree-zero, and comparison-component identifications its last
step requires. Existing abelian pullbackSections_comparison and
GlobalSectionsLimitComparison give a shorter route without any derived objects.
The remaining missing interface is now stated independently of continuity.
GlobalSectionsLimitComparison and PullbackSectionsComparison are tools from
sk-prop-h2 used for section continuity; no statement or realized step of the
sk-thm-p1 unit is bypassed or altered. The main theorem's original docstring
is preserved; updated DAG proof steps record the implemented route.

The comparisons are well-typed with the original universe sizes, arbitrary
Lambda and M, and arbitrary base X. The affine section proof establishes qcqs
for the pullbacks, rather than assuming absolute qcqs for D_i or separation for X.
The single-square comparison makes no affine, qcqs or nonempty assumption;
empty pullbacks and the zero module have the same natural comparisons, and
a singleton inverse system is handled by the same limit argument. Cofilteredness
excludes an empty index category. No statements or definitions were changed.

## New nodes

lem-weil-pbc-constant-module-limit-affine-section-descent is the affine-test-object
section part of the argument, now fully proved from existing global continuity
and the independent cartesian comparison. It has no point or fiber in its statement.

lem-weil-pbc-constant-module-pullback-section-comparison is the sole new open item:
additive equivalences between constant-module direct-image sections and abelian
global sections of the corresponding constant pullback, compatible with one
cartesian map. This is independent of inverse systems and strictly a comparison
step, not the parent theorem under another name. Searches of the imported
blueprint for constant modules, sections, and pullback sections found no duplicate.
LeanFinder/Loogle/grep searches and the unavailable LeanSearch service were
recorded with their actual outcomes. No change record is needed.


## Second reading by V3

1. PASS: diff against the repository changes only the original theorem proof and
   plain proof imports. Its signature and original docstring are byte-for-byte
   unchanged. Both added modules are new; no existing definition, target, or public
   import is changed. The existing node changes only proof, proof_deps and
   proof_origin. No statement change record is required.
2. PASS: compiled all three modules in dependency order with lcompile.py, with no
   errors or warnings. Independently appended #print axioms to scratch copies for
   all three public theorems: each reports only propext, Classical.choice,
   Quot.sound and sorryAx. The sole textual sorry is the named single-square
   comparison theorem, with its docstring and node. There are no definitions in
   the delivery, no hollow data and no forbidden declaration or compiler escape.
   Existential equivalences are eliminated only inside a theorem proof.
3. PASS: the open comparison is a coefficient/evaluation/adjunction-unit identity
   for one cartesian square. It does not assert continuity, a stage representative
   or germ descent, and is strictly a part of the argument. Its equivalences come
   from forgetting coefficients, etale restriction and constant inverse-image
   comparisons. The two projection equations uniquely determine the cartesian map.
   The identity map gives identity compatibility; zero coefficients and empty
   pullbacks give zero groups, with no nonempty assumption required. No finite
   generation is used. Its docstring supplies the construction and coherence
   argument. Independent LeanFinder, Loogle and grep searches, plus source reads
   of constantCommuteCompose, upperStarConstantSheafIso, pullbackSectionsEquiv,
   pullbackSections_comparison and globalSections_limit_comparison, found no
   duplicate. Proving the remaining coefficient and composition coherence is not
   a short missing tactic: the abelian cartesian compatibility is itself open in
   an existing dependency. It remains explicitly reported as a hole.
4. PASS: read the germ proof from its target downward, then the affine-section
   reduction and comparison. The affine cover refinement preserves the point and
   germ by factorization and naturality. The base-changed cone is a genuine limit;
   qcqs follows relative to affine U, with no absolute hypothesis on X. Existing
   global-section continuity supplies the representative. The report lists all
   six old proof dependencies no longer used directly and all removed original
   imports. Read dag/units/sk-thm-p1.json and its realized list: this auxiliary
   descent node realizes none of its fixed statement or steps; all such nodes
   remain unchanged. The supporting sk-prop-h2 unit and the origins of the two
   section tools were checked as well. No unit route is replaced.
5. PASS: both new nodes match their Lean signatures, source and proof plans, have
   chapter/unit, created, blueprint, lean records and recorded searches. Each
   proof_deps is the union of the proof-step uses. The parent node records the
   actual affine-refinement, section-descent and germ-naturality proof. Its only
   non-elementary node dependency is the proved affine-section reduction.

Changed in this second reading: removed two redundant plain proof imports from
ConstantModuleLimitAffineSectionDescent, added the independent LeanFinder search
and its results to the open comparison node, and recorded this review. No proof,
statement or definition was rewritten. Accounting remains one original hole
closed, one new hole added, net zero: a decomposition, not an axiom-free proof of
the original module. The additional affine-section theorem is fully proved from
its stated dependencies.
