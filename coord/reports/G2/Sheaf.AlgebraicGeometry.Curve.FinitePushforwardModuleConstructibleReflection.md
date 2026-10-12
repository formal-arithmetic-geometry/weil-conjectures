## What changed

Closed AlgebraicGeometry.Scheme.isConstructibleSheaf_of_finite_lowerStar_module in
Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleConstructibleReflection without
changing its statement or public imports. Added proof imports of ConstructibleSheaf.Monoidal, the existing
FinitePushforwardCoefficientControl module (using import all), and the new locally
constant strata module. The proved private helper finite_module_stalks establishes
reflection of IsFiniteSheaf for arbitrary commutative coefficient rings and all
separably closed stalks, using the existing private theorem finite_counit_epi. The final proof combines this with locally constant strata.
Updated the parent node's proof route and added the geometric local constancy node.
The second reading restored the remaining geometric proof-plan imports in the new
module, all as proof-only imports.

## Proved and sorry left

Hole closed: AlgebraicGeometry.Scheme.isConstructibleSheaf_of_finite_lowerStar_module
(node p2-finite-pushforward-module-constructible-reflection). No sorry remains in
the assigned module. Its private helper finite_module_stalks is proved without new holes.
The duplicate finite_module_counit_epi helper was removed in this repair; the proof
now applies the existing AlgebraicGeometry.finite_counit_epi directly.

Hole added: AlgebraicGeometry.Scheme.exists_locallyConstant_stratification_of_finite_lowerStar_module
(node lem-weil-pbc-finite-module-locally-constant-strata), in the new module
Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleLocallyConstantStrata.
This is a decomposition: one upper hole closed, one strictly partial geometric
hole added. The new statement supplies only local constancy, whereas finite
source stalks are proved independently in the parent (without a curve hypothesis).
The main proof builds the finite locally constant class fields and the
constructibility witness; it does not merely rename or apply a new copy of the
original theorem. Net holes closed minus holes added is zero.

Both modules compile together through lcompile.py --all. The inherited hypotheses
and universes are unchanged. The finiteness proof handles separably closed stalks
by the epic counit, using the finite product formula only at algebraically closed
points. No unproved theorem supplies arbitrary data to a definition.

## No longer needed

Removed these original proof imports from the parent module:
- Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting
- Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
- WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
- WeilConjectures.SixFunctors.Finite.BaseChange
- WeilConjectures.SixFunctors.Finite.Stalk

The first four are now proof-plan imports of the local constancy module, together
with ConstructibleSheaf.GenericConstancy and ConstructibleSheaf.UniversalHomeomorphism
(which publicly supplies Pullback). The fifth remains a transitive dependency of
the reused counit. No original public import was removed. No module is globally
pruned. The original parent proof_deps no longer used directly are
thm-weil-pbc-universal-homeomorphism-invariance,
lem-weil-pbc-generic-finite-algebra-splitting, lemma-weil-pbc-finite-exchange,
lemma-constructible-hom-constant-locally, and lemma-weil-pbc-finite-stalk-formula.
The first four remain dependencies of the local constancy node; the last is used
by the existing counit. Removed the duplicate private declaration
AlgebraicGeometry.finite_module_counit_epi from the returned delivery.

## Where the brief, the DAG or earlier work was wrong

Repair of the return: the earlier delivery repeated the exact statement of
AlgebraicGeometry.finite_counit_epi, which is already proved in
Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl. Although that
helper is private, a proof-only import all makes its name available without any
change to its visibility or signature. The duplicate helper is now deleted and
finite_module_stalks uses the existing proof. The import-direction check permits
this dependency, and both delivered modules compile together without warnings.
The parent DAG now records the existing coefficient-control node for this step.
The previous second reading was removed for a fresh independent reading.

The arbitrary coefficient ring excludes the existing Noetherian-ring retract
constructibility theorem and the torsion/ULift-Z reflection interfaces. These
are not interchangeable with the assigned statement. The local constancy portion
of the original node has no directly applicable existing declaration; it is now
an explicit item, with the source argument and edge cases in its docstring.

Read Stacks etale-cohomology.tex labels lemma-decompose-quasi-finite-morphism
(095K), lemma-finite-pushforward-statements (0A5D), and the relevant library
constant-sheaf, pullback and universal-homeomorphism interfaces. The new proof
sketch uses the original direct-factor refinement, not a claim that an arbitrary
quotient of a locally constant module sheaf is locally constant. Empty sources,
empty fibres, the zero ring/sheaf, zero-dimensional curves, nilpotents, and
degree-one finite morphisms are included. Projectors are made locally constant
using finitely many generators, not finiteness of the underlying module set.

Actual Mathlib searches are in searches.jsonl: LeanFinder returns sheaves of
modules of finite type but no etale source stratification; grep finds no matching
finite-image reflection; Loogle finds Module.Finite.of_surjective, used in the
proof. LeanSearch returned Internal Server Error, recorded as unavailable.
Whole-blueprint searches for finite pushforward and locally constant found no
arbitrary-module source-stratification theorem. The unit's realized route is
unchanged: this is a lower-level split of the C4/C5 constructibility reflection.

## New nodes

lem-weil-pbc-finite-module-locally-constant-strata records the source stratification
with locally constant restrictions only. Its proof explains reduction, generic
finite-algebra splitting, direct-summand projectors, etale descent, and the
remaining algebraically closed point strata. Stalk finiteness is deliberately
outside this remaining geometric assertion and is proved in the parent. The new
node inherits sec-proper-base-change / sk-thm-p1 and records its place in the
normalization/finite-direct-image blueprint route. No change record is needed:
no existing definition, statement, universe or visibility was changed.

## Second reading by G2

1. Compared the existing module and parent node with the repository using diff.
   The theorem signature, surrounding coefficient parameters, universe, visibility,
   original docstring, and public imports are byte-for-byte unchanged. Only proof
   imports, a proved private helper, and the proof body changed. The parent's node
   changes only proof, proof_deps, and proof_origin. Read the landed change record
   finite-pushforward-module-constructible-reflection.md; no new interface change
   or forced adaptation is present.
2. Compiled both modules together with lcompile.py --all after repairs: clean.
   In a scratch copy, #print axioms shows only propext, Classical.choice, Quot.sound
   for finite_module_stalks and the imported finite_counit_epi. The main theorem
   and the new local constancy theorem additionally use sorryAx, as expected.
   Exactly one sorry remains, in the named new theorem with its node and proof
   docstring. No forbidden declaration, hollow definition, or arbitrary witness
   used to define data occurs. Checked the stalk quotient proof at every separably
   closed point: the skyscraper adjunction preserves epis, ModuleCat converts epi
   to surjectivity, and Module.Finite.of_surjective gives precisely the needed
   finite-generation field.
3. Read the entire new theorem, node, generic finite-algebra splitting theorem,
   constant-sheaf interfaces and constructibility definitions. The remaining
   assertion supplies local constancy only; stalk finiteness has a separate
   proved argument without a curve hypothesis. This is a strict partial reduction,
   not a renaming of constructibility reflection. Tested empty source/fibres,
   zero ring/module, dimension zero, degree one, and nonreduced source/target.
   The projector argument uses finitely many module generators, not finitely
   many elements of the module, and uses direct summands rather than arbitrary
   quotients. The omitted closed fibres have reduction a finite disjoint union
   of algebraically closed points, where every module sheaf is constant.
   Independently ran LeanFinder on direct summands of locally constant finitely
   generated module sheaves (only condensed-module results), Loogle on
   Module.Finite.of_surjective (exact match), and grep on retract/local-constant
   and summand/constant concepts (no match); searches.jsonl records these calls.
   Searched lean/Sheaf and lean/WeilConjectures with both pushforward/reflection
   and retract/local-constant terminology. Existing of_retract requires
   IsNoetherianRing, and finite underlying-set interfaces do not cover arbitrary
   finitely generated modules. No split-off hole closes in a few minutes.
4. Read the unit sk-thm-p1.json including realized, and the original proof_deps.
   The C4/C5 normalization and finite-direct-image route stays unchanged; this
   split is below the unit level. The parent now combines proved finite stalks
   with local constancy on the same stratification. Completed No longer needed
   with every original proof import and old dependency removed from the parent;
   none is claimed globally pruned. Added the remaining hole's proof-plan
   imports to its own module so the geometric route stays available there.
5. The Lean conclusion of the new node agrees with its verbatim lean.statement;
   its statement, complete proof sketch, source, three search records, status,
   created, blueprint, chapter, unit, and lean fields are present. Parent steps
   follow the counit, finite-stalk quotient, and stratification assembly actually
   written. The new node's uses union equals its proof_deps. Read the source
   pages [095K](https://stacks.math.columbia.edu/tag/095K),
   [0959](https://stacks.math.columbia.edu/tag/0959), and
   [0A5D](https://stacks.math.columbia.edu/tag/0A5D): 0959 supplies finite exchange;
   095K supplies the geometric stratification motivation. The arbitrary-module
   refinement is the explicit generic-splitting/projector argument written here,
   not a claim that 0A5D itself states arbitrary-module reflection.

Changed in this second reading: restored six proof-plan imports in the new
local constancy module and completed the removed-import/dependency accounting.
The proved Lean argument and every existing signature were left unchanged.
One original hole is closed syntactically, one geometric hole is added; this
is a decomposition with net zero holes closed, and no globally pruned module.
