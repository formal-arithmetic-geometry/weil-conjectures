## What changed

Replaced the sole proof in
Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing with a complete Lean reduction.
The proof writes the positive degree as q+1, equips the induced open subscheme with the
IsAffine instance supplied by hU, restricts F using Scheme.Modules.restrictFunctor U.ι,
and applies Scheme.Modules.subsingleton_H_succ_of_isAffine. Mathlib supplies
quasi-coherence of the restriction. The additive comparison with open module cohomology
then transports subsingletonness by its injectivity.

Added the proof-only import Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison and
its new module. Updated pqf-lem-affine-vanishing's proof, proof_deps and proof_origin.
The existing theorem's signature and all definitions are unchanged.

## Proved and sorry left

AlgebraicGeometry.subsingleton_openModuleCohomology_of_isAffineOpen: its former sorry
is replaced with a compiling proof. No sorry remains in the assigned module.

AlgebraicGeometry.nonempty_openModuleCohomology_addEquiv_restrict_H: one new named
sorry, in Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison, with node
lem-pqf-open-module-cohomology-comparison. This is a general comparison, not a vanishing
statement: it assumes neither quasi-coherence, affineness nor positive degree. Its
docstring supplies the resolution-restriction argument (01E1) and the comparison after
forgetting modules (03FD). The original affine vanishing theorem is used separately,
not included in the remaining statement.

Both delivered modules compile together with no warnings using lcompile.py --all.
The comparison was checked on U empty (zero section complexes), U top (the ordinary
module/abelian comparison), F zero, and degree zero (the usual equality of sections).
It imposes no assumptions excluding these cases.

## No longer needed

None. The original sole proof dependency lem-pc-affine-vanishing and its
proof-only import remain used. The original public imports remain because they
are also the module's exported interface for its nine direct importers; removing
them requires an interface change and downstream review, as preflight confirms.
The new comparison import is proof-only. The unit's realized fields are empty,
and the approved affine-scheme route is retained.

## Where the brief, the DAG or earlier work was wrong

Step 3 of the original DAG calls the comparison elementary, but the definitions are
different derived constructions: openModuleCohomology derives additive sections in
module sheaves on X, whereas Scheme.Modules.H is Ext cohomology of abelian sheaves
on the induced open scheme. The new node isolates this missing comparison.

The original theorem docstring cites Tag 01E3 for injective module/abelian acyclicity.
The current Stacks 01E3 states local annihilation of cohomology classes, not that
comparison. The appropriate reference is 03FD. The new node and docstring use 03FD;
the second reader corrected that citation in the old docstring.

Searches actually run via msearch.py: LeanFinder returned only cohomology definitions
and section-level facts; Loogle did not recognize Functor.rightDerived; grep of the
comparison names returned no Mathlib matches; LeanSearch returned Internal Server Error.
Repository searches found module_cohomology_iso_underlying_abelian for global module
cohomology and restrict_injectiveResolution for restriction on the over-site, but no
additive comparison of the two displayed open-scheme constructions. The new lemma's
proof plan uses these existing results rather than duplicating their statements.
Blueprint searches for "cohomology of modules" and "Locality of cohomology" found no
matching blueprint nodes; the existing comparison nodes concern global cohomology.
The affine theorem is an already approved tool use for this item.

## New nodes

lem-pqf-open-module-cohomology-comparison, in
 dag/nodes/sec-abelian-varieties/lem-pqf-open-module-cohomology-comparison.json,
states the additive comparison of module-derived sections on an arbitrary open
with underlying abelian cohomology of the restricted module. It is sourced to
Stacks 01E1 (2) and 03FD and records the actual searches. The proof steps restrict
an injective resolution, identify the section complexes, then apply the existing
module/abelian comparison and identify terminal-object Ext with Scheme.Modules.H.
Its statement module is Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison.
There are no statement or definition changes and no change records.

## Second reading by B3

1. Compared the existing module with the repository using diff. Its theorem signature
is byte for byte unchanged; no definitions were changed or introduced. Changes are
the proof, imports, and the correction of the docstring's 01E3 citation to 03FD.
The new comparison has its own new module and node. No change record is needed for
an existing statement or definition; none changed.
2. Both modules compiled locally without errors or warnings. The assigned theorem
contains no sorry; exactly one named theorem remains sorry in the new comparison
module. Scanned for forbidden declarations and attributes; none occurs. A scratch
copy with #print axioms for both delivered declarations shows only propext,
Classical.choice, Quot.sound, and sorryAx. Thus the original sorry is reduced, not
an axiom-free closure of the target: the general comparison still needs proof.
3. Read the comparison and its node against Stacks 01E1 (2) and 03FD. The statement
is true without affineness or quasi-coherence; for U empty both groups are zero,
for U top it is the global module/abelian comparison, for F zero both are zero,
and for p=0 both are sections on U. It is not a renamed vanishing theorem: the
actual affine vanishing is supplied separately by the existing theorem. Read
restrict_injectiveResolution and module_cohomology_iso_underlying_abelian; their
statements supply the steps cited. Independently searched LeanFinder for derived
sections and open restriction, Loogle for Functor.rightDerived (identifier unknown
to the service), and grep for isoRightDerivedObj and derived-comparison names.
Mathlib supplies the resolution computation, but no ready comparison of the two
displayed constructions was found. Upstream's higherDirectImage comparison has
affine-base, quasi-compactness, separatedness and quasi-coherence hypotheses and
different functors, so does not close this arbitrary-open comparison in a few lines.
No few-minute proof of the split-off comparison was found.
4. The proof first uses the existing affine theorem and then the new general
comparison. Checked the original proof_deps: its sole dependency,
lem-pc-affine-vanishing, remains used. The unit sk-prop-av-pqf-finite has empty
realized fields, and the approved affine-scheme tool route is retained. Reviewed
the original public imports and retained their exported interface, on which nine
direct importers may rely; no unused original proof-only import remains. Both new dependency imports are plain
proof-only imports; the new module's two public imports are needed by its signature.
5. Compared proof steps, proof_deps and proof_origin with the Lean reduction;
they agree. The new node has source, complete proof steps, dependency union,
statement dependencies, creation provenance, blueprint parent, unit, chapter,
verbatim Lean signature and genuine logged searches. Replaced duplicate grep
records with the independent reader's three actual searches. Added the omitted
exact-forgetful/homology step to the docstring and node. Existing node changes
are confined to the permitted proof fields.

Repairs: added proof-plan imports of RestrictInjectiveResolution and
ModuleAbelianZariskiCohomology to the new module; made explicit why forgetting the
global-ring module structure preserves homology; corrected the Stacks citation;
retained the original public-import interface after the dry-run check; repaired
the new node's search records. The compiling Lean reduction itself was retained.

The first dry run rejected removal of the legacy public imports because it changes
what nine downstream modules see and requires a change record. Reverted that
interface change; this delivery keeps all original public imports. A read-only
invocation of tools/downstream.py returned no output on this machine, so direct
importers were independently enumerated with rg. No tools were modified.
