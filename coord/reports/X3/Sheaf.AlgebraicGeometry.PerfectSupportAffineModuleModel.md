## What changed

Replaced the whole proof of
AlgebraicGeometry.Scheme.perfect_support_affine_module_model by a compiling reduction.
The existing signature, universes, public imports and docstring are unchanged.
The proof constructs F as the exact derived functor of the existing explicit
AlgebraicGeometry.Scheme.affinePerfectSheafification. A private proved helper establishes
finite-limit preservation using localization injectivity for tilde. Colimit preservation
and additivity follow from the adjunctions and equivalences. Fullness is proved by comparing
F with the affine derived equivalence followed by the full quasi-coherent inclusion and
the existing affine localized-site derived transport. The comparison descends through Q.
The proof assembles independently obtained source and target models and applies scalar
compatibility to its chosen source isomorphism. No arbitrary witness is chosen to define data.

Three new modules state strictly separate outstanding steps: the perfect source model,
the supported shifted target model, and scalar compatibility for an arbitrary comparison.
Each states one named public theorem with a complete proof in words and its own DAG node.
The parent node's proof and proof dependencies now describe the Lean reduction.
A declaration-local heartbeat allowance accommodates elaboration of the two localization
comparisons and witnesses; the module compiles within the single-file time limit.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.perfect_support_affine_module_model
(lem-sc-perfect-support-affine-module-model).
There are no sorries left in the item's module. Exactness, additivity, fullness and the
combining proof are written in Lean. This is a decomposition, not an axiom-free proof
of the whole mathematical result: one hole closed, three holes added, net minus two.

Added and left exactly these three holes:

- AlgebraicGeometry.Scheme.affine_open_perfect_source_model
  (lem-sc-affine-open-perfect-source-model): bounded finite-projective source only;
  no support, target or scalar assertion.
- AlgebraicGeometry.Scheme.affine_open_supported_target_model
  (lem-sc-affine-open-supported-target-model): module preimage and elementwise torsion
  of the shifted target only; no perfect source or uniform exponent.
- AlgebraicGeometry.Scheme.affine_open_realization_scalar
  (lem-sc-affine-open-realization-scalar): scalar identity for any comparison;
  no model existence, perfectness or support assumption.

All four delivered modules compile together without errors or non-sorry warnings.
The private exactness helper is proved, with no new sorry in a definition or private theorem.
The split statements cover the empty open, zero ring, zero scalar, and unit scalar;
none requires the original scheme to be quasi-compact or quasi-separated.

## No longer needed

Removed direct proof imports Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective and
Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison from the item's module.
Their nodes lem-pc-perfect-affine-bounded-projective and
lem-pc-open-derived-restriction-comparison are still required by the new source/target
steps and are explicitly imported there. Thus no mathematical dependency module is
claimed pruned from the target closure. No unit statement or realized unit step is bypassed.
The original affine derived equivalence import is retained and used in the fullness proof.
No other old node or module becomes unnecessary in this delivery.

## Where the brief, the DAG or earlier work was wrong

The existing three dependencies supply the spectrum model and restriction comparisons,
but do not themselves state source perfection after open restriction, the supported
shifted module preimage, or scalar compatibility under the explicit affine realization.
The parent proof's third step has no named dependencies despite containing these substantial
comparisons. This delivery makes its independent obligations available as separate items.
No false statement or weakened conclusion was found.

LeanSearch returned Internal Server Error for all three new statements; LeanFinder,
Loogle, Mathlib source grep and project/blueprint searches were used and recorded.
WANTED: literature/stacks-project/perfect.tex, Tags 06Z0, 08EB and 08EJ, for the three
new nodes; the local source file is absent on this machine. The canonical tag texts
were read at https://stacks.math.columbia.edu/tag/06Z0,
https://stacks.math.columbia.edu/tag/08EB and https://stacks.math.columbia.edu/tag/08EJ.
The proof interface elaboration needs explicit derived-category universe parameters
because the open-site target and the module category use different morphism universes.

## New nodes

lem-sc-affine-open-perfect-source-model:
lean/Sheaf/AlgebraicGeometry/AffineOpenPerfectSourceModel.lean. The bounded source
portion of steps 1 and 2, with a fixed natural realization comparison; strictly omits
the supported target and scalar conclusion. Uses the existing restriction, spectrum
perfect criterion, localized transport and scheme-isomorphism perfect transport nodes.

lem-sc-affine-open-supported-target-model:
lean/Sheaf/AlgebraicGeometry/AffineOpenSupportedTargetModel.lean. The shifted target
portion of steps 1 through 3, with its cohomology torsion and counit. No perfectness
hypothesis or source model, and no finite generation of the target is assumed.

lem-sc-affine-open-realization-scalar:
lean/Sheaf/AlgebraicGeometry/AffineOpenRealizationScalar.lean. The sectionwise scalar
comparison portion of step 3. It works for every model complex and arbitrary isomorphism,
independently of existence, boundedness, perfectness and support.

No existing interface or statement changes; no change record or forced adaptation.
Second reading removed the redundant proof import of
Mathlib.Algebra.Homology.DerivedCategory.Linear from AffineOpenRealizationScalar;
DerivedGlobalScalar already publicly supplies it, so this prunes no closure module.


## Second reading by X3

1. Compared the sole existing module with its repository version using diff and
   checked the complete theorem signature byte for byte. Verdict: unchanged,
   including every hypothesis, conclusion, universe and the eM binder. Public
   imports and the existing docstring are unchanged. The three other modules are
   new; no existing definitions, targets or unheld modules are changed.
2. Compiled all four delivered modules in import order through lcompile.py:
   4.3, 4.5, 4.7 and 17.1 seconds, exit zero. A scratch copy with explicit
   #print axioms checks showed only propext, Classical.choice and Quot.sound for
   affineSheafification_preservesFiniteLimits, and those plus sorryAx for the
   parent and the three split statements. Read every proof: localization
   injectivity proves exactness, localization uniqueness transfers fullness to
   the explicitly constructed mapDerivedCategory functor, and the witnesses are
   assembled without changing the conclusion. No forbidden declarations or
   hollow data definitions exist. The only three direct sorries are the reported
   public named statements. Equivalence witnesses from upstream existence
   theorems are eliminated inside a proposition to prove fullness, not used to
   define the delivered functor or any public data.
3. Read each split statement, its docstring and node, and checked canonical
   Stacks Tags 06Z0, 08EB and 08EJ. Verdict: true, needed, strictly separate parts
   of the argument, not renamed copies of the parent. The source statement
   omits target/support/scalars; the target statement omits source/perfectness/
   uniform exponents; the scalar statement is a naturality identity without
   model existence. For arbitrary F, the natural comparison through Q suffices
   by localization uniqueness. Empty U and the zero ring give zero categories;
   f=0 permits exponent 1, and a unit f forces zero target cohomology. An arbitrary
   e commutes with global scalar identities by centrality. Independent searches
   via msearch.py (LeanFinder, Loogle, grep), plus rg of both library roots,
   found only components: bounded derived representatives, linear map_smul,
   and LocalizedModule.subsingleton_iff_support_subset. None closes a split
   statement in a few minutes; all three remain explicitly reported holes.
4. Checked the proof from its explicit functor construction down to the three
   uses, the old proof_deps, and dag/units/sk-thm-picard-duality.json realized.
   Verdict: no unit route bypassed; the realized lists are unchanged. The two
   removed direct dependency imports are still needed in the split modules and
   the report names them. No module is claimed pruned from the target closure.
   Proof-only imports are plain imports. Removed one redundant plain import of
   Mathlib.Algebra.Homology.DerivedCategory.Linear from the new scalar module;
   its public DerivedGlobalScalar import already provides it. The exactness
   helper is not replaced by the private helper in AffineDerivedTildeHomologyComparison,
   which is inaccessible and proves a different intermediate kernel interface.
5. Read all four node records alongside the Lean. Verdict: the parent's steps
   and dependency union match exactness/fullness, the two model calls, and the
   scalar call. Each new node records the proper source, separate statement,
   docstring proof, dependencies, origin, creation, blueprint, chapter, unit and
   Lean declaration. Added independent Loogle search evidence to the three new
   nodes. The existing node changes only its proof, proof_deps and proof_origin.

Changed only the redundant scalar proof import, the three new nodes' search
records, and this report. Tried removing the declaration-local unusedVariables
suppression: Lean then warns about the original existential eM signature binder.
Restored the suppression to keep that existing signature byte for byte unchanged.
The ledger result remains a decomposition: one original hole closed, three added,
net minus two; no additional hole was closed during second reading.
