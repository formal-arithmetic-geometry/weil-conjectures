## What changed

Closed `AlgebraicGeometry.Scheme.isConstructibleSheaf_integral_backward`, preserving its
signature and docstring. Keep the supplied stratification, identify its set inverse images
with underlying abelian inverse images using filtered left Kan extensions and sheafification,
and apply `finite_local_abelian_forget_iff`. Transport abelian local constancy through the
canonical integral coefficient equivalence. Compare stalks on constant cover members to
prove finiteness at separably closed points from finiteness at algebraically closed points;
finite integral stalks are finitely generated. Finally commute the coefficient equivalence
with pullback and construct `IsConstructibleSheaf` on the same stratification.

All six private helpers are proved. No arbitrary object is chosen from a sorried existence
result: the only choices are from proved constancy and cover-lifting statements. The DAG
proof and dependencies now describe the actual Lean route. Compilation succeeds without
warnings, within the single-file time limit. The required leanfinder, loogle and grep searches
ran; the only relevant Mathlib search hit was `Sheaf.isConstant_iff_forget`, whose global
full-faithfulness assumptions are unnecessary here.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.isConstructibleSheaf_integral_backward`
(node `q1-constructible-integral-coefficients-backward`). No holes were added, no holes remain
in the delivered module, and nothing was split off. This is a proof from existing declarations,
and axiom inspection of the resulting theorem shows only `propext`, `Classical.choice`,
and `Quot.sound`. The earlier report of an inherited
`finite_constant_abelian_refinement` hole is stale: that imported theorem is now proved.
This delivery closes one hole and adds zero holes.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`
  (`lemma-weil-pbc-etale-pullback-forget-modules`);
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
  (the target uses `IsConstructibleSheaf`, not the finite-ring predicate);
- `Sheaf.Paper.InverseImageStalkGerm`
  (`lem-weil-pbc-inverse-image-stalk-germ`);
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`
  (`lemma-weil-pbc-universal-homeomorphism-site-equivalence`).

Also removed `lem-weil-pbc-torsion-sheaf-characterizations` from this node’s proof
dependencies. The proof does not use the torsion characterization, but its import is retained because
lem-weil-pbc-torsion-sheaf-characterizations realizes part of the fixed sk-def-pbc statement.

Also removed `lem-weil-pbc-constant-module-sheaf-underlying` from this node's proof dependencies:
we apply the coefficient equivalence to abelian constants directly. The geometric-stalk and
constructibility definition nodes remain needed. These are pruning statements for this item;
other targets or consumers may still require the removed modules. All public imports stay.
Added only the proof imports `FiniteLocalAbelianForget`, `ConstructibleSheaf.Pullback`, and
`Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`'s library extension
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.

## Where the brief, the DAG or earlier work was wrong

The backward direction needs no torsion hypothesis; its public signature is retained exactly.
The old plan proposed comparing separably closed stalks by universal homeomorphisms. The
existing abelian trivializing cover instead identifies both kinds of stalk with the same
constant value, so that machinery is unnecessary. Empty schemes require no chosen point:
cover lifts are used only after a geometric point is supplied. The zero constant group is
finite and causes no exception. The original unit `sk-thm-p1` statement and steps are preserved;
this item realizes none of its fixed unit-level steps. Sources read: public Stacks Tags
03RW, 095E and 03RU, plus the docstrings and signatures of the used library declarations.

## Earlier second reading (a previous round; superseded)

1. **Interface unchanged.** I compared the delivered Lean module with the repository version. The public theorem signature is byte-for-byte unchanged; only proof-only imports and the proof body changed. The DAG statement is unchanged.

2. **Proof validity.** The module compiles with `lcompile.py` in 11.7 seconds. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in the delivered file. Axiom inspection reports only the standard axioms together with `sorryAx` inherited from an imported open theorem (`finite_constant_abelian_refinement`), as documented in the report.

3. **Statements and dependencies.** No new public statements or split-off nodes were added. The private comparison helpers are true typed isomorphism/transport constructions, and the node proof and `proof_deps` match the route used in the Lean proof. The finite stalk argument handles separably closed points by lifting through a locally constant cover and uses the algebraic-closure point only to establish finiteness of the constant value.

4. **Pruning.** The removed imports and proof dependencies listed above are unused by the final proof; the retained imports are used. The coefficient and pullback comparison is explicit, so the proof does not rely on the previously proposed universal-homeomorphism or torsion machinery.

5. **Unit route.** The target's public statement and the unit record are preserved. This item realizes no fixed unit-level step, and the DAG retains `unit: sk-thm-p1` unchanged. The torsion characterization import is retained because `lem-weil-pbc-torsion-sheaf-characterizations` realizes part of the fixed `sk-def-pbc` statement, even though this proof does not use that characterization.

I changed only this review section; no Lean declarations or DAG statements were altered during second reading.

## Second reading by W2

1. Interface: read the full repository/sandbox module diff and node diff. The existing
   public theorem signature and docstring are byte-for-byte identical. Public imports,
   universes, namespace and visibility stay identical. Only proof imports, six proved
   private helpers, a private coefficient abbreviation and the theorem proof are new.
   No existing definition or statement was changed; no change record is needed. Pass.

2. Proof: compiled the delivered module through lcompile.py without errors or warnings
   (13.3 seconds). Compiled a scratch copy ending with
   `#print axioms AlgebraicGeometry.Scheme.isConstructibleSheaf_integral_backward`:
   only propext, Classical.choice and Quot.sound (12.3 seconds), with no sorryAx.
   Inspected all private constructions and the final proof: no sorry, forbidden declaration,
   or data selected from an unproved mere-existence theorem. Constants are selected from
   proved local-constancy witnesses; the coefficient functor and comparison isomorphisms
   are actual constructions. Pass.

3. New statements: no split-off statements, new public declarations or new nodes.
   Checked finiteLocalSets_of_iso transports both cover restrictions and stalk finiteness;
   abelianConstantStalkIso composes restriction/site-equivalence, pullback-stalk and
   constant-stalk isomorphisms in the required directions. finiteAbelianStalks lifts the
   supplied separably closed point through the cover, then uses an algebraic-closure
   point on that same member to show its constant value is finite. Thus empty schemes
   require no chosen point, empty irrelevant cover members cause no inference of finite
   constants, and the zero group remains valid. integralFiniteLocal transports constants
   through the canonical equivalence and uses finite underlying stalks to obtain finite
   generation. Read FiniteLocalAbelianForget and its refinement dependency. Pass.

4. Route and pruning: searched with different queries via leanfinder (finite stalks at
   separably closed points), loogle (Functor.lanCompIsoOfPreserves), grep (finite stalks
   and Kan extension comparisons), and rg in both library roots and upstream.
   No shorter matching public theorem was found. FiniteLocalCyclicModuleForget has a
   related private constant-stalk comparison but has cyclic, not integral, coefficients;
   it cannot replace this argument. The Mathlib Kan-extension comparison returned by
   Loogle is already used. Checked every old proof dependency against the new route;
   the pruning list now explicitly includes the unused torsion-characterization node,
   whose import is nevertheless retained for the fixed sk-def-pbc realization. The
   sk-thm-p1 realized statement and steps do not name this item, and none is bypassed.
   All public imports remain required by the signature; new imports are proof-only. Pass.

5. DAG: compared the unchanged statement and Lean record, checked each proof step against
   the corresponding helper and used declarations, and verified proof_deps is the union
   of step uses. Read the records for finite-local-abelian-forget, geometric-point lifting,
   pullback/local-site equivalence, stalk pullback and isomorphism invariance; their Lean
   declarations supply the operations used here. proof_origin describes this route.
   Unit and blueprint fields remain unchanged. Pass.

Second reading changed the report only: corrected the stale inherited-hole claim, completed
its pruning list, and added this independent review. Lean and DAG needed no repair.
