## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.ConstantModuleHigherDirectImageCyclicReduction` with a complete
Lean reduction. Every existing signature and public import is unchanged.

The proof constructs the quotient coefficient module, restricts it to lifted integers,
and uses the canonical `Module.fgSystem` diagram and colimit cocone. It proves the
annihilator equation, proves vanishing of every finitely generated submodule, and maps
the concrete cocone to a colimit of zero objects. The canonical fgSystem linear
isomorphism transfers this to the original additive quotient. Finally the already
proved `nonempty_higherDirectImage_forget_iso` and `constantCommuteCompose` transfer it
to the original module coefficient. Faithfulness detects the vanishing identity.

Added `Sheaf.Algebra.FinitelyGeneratedCyclicFunctorVanishing`, with a fully proved
`ModuleCat.isZero_obj_of_fg_of_cyclic`. This is purely algebraic: Mathlib's finitely
generated group classification gives a finite decomposition. Evaluating the
annihilator on torsion generators proves divisibility; evaluating it on a free
generator forces d=0. Explicit projections and inclusions write the identity as a
finite sum of maps through the cyclic factors. Additivity makes its image zero.
No finite-generation or torsion assumption has been added to the original theorem.

Added `Sheaf.AlgebraicGeometry.ConstantAbelianHigherDirectImageFilteredColimit` to
isolate the remaining coefficient-size continuity argument. Its index category is
in Type(u+1), matching the actual set of finitely generated submodules; it has no
torsion assumption, so the d=0 case is retained. Its docstring gives the full
03Q5/0739/03Q8 argument, including naturality of the canonical cocone comparison.
The corresponding new node names the existing large cohomology, affine-site
comparison, pullback-of-constants, and sheafified-presheaf interfaces for the next worker.

Three local modules compile with lcompile.py, with no compiler or linter warnings.
The algebraic helper is proved entirely from Mathlib. No unproved existence theorem
is used to choose coefficient data: the quotient and direct-limit diagram are real
constructions, and the classification equivalence comes from a proved Mathlib theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.isZero_constantModHigherDirectImage_of_cyclic`
(node `lem-sbc-constant-module-higher-direct-image-cyclic-reduction`).
The proof combines the explicit colimit construction, the fully proved algebraic
helper, and the existing coefficient comparison, conditional on the new continuity lemma.

Fully proved the new declaration `ModuleCat.isZero_obj_of_fg_of_cyclic`
(node `lem-sbc-fg-cyclic-functor-vanishing`), with no sorry.

The sole sorry added, and the sole sorry in all delivered files, is
`AlgebraicGeometry.Etale.preservesColimitsOfShape_constantAbelianHigherDirectImage`
(node `lem-sbc-constant-abelian-higher-image-filtered-colimit`).
Thus one upper hole was closed and one strictly smaller continuity hole was added:
this is a decomposition, not an unconditional proof of the original theorem and
not a claim of positive net hole progress.

The algebraic proof includes d=0, d=1, the zero module, empty free and torsion
indices, and ZMod 1 factors. The remaining continuity statement includes degree zero
and empty schemes and imposes no torsion condition. The main proof includes the zero
coefficient ring and arbitrary coefficient cardinality.

## No longer needed

Removed the direct proof imports:

- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`;
- `Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit`;
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`.

The small-index node `lem-weil-pbc-cohomology-filtered-colimit` is not used directly:
the index here is Type(u+1), and the new continuity node instead uses
`lem-pbc-u2-sheafH-large-filtered-colimit-derived`.
The direct use of `lem-weil-pbc-etale-module-cohomology-forget` is replaced by the
already proved higher-direct-image interface
`lem-sbc-higher-direct-image-forget-comparison`; its cohomological infrastructure
remains a transitive dependency of that interface.

The presheaf node `sbc-lem-higher-direct-image-presheaf` and the sheafification node
`def-weil-pbc-sheafification` are still needed in the new continuity node's proof plan;
they are not claimed as mathematically pruned. The structure-theorem node
`lem-sbc-finitely-generated-abelian-group-structure` is still used by the proved
algebraic helper. No unit-level statement or step has been bypassed.

Did not import
`Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit`.
Second reading found that the claimed import cycle is absent from the current
source tree. This existing theorem handles module coefficients, rather than the
abelian coefficient functor stated here. A trial transport through lifted-integer
modules, the natural derived coefficient comparison and the constant-sheaf
comparison did not compile within the 60-second single-file limit. The existing
module theorem itself imports and checks successfully in 4.0 seconds, so the delay
is in the attempted comparison proof. The verified decomposition is retained;
the module theorem is a candidate shorter route for closing the remaining node.
No modules held by another group were adapted.

## Where the brief, the DAG or earlier work was wrong

The existing DAG's small-index cohomology theorem does not directly handle the
coefficient-size set of finitely generated subgroups of an arbitrary Type(u+1) ring.
This delivery tracks that universe explicitly rather than asserting the index is small.
The existing module large-continuity theorem is available in the current tree;
its applicability requires a natural transport from module coefficients to the
abelian coefficient functor. The first report's import-cycle claim was stale and
has been corrected by the second reader. The new abelian constant-coefficient statement
is only the continuity step: it has neither a cyclic-vanishing hypothesis nor a quotient
coefficient conclusion, and does not repackage the original theorem.

Source statements checked: Stacks 03Q5 has no torsion hypothesis on abelian sheaves;
0739 applies to arbitrary filtered diagrams on a finite-cover basis; 03Q8 computes
higher images by the sheafified restricted cohomology presheaf. These support the
remaining continuity statement, including d=0 and degree zero. References:
https://stacks.math.columbia.edu/tag/03Q5,
https://stacks.math.columbia.edu/tag/0739,
https://stacks.math.columbia.edu/tag/03Q8.
No statement is disputed and no existing definition or signature was changed.

## New nodes

`lem-sbc-fg-cyclic-functor-vanishing`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-fg-cyclic-functor-vanishing.json`, records
the proved algebraic helper. The statement introduces preadditivity, additivity,
finite generation, zero objects, and the canonical lifted-integer action explicitly.

`lem-sbc-constant-abelian-higher-image-filtered-colimit`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-constant-abelian-higher-image-filtered-colimit.json`,
records the single remaining continuity theorem, its source, complete proof plan,
and the existing declarations to use next. Both nodes keep the original chapter
and unit and point back to the original presheaf blueprint ancestor's coefficient
reduction. Searches of the full imported blueprint found no duplicate of either
specific statement. The Mathlib search logs contain all three requested search
kinds for both statements; LeanSearch was actually unavailable (HTTP 500).
Second reading removed the redundant imports `Sheaf.AlgebraicGeometry.DerivedCategories`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, and
`Mathlib.CategoryTheory.Filtered.Basic` from the new continuity module.
`ConcreteCoefficients` and `UpperLowerStarCoherence` supply its entire interface;
a scratch copy with just these two public imports compiled in 2.2 seconds.
Removing `ConcreteCoefficients` fails on the Grothendieck/derived-category instances,
so it is needed for the statement.
No change record is needed: all changes to the existing module are proof imports
and proof code, and both extra interfaces are new modules.


## Second reading by C2

1. Compared the delivered original module with the repository file by `diff -u`.
   The declaration `isZero_constantModHigherDirectImage_of_cyclic`, including
   coefficient universe, all hypotheses, cyclic quantification and conclusion,
   is byte-for-byte unchanged through `:= by`. Its docstring and three public
   imports are unchanged. Only proof imports and the proof body differ. There
   are no changed definitions, forced adaptations or change records. Verdict: pass.

2. Independently compiled all three delivered modules in import order with
   `lcompile.py --all`: 6.1, 3.4 and 16.2 seconds, no errors or warnings. A scratch
   module printed axioms of all three public theorems. The algebraic helper uses
   exactly `propext`, `Classical.choice`, `Quot.sound`; the continuity theorem and
   original theorem additionally use `sorryAx`, as reported. Inspected the
   private linear-map construction and the quotient/fgSystem constructions:
   their data contain no sorry and no arbitrary unproved existence witness.
   Mathlib's classification equivalence is chosen from a proved theorem. There
   is exactly one delivered sorry, in the named continuity theorem, and no
   forbidden declarations. Verdict: pass as a decomposition, not a closed target.

3. Read the two new Lean statements and their nodes. The algebraic helper is
   strictly the finite-generation part: it evaluates the annihilator on free
   and torsion single generators and checks the explicit identity decomposition
   coordinatewise. Empty indices give empty sums, d=0 allows free summands,
   d=1 gives only zero torsion factors, and zero modules are included. The
   remaining theorem concerns canonical filtered cocones only, with neither
   cyclic vanishing nor a quotient coefficient conclusion. Checked q=0, the
   empty source, identity morphisms and arbitrary coefficient-size filtered
   categories. Read Stacks Tags [03Q5](https://stacks.math.columbia.edu/tag/03Q5),
   [0739](https://stacks.math.columbia.edu/tag/0739),
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8) and
   [0F08](https://stacks.math.columbia.edu/tag/0F08), and Mathlib's
   `AddCommGroup.equiv_free_prod_directSum_zmod` at lines 119–132. The continuity
   proof uses qcqs only after restricting the target to affine etale objects;
   0739 imposes no torsion condition. Independently searched with LeanFinder
   for coherent-site cohomology continuity, Loogle for additive functor zero
   objects (identifier unavailable), msearch grep for cyclic zero objects, and
   rg over both Lean roots for filtered higher images. No exact replacement
   for either new statement was found; the existing module-continuity result
   is the transport candidate described above. Both new declarations have
   matching nodes, sources and natural-language proofs. Verdict: pass.

4. Read the proof from the conclusion backwards: faithful forgetting detects
   the zero identity; the existing higher-image comparison and
   `constantCommuteCompose` identify the forgotten image; fgSystem gives the
   explicit coefficient colimit; the proved helper handles each finite subgroup.
   Thus no cyclic reduction has merely been renamed. Checked each proof import
   against these uses; proof-only imports are plain imports. The new continuity module was separately checked with only its two necessary
   public imports; three redundant public imports were removed. The removed direct
   modules and all old proof dependencies are accounted for in `No longer needed`:
   the structure theorem remains through the helper, presheaf/sheafification
   remain in the continuity plan, and the old small-index and cohomological
   coefficient interfaces are replaced by the stated larger/higher interfaces.
   Read `dag/units/sk-lem-failure-field.json`: its realized statement and step
   lists are empty and unchanged; the delivery changes only a coefficient
   reduction below that unit and bypasses no realized unit step. Verdict: pass.

5. Compared the original node: only `proof`, `proof_deps`, `proof_origin` differ.
   Its three proof steps match the quotient/finite decomposition, mapped colimit,
   and faithful coefficient comparison in Lean. Read the new nodes in full:
   their proof dependency unions, original chapter/unit, creation records,
   Lean signatures, searches and blueprint ancestry match the delivery. Checked
   the cited large cohomology theorem's Type(u+1) index, the abelian presheaf
   interface and the pullback-of-constants statement. The continuity plan uses
   affine qcqs pullbacks and the natural sheafification comparison rather than
   asserting continuity on a non-qcqs scheme. Verdict: pass.

Second-reading changes: corrected the stale import-cycle claim in this report,
and removed three redundant imports from the new continuity module.
Tried the existing module-continuity route in scratch copies, but retained the
original cleanly compiled proofs after the comparison trials exceeded the file
limit. No delivered Lean statement, proof body or node was rewritten. The accounting
remains one original hole closed, one new continuity hole added, and a fully
proved new algebraic helper: net zero holes, a genuine decomposition.
