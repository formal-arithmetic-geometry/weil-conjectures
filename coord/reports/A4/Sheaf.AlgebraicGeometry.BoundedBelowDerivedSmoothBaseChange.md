## What changed

Completed `AlgebraicGeometry.Etale.boundedBelow_derived_smooth_baseChange` with its
signature, universes and all three conjuncts unchanged. Its single `sorry` is replaced
by a complete proof. The original bounded-to-bounded-below unit route is retained:
apply bounded smooth base change to upper truncations, use the truncation criterion
and naturality in each degree, then detect isomorphisms on cohomology.

The allowable-torsion typing is also proved. Higher direct images of single sheaves
use the existing qcqs prime-torsion theorem. The existing proved field-extension
stalk comparison identifies stalks after extending a separably closed field to its
algebraic closure, so that theorem needs no interface repair. No stronger
algebraic-closedness hypothesis on the point field is imposed. Bounded
triangulated devissage plus the truncation triangle then proves torsion preservation
for bounded-below complexes. Exact inverse image and its stalk comparison supply
source typing; the exchange isomorphism transports it to the target.

Refactored `AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow` in the unclaimed
module `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: construct its unit,
composition comparisons and counit as a natural transformation and evaluate at K.
The new constructed definition is `abelianDerivedBaseChangeTransformation`.
Existing signatures, public imports and canonical maps are preserved; this avoids
kernel timeout during componentwise naturality proofs. Change record:
`coord/changes/A4-abelian-exchange-natural-transformation.md`.
The definition change reopens dependent targets' statement review. No target
statement and no other group's module is changed.

Updated the proof, proof dependencies and proof origin of
`sbc-thm-bounded-below-derived-smooth-base-change`; updated the existing definition
node's Lean declaration list and explanation. No new nodes or modules.

New proof imports:

- `Sheaf.AlgebraicGeometry.GeometricPointFieldExtension`
- `Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion`

Validation: both delivered modules compile together cleanly, with no warnings, in
about 2.3 and 7.5 seconds respectively. The two unchanged direct users of the abelian
arrow, `BoundedAllowableTorsionSmoothBaseChange` and `EtaleLocalityBaseChange`, are
checked individually against the changed definition. Edge cases covered by the
proof include n below the lower bound, negative derived degrees, the zero sheaf,
and the empty allowable-prime set (the zero annihilator witness is the positive
integer 1). The separably closed field comparison allows imperfect fields.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.boundedBelow_derived_smooth_baseChange`
(node `sbc-thm-bounded-below-derived-smooth-base-change`).

No `sorry` remains in either delivered module. Added holes: 0. Split-offs: 0.
Every new private helper is fully proved; the natural transformation is constructed
from existing canonical data. This is a proof from existing recorded dependencies,
not a claim that all dependencies have already been proved. In particular the
unchanged bounded base-change theorem, bounded-below truncation criterion, qcqs
prime-torsion theorem and allowable-torsion triangulated-closure instances remain
upstream obligations with their existing nodes. No hole is moved or renamed.

## No longer needed

All removed direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality`

The two imported naturality statements were for other coefficient interfaces. The
abelian exchange's naturality is now immediate from its constructed transformation.
Derived stalk conservativity is replaced by `DerivedCategory.isIso_iff`.
The explicit filtered-colimit torsion argument is delegated to the existing qcqs
prime-torsion node. Bounded devissage replaces the spectral-sequence filtration
step. The direct inverse-image stalk isomorphism replaces inverse-image composition
and the geometric-point global-germ construction. Some removed imports still occur
transitively through other necessary dependencies; this list does not claim that
all their modules leave the library closure.

Removed direct DAG proof edges:

- `sbc-lem-bc-naturality`
- `def-weil-pbc-derived-inverse-image`
- `lem-weil-pbc-derived-stalk-conservative`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-weil-pbc-geometric-point-pullback-stalk`
- `def-weil-pbc-inverse-image`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lemma-weil-pbc-direct-image-filtered-colimit`
- `def-weil-pbc-hypercohomology-filtrations`
- `prop-weil-pbc-inverse-image-exact`
- `lem-weil-pbc-inverse-image-composition`

A source import-closure comparison on this snapshot shows the following three
modules leave `TargetsCheck`'s closure:

- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk`

The item's own closure additionally loses
`Sheaf.CategoryTheory.RingedSiteModules`; other targets still need that module.
Its closure gains `Sheaf.AlgebraicGeometry.GeometricPointFieldExtension`, which was
already in the targets' closure. `DerivedGlobalGerm` remains in the item's closure
on the reviewed snapshot; the earlier report incorrectly listed it as removed.
All pruning is of dependencies below the blueprint unit; its bounded-to-bounded-below
truncation route is kept.

## Where the brief, the DAG or earlier work was wrong

The planned naturality dependency has a different coefficient interface from the
abelian arrow actually appearing in this statement. Its naturality can be obtained
without any new theorem obligation by assembling the same canonical arrow in the
functor category. Directly expanding the old arrow to do this causes a deterministic
kernel timeout; the constructed transformation is the required definition API fix.

The existing qcqs prime-torsion theorem tests algebraically closed fields whereas
the allowable-torsion definition tests separably closed fields. This is a genuine
interface mismatch, resolved by the existing proved field-extension stalk comparison after algebraic closure;
the existing theorem and its holder's file are unchanged.

The long spectral-sequence torsion argument and separate derived stalk detection in
the DAG are unnecessary for this proof. The already-proved bounded-devissage and
cohomological detection APIs give the same conclusions with fewer dependencies.
The original theorem statement needs no correction.


## Second reading by A4

1. **Interface: pass.** Diffed both delivered modules against the repository and
   compared the exact signature slices of every existing declaration. They are
   byte for byte identical, including all universes, the Smooth/qcqs assumptions,
   the chosen square, the allowable-torsion input and all three conclusions.
   No existing declaration is removed. The sole definition-body change is the
   abelian arrow refactor, declared in
   `coord/changes/A4-abelian-exchange-natural-transformation.md`; the new
   transformation belongs to the existing base-change definition node. Public
   imports are unchanged. Read the whole new construction: its unit is for e,
   its comparison is e/g followed by sq.w.symm followed by inverse h/f, and its
   counit is for f, exactly as before. A scratch proof checked the component
   identity abstractly for arbitrary functors, unit, comparison and counit.
   Expanding the three factors of the comparison gives the old formula. A
   concrete equality probe reproduced the old kernel timeout, supporting the
   recorded reason for this refactor. The abstract identity compiles cleanly.
   Independently recomputed the transitive downstream list; it agrees with the
   change record. Dependent targets' statement review is explicitly reopened.

2. **Proof and axioms: pass.** Compiled both modules together, in import order,
   after the review changes: 2.3 and 7.5 seconds, no errors or warnings. Scanned
   both whole files: no sorry/admit or forbidden declarations, no postponed data,
   no overlong lines. Scratch `#print axioms` of both exchange definitions lists
   only propext, Classical.choice and Quot.sound. The main theorem additionally
   lists sorryAx from its unchanged upstream obligations: the bounded theorem,
   truncation criterion, qcqs prime-torsion theorem and allowable-torsion closure
   instances. No local hole is hidden or moved. All definitions construct their
   data from canonical functors, comparisons and adjunctions.

3. **Split statements and edge cases: pass.** No split-off theorem, new hole or
   new node is delivered. Read the higher-direct-image theorem's actual field
   hypotheses, the allowable-torsion definitions, and the field-extension theorem.
   The input hypothesis restricts to algebraically closed fields; extending each
   separably closed output point to AlgebraicClosure and transporting across the
   existing additive stalk isomorphism gives exactly the required output for
   arbitrary separably closed fields, including imperfect ones. Positive
   annihilators and prime conditions are unchanged. In negative degrees the
   image is zero. Zero sheaves and an empty allowable-prime set are covered by
   the annihilator 1. For n below a lower bound the upper truncation is zero;
   neither bounded devissage nor the comparison argument assumes n >= a.

4. **Route and pruning: pass after simplification.** Read the node's proof plan,
   the `sk-rem-rest` unit record (whose realized statement/steps lists are empty),
   and all Lean declarations used for its steps. The proof still applies the
   bounded smooth-base-change theorem to tau_le_n K, uses the recorded truncation
   criterion and exchange naturality on H^n, then detects the derived
   isomorphism on cohomology. Bounded devissage and the truncation triangle supply
   the separately required allowable-torsion typing; they do not bypass a unit
   step. Searching the library for field-extension stalk results found the
   already-proved `Scheme.isIso_pointSmallEtalePrecomp_sheafFiber`, which replaces
   the duplicated private comparison proof. Used this existing theorem without
   changing its module. Removal probes identified four further redundant direct
   proof imports (PlusCompatibility, UpperLowerStar.Stalk, Point.Skyscraper and
   DerivedCategory.TStructure); the final proof compiles with all four removed
   together. The remaining four direct proof imports supply the bounded theorem,
   truncation criterion, field-extension comparison and qcqs theorem. All new
   imports are plain imports. The eleven removed old DAG proof edges are all
   listed under No longer needed. Independently compared source import closures:
   the three listed modules leave TargetsCheck; corrected the stale claim that
   DerivedGlobalGerm also leaves the item's closure.

5. **DAG: pass after repair.** Read each retained proof dependency's statement
   and declaration, including the bounded theorem's unconditional ambient
   isomorphism, the three canonical truncation maps, the plus/unbounded comparison,
   exact inverse-image cohomology and geometric stalk comparison. Each supplies
   what the proof takes from it. Updated the field-extension step to use
   `lem-weil-pbc-geometric-point-field-extension` instead of the two lift lemmas
   underlying the discarded local proof. The proof_deps list equals the union of
   step uses. The proof and proof_origin describe the actual truncation and
   devissage argument. The definition node records the new constructed
   transformation and the declared body refactor. No node statement, unit record
   or target is changed.

Changes made by this reading: replaced the duplicated stalk-comparison proof with
an existing theorem; removed its two imports and four further redundant imports;
updated the corresponding DAG step/edges and report; corrected the item-closure
pruning claim. Main theorem and all existing signatures unchanged. Closed 1 of 1
original holes, added 0, split off 0; the final delivered files contain no sorry.
