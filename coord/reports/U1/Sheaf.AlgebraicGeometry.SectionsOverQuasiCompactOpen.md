## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen` without
changing its signature, universes, visibility, public imports, or existing docstring.
The proof constructs both actual Hom diagrams and both evaluation cocones. It proves the
power inclusions are mono, constructs their transition maps, checks identity/composition
and evaluation compatibility, constructs quotient transitions by `cokernel.desc`, and
proves colimit injectivity and surjectivity from stagewise kernel and lifting criteria.
No data definition is chosen from an unproved existence theorem.

Added four statement modules and their DAG nodes. `IdealPowerComplement` is proved:
it constructs the open as the union of neighborhoods on which 1 lifts; a germ argument
identifies this with the surjective-stalk locus. The existing proved
`ideal_module_product_stalk` and Mathlib's sectionwise bijectivity criterion prove that
all powers have bijective sections on this open. The other three modules isolate the
geometric steps still needing formalization. Their statements are strictly parts of the
argument and contain no colimit-comparison or diagram-existence conclusion.

All five modules compiled together in import order. The item compiles without warnings.
Updated the existing node's proof, proof_deps and proof_origin to match the implemented
argument. The unit's realized statements/steps are preserved; this decomposition is
below the unit level. Added proof imports of the four new modules, Grp.FilteredColimits
and ConcreteCategory.Basic. In particular the filtered-colimit preservation instance
is explicitly shrunk to index universe zero for the diagram indexed by naturals.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.sections_over_quasiCompact_open`
(node `lem-weil-pbc-sections-over-quasi-compact-open`).
This is a decomposition, not an axiom-free proof of the entire geometric theorem.

Also proved the new declaration
`AlgebraicGeometry.Scheme.ideal_power_complement`
(node `lem-weil-pbc-ideal-power-complement`), without adding a hole.

Three holes added, each the complete proof of one public theorem in its own module:

- `AlgebraicGeometry.Scheme.ideal_power_evaluation_eventually_zero`
  (`lem-weil-pbc-ideal-power-evaluation-eventually-zero`): finite affine eventual vanishing.
- `AlgebraicGeometry.Scheme.ideal_power_annihilator_system`
  (`lem-weil-pbc-ideal-power-annihilator-system`): actual annihilator subsheaves,
  quasi-coherence, increasing inclusions, and triviality/isomorphisms over a unit open.
- `AlgebraicGeometry.Scheme.ideal_power_quotient_local_lifting`
  (`lem-weil-pbc-ideal-power-quotient-local-lifting`): stagewise eventual zero and section
  lifting through annihilator quotients using finite affine overlap gluing.

No sorry remains in the item's module or its private helpers. Net holes for this
transaction before any closure pruning: one closed, three added. Edge cases checked
mathematically: empty X/U, zero ideal, unit ideal, n=0, zero module, and no generators.
Degree zero uses the identity power, its annihilator is zero. A zero ideal has empty
complement and positive powers zero. A unit ideal has zero annihilators and ordinary
section evaluation. Arbitrary annihilator presentations are pinned by their range on
all opens; mono presentations are equivalent over F and do not add a hidden hypothesis.

## No longer needed

Removed these eight direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
  (`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`).
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
  (`lem-weil-pbc-quasi-coherent-module-cokernel-image`).
- `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`
  (`lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`).
- `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`
  (`lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`).
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
  (`lem-weil-pbc-quasi-coherent-finite-type-affine`).
- `Sheaf.AlgebraicGeometry.SectionsAnnihilatedByIdeal`
  (`lem-weil-pbc-sections-annihilated-by-ideal`).
- `Sheaf.Paper.SectionsOverQuasiCompactOpen`
  (`lem-weil-pbc-sections-over-quasi-compact-open-in-affine`).
- `Sheaf.Topology.GlueSheavesOfModules`
  (`lem-weil-pbc-glue-sheaves-of-modules`).

The zero-set-affine lemma is unnecessary for the new complement proof: its local lifting
and stalk calculations are written directly. The existing affine comparison module is
not needed anywhere in this delivery's proof plan; the source's actual denominator and
monomial argument is used instead of its unusable Lean signature. The remaining six
removed imports are unnecessary in the item's combining proof but some remain relevant
as planned prerequisites of the three new holes, as explicitly recorded in their DAG
proof_deps. This report does not claim those modules are globally unreachable or that
their underlying mathematical facts are dispensable to those future proofs.

No public import was removed. No module realizing a unit statement or unit proof step
was bypassed.

The complete list of old direct `proof_deps` absent from the new combining proof is:

- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
- `lem-weil-pbc-affine-open-spec-points`.
- `lem-weil-pbc-quasi-coherent-finite-type-affine`.
- `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`.
- `def-pc-scheme`.
- `lem-weil-pbc-module-restriction-open-immersion-colimits`.
- `lem-weil-pbc-affine-tilde-gamma-adjunction`.
- `lem-weil-pbc-spec-module-tilde-sections`.
- `lem-weil-pbc-sections-over-quasi-compact-open-in-affine`.
- `def-weil-sheaf-of-modules-category`.
- `def-weil-pbc-quasi-compact-scheme`.
- `lem-weil-pbc-filtered-colimit-modules-elementwise`.
- `lem-weil-pbc-glue-sheaves-of-modules`.
- `lem-weil-pbc-sections-annihilated-by-ideal`.
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`.
- `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`.

These are direct DAG dependencies removed, not a claim that all their modules are
globally pruned. The filtered-colimit representatives now come directly from Mathlib.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the imported affine theorem
`AlgebraicGeometry.sections_over_quasiCompactOpen_of_affine`
in `Sheaf.Paper.SectionsOverQuasiCompactOpen` claims an injective function on the sigma
of maps from all stages and a bijection on the corresponding quotient sigma. This is
not the colimit statement of Stacks 01PM. There is an elementary counterexample to its
written Lean signature: take A=Z, M=0, I=top, D=top, and N_n=0. The section group is a
singleton, while the domain sigma has distinct elements at n=0 and n=1 (the zero maps).
Thus no injective c can exist. Even evaluation itself has duplicate zero representatives
at every stage for nonzero M. This delivery does not use that false declaration and
makes no edits to its module, held outside this item. The maintainer should mark/repair
that declaration and review its other users. The correct source is the colimit map.

The original step-1 prerequisites and annihilator lemma take `IdealSheafData`, whereas
this item's inclusion is an arbitrary mono quasi-coherent module into the unit sheaf.
There is no supplied identification transporting that inclusion, its powers, and its
annihilators to `IdealSheafData`. The new complement proof avoids that missing bridge;
the new annihilator-system node states the needed result directly for this encoding.

The source tex is absent in this machine's read-only repository. The actual source
statements and proofs were read at the Stacks 01PQ and 01PM pages, recorded in the
nodes. LeanSearch was attempted and returned HTTP 500; it is recorded as unavailable,
not as a negative search. LeanFinder, Loogle and source grep also ran. Searches of the
entire imported blueprint found no matching annihilator or sections-comparison node.

## New nodes

`lem-weil-pbc-ideal-power-complement`:
`Sheaf.AlgebraicGeometry.IdealPowerComplement`, proved local unit-lifting construction
and all power section bijections. This is strictly the geometric setup, without F,
annihilators, diagrams or colimits.

`lem-weil-pbc-ideal-power-evaluation-eventually-zero`:
`Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero`, the finite-cover
stagewise kernel criterion. This does not construct or compare colimits.

`lem-weil-pbc-ideal-power-annihilator-system`:
`Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorSystem`, annihilator family construction
and its quotient restriction, with quasi-coherence information needed downstream.
This has no compactness assumption and no comparison-diagram conclusion.

`lem-weil-pbc-ideal-power-quotient-local-lifting`:
`Sheaf.AlgebraicGeometry.IdealPowerQuotientLocalLifting`, two stagewise criteria on a
specified annihilator system, from the finite-cover and overlap argument in 01PQ and
the actual denominator/monomial proof in 01PM. It neither chooses the annihilator
family nor constructs the Hom diagram. The item performs the entire categorical
assembly and both comparison proofs.

No interface change record or forced adaptation was required.

## Second reading by U1

1. PASS: Diffed the existing module against the read-only repository and checked its
   declaration table. The existing theorem signature, universes, visibility, public
   imports and docstring are unchanged. Only proof code, private helpers and proof
   imports change. The existing node changes only proof, proof_deps and proof_origin.
2. PASS: Independently compiled all five modules in import order with lcompile.py,
   with no errors or warnings. Searched all delivered Lean for forbidden declarations
   and sorry. The only three sorries are the reported public named helper theorems;
   there are no hollow definitions. A scratch copy with #print axioms for all five
   public theorems gives only propext, Classical.choice and Quot.sound for
   ideal_power_complement, and those plus sorryAx for the other four declarations.
   homDiagram is an explicit construction. The choices of r and one are determined
   by their mono/bijective inclusions, and the annihilator presentations are fixed
   up to unique isomorphism over F by their ranges on every open.
3. PASS: Read each new statement and its docstring, compared with Stacks 01PQ/01PM,
   and tested empty X/U, zero/unit ideals, degree zero and zero F mathematically.
   The annihilator theorem states only the subsheaf system, the eventual-zero
   theorem only a kernel criterion, and the quotient theorem only the two stagewise
   criteria. None duplicates the item. Independent LeanFinder search for extension
   away from a vanishing locus found structure-sheaf localization lemmas, not these
   module statements. Loogle confirms the sectionwise stalk-bijectivity lemma already
   used. Mathlib/upstream/project grep and inspection of SectionsAnnihilatedByIdeal
   found only the existing IdealSheafData formulation, which needs a bridge to this
   arbitrary mono encoding. No few-minute proof closes any of the three geometric holes.
4. PASS after repair: Read the categorical assembly from the target downward: mono
   cancellation establishes coherent r; cokernel epi cancellation establishes q;
   evaluation gives natural cocones; Mathlib representatives and the two stagewise
   criteria prove the colimit claims. No unit statement or realized proof step in
   dag/units/sk-thm-p1.json is bypassed. Removed unused public QuasiSeparated imports
   from Complement, AnnihilatorSystem and EvaluationEventuallyZero; those modules
   compile without them. Expanded No longer needed to list every old direct DAG
   dependency removed. These are direct dependencies, not global closure-pruning claims.
5. PASS after repair: Checked every new node's source, creation, Lean declaration,
   chapter/unit, statement, proof steps and dependency union. The complement node
   follows the actual germ/stalk proof. The three open nodes record the intended
   geometric arguments. Removed the old project filtered-colimit module-elementwise
   node from the item's proof_deps and proof-step uses: the actual proof uses
   Mathlib Concrete.colimit_exists_rep with AddCommGrpCat filtered-colimit preservation.

Second reading changed only three unused public imports, the item's filtered-colimit
DAG dependency description, and report completeness. No theorem statement or proof
body was changed. The result remains a decomposition: one original hole closed,
three geometric holes added, and the complement helper proved with standard axioms.
