## What changed

The original declaration `AlgebraicGeometry.Scheme.exists_etale_units_stalk_galois_equiv`
has a complete Lean proof with its signature unchanged. It uses the evaluation
homomorphism, converts its bijectivity to an additive equivalence, and proves the Galois
formula by injectivity of the separable-closure embedding and naturality of `ΓSpecIso`.
The new proof imports are
`Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluation` and
`Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationBijective`. The unused private import
`WeilConjectures.CategoryTheory.Sites.Torsor` is removed.

Three new modules refine the original geometric argument:

- `Sheaf.AlgebraicGeometry.EtaleEvaluationSeparable` proves
  `AlgebraicGeometry.Scheme.etale_evaluation_isSeparable` using the residue-field
  factorization of a field-valued point and the source-library
  `Scheme.Hom.etale_residueFieldMap`.
- `Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluation` proves
  `AlgebraicGeometry.Scheme.exists_etale_units_stalk_evaluation`. It constructs a ring
  homomorphism into the separable closure, maps units, proves restriction compatibility,
  applies `Point.presheafFiberDesc`, and removes the coefficient universe lift.
- `Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationBijective` states the remaining
  geometric bijectivity assertion, with the finite-extension/common-refinement proof
  written in its docstring and node.

There are no changes to existing statements, definitions, visibility, or public imports.
The original theorem has a declaration-scoped suppression of the unused-variable linter:
its unchanged dependent-function signature names `hτ` and `hx`, which do not occur in the
conclusion's type; both hypotheses are used explicitly in the proof.

All four modules compile together through `lcompile.py --all`, with no warnings.
The item is a decomposition rather than an axiom-free proof of the original theorem.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_etale_units_stalk_galois_equiv`
(node `lem-sc-etale-units-stalk-galois`). No direct `sorry` remains in the item's module.

Also proved both new intermediate declarations:
`AlgebraicGeometry.Scheme.etale_evaluation_isSeparable`
(node `lem-sc-etale-evaluation-separable`) and
`AlgebraicGeometry.Scheme.exists_etale_units_stalk_evaluation`
(node `lem-sc-etale-units-stalk-evaluation`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_bijective`
(node `lem-sc-etale-units-stalk-evaluation-bijective`). Its entire proof is `:= by sorry`.
It assumes only the concrete evaluation formula and concludes bijectivity; it neither
constructs the homomorphism nor assumes or concludes Galois equivariance. It is strictly
part of the original argument, rather than a renamed form of the original theorem.

Thus one upper hole is closed and one lower hole added: a decomposition with net zero
holes closed in the target import closure. The Galois compatibility, construction of the
homomorphism, and separability of evaluations are implemented in Lean.

## No longer needed

The unused private import `WeilConjectures.CategoryTheory.Sites.Torsor` is removed
from the item. All original public imports and all original node proof dependencies
(the three definition nodes) remain. No whole-library module pruning is claimed: the
removed import may still be reached by other targets. No blueprint unit statement or unit proof
step is bypassed; `dag/units/sk-thm-br.json` has no realization entry for this auxiliary
comparison. Unneeded public imports were removed while preparing the new separability
module; its final statements need only EtalePoint and AlgebraicClosure, with the
source-library residue-field theorem imported privately for the proof.

## Where the brief, the DAG or earlier work was wrong

The existing node's only proof dependencies are definitions; it supplies no theorem for
the geometric evaluation or its bijectivity. Its plan is mathematically sound, but needs
a formal construction and a separate geometric colimit argument. This delivery proves
the construction and its algebraic compatibility, and leaves the bijectivity argument
as a smaller item. The separability proof uses residue fields directly and needs no
quasi-compactness of the whole etale neighbourhood. In particular, imperfect base fields
are included; values land in the separable closure, not arbitrary algebraic-closure units.

Searches: LeanFinder returned the finite-product classification of etale algebras over a
field and related ring-homomorphism results, but no stalk evaluation theorem. Loogle
had no hit for `Scheme.ΓSpecIso` (the actual full namespace is
`AlgebraicGeometry.Scheme`). Grep of the two library roots, DAG, and Mathlib's etale-site
files found no exact evaluation comparison. LeanSearch returned Internal Server Error;
its unavailability is recorded, not treated as evidence of absence.

The cited local Stacks TeX files are absent from this machine. The primary-source online
pages [Example 03QV (2)](https://stacks.math.columbia.edu/tag/03QV) and
[03QU](https://stacks.math.columbia.edu/tag/03QU) were read without downloading files.
Example 03QV (2) identifies the units coefficient with separable-closure units and the
natural action; 03QU is the cohomology comparison, not itself a proof of evaluation.
The detailed formal arguments and the remaining bijectivity proof are recorded as
agent-written elaborations of that identification. The residue-field extension step
uses the existing finite-separable residue-field result (Stacks 02G8).

## New nodes

`lem-sc-etale-evaluation-separable`: proved. Evaluation of any global function at a
geometric lift is separable. It uses finite separability of etale residue-field
extensions and the algebra-map compatibility determined by the lift over the base.

`lem-sc-etale-units-stalk-evaluation`: proved. The additive homomorphism is constructed
from uniquely specified evaluation ring maps into the separable-closure subtype,
followed by the stalk colimit. No data is chosen from an arbitrary unproved existence
statement.

`lem-sc-etale-units-stalk-evaluation-bijective`: the only new `sorry`. Its proof separates
surjectivity (a unit lies in a finite separable subextension) and injectivity (a common
finite separable compositum detects equality of germs). Edge cases checked: arbitrary
imperfect fields, empty etale objects (there are no lifts), the identity unit, and
non-quasi-compact neighbourhoods (refine at the chosen point). No Galois clause is hidden
in this remaining statement.

## Second reading by T3

1. Compared every delivered module with the repository version. The three auxiliary
   modules are new. The existing theorem's signature is byte for byte identical,
   as are its docstring and public imports. Only its proof, private imports and a
   declaration-local linter option change; no change record is required. Verdict: pass.
2. Compiled the four files in import order with `lcompile.py --all`, without warnings.
   Scanned every Lean file for forbidden declarations and proof escapes. The only
   textual hole is the entire proof of
   `AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_bijective`. No definition
   contains a hole or selects an arbitrary unproved witness. The evaluation ring map
   is explicitly the separable-element subtype of ordinary evaluation; the stalk map
   is its compatible colimit descent. Scratch copies printed axioms for all four
   declarations: separability and evaluation use only `propext`, `Classical.choice`,
   `Quot.sound`; bijectivity and the upper theorem additionally use `sorryAx` through
   the remaining hole. Delivery also runs the maintainer's per-constant probe.
   Verdict: pass as a decomposition, subject to the stated bijectivity hole.
3. Read the bijectivity statement and its proof docstring. It concerns every additive
   map satisfying the concrete evaluation formula, with no additional geometric
   hypotheses; the formula uniquely determines the map because germ maps are jointly
   surjective and the field embedding is injective. Surjectivity uses the finite
   separable subfield generated by a unit; its inverse belongs to the same field.
   Injectivity uses finite separable components around the two lifts and their
   compositum inside the algebraic closure. Empty neighbourhoods have no lifts;
   disconnected and non-quasi-compact neighbourhoods are refined at the chosen point;
   the identity unit and imperfect base fields cause no exception. This is strictly
   the bijectivity portion, not the original existence-and-action assertion.
   Independently searched LeanFinder for the geometric fiber of the multiplicative
   sheaf, Loogle for `Point.presheafFiberDesc`, and both local library roots for
   `gmSheaf` equivalences and unit-stalk bijectivity. No existing theorem closes it.
   The related generic-point stalk comparison has different source and target; field
   sections/stalk invariants and Galois classification do not supply this evaluation
   comparison. Verified the geometric component argument against
   [Stacks 02GL](https://stacks.math.columbia.edu/tag/02GL), and the units identification
   against [Stacks 03QV (2)](https://stacks.math.columbia.edu/tag/03QV).
   The remaining formal colimit argument is not a few-minute proof. Verdict: pass.
4. Reviewed the implemented residue-field separability, explicit evaluation descent,
   and Galois action calculation from the top down. The source residue-field theorem
   is already proved, and Mathlib supplies the cocone descent. No shorter existing
   stalk comparison was found. Checked every old `proof_deps`: all three definition
   nodes are retained. The unit `sk-thm-br` has empty statement and step realization
   arrays for this auxiliary comparison; its Brauer-injection/Tsen route is retained.
   Corrected the report's missed private Torsor import removal. Verdict: pass.
5. Read all four node files against their Lean statements and proofs. Each dependency
   list equals the union of its proof steps' `uses`; the existing node records exactly
   the evaluation/bijectivity reduction and Galois calculation. New nodes have sources,
   complete proof plans, searches, creation/blueprint/chapter/unit records, and exact
   declaration records. The bijectivity node records the sole remaining hole.
   Verdict: pass.

Second reading changed the bijectivity module's imports: it now publicly imports only
Gm, GaloisUnitsCohomology and EtalePoint, which its statement needs, instead of publicly
re-exporting the evaluation theorem used only by the upper proof. The item imports
that evaluation theorem privately and directly. Updated the report to record both
proof imports and the removed private Torsor import. No mathematical statement or
proof body was changed. One original hole is closed and one smaller hole is added;
net progress in holes is zero, with the construction and action calculation formalized.
