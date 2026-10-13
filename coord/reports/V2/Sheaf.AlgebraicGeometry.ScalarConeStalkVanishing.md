## What changed

Proved `AlgebraicGeometry.Scheme.scalar_cone_stalk_vanishing` with its original
signature. Two proved private helpers establish global-section linearity of
homology by localization and the scalar action on module stalks by a germ
calculation. Apply the existing exactness theorem to the distinguished
triangle's homology short complex, then prove both maps zero in each case.
Added proof-only imports of `Sheaf.Algebra.Homology.ModuleStalkExact` and
`Mathlib.Algebra.Homology.ShortComplex.Linear`. Updated the existing node's
proof, proof_deps, and proof_origin to agree with this argument.

The module-stalk exactness node belongs to the proper-base-change unit and is
used as a tool: clause (5) applies to any exact module-sheaf short complex.
The item's own unit has no realized statement or steps that this bypasses.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.scalar_cone_stalk_vanishing`
(node `lem-sc-scalar-cone-stalk-vanishing`).
Both private helpers, `homology_linear` and `stalk_scalar_apply`, are proved.
No sorries remain in this module. No holes or new modules were added.
This is a proof, not a decomposition.

## No longer needed

Removed the redundant added proof-only import
`Mathlib.Algebra.Homology.DerivedCategory.Linear`: it is already exported by
`Sheaf.AlgebraicGeometry.DerivedGlobalScalar`. No original imports removed:
the existing public affine-scheme import is retained as
part of the module interface exported to its importer; the proof itself uses
no affine hypothesis. No original proof-dependency nodes or Sheaf modules
were pruned (the original proof_deps list was empty). The planned derived stalk functor,
quasi-isomorphism preservation, and stalk-complex homology comparison are
unnecessary: apply stalk exactness to the homology-sheaf sequence directly.
No nodes or modules for those constructions are imported or created.

## Where the brief, the DAG or earlier work was wrong

The original plan contained three non-elementary steps with no proof dependencies.
The updated route names the existing module-stalk exactness theorem and writes
the scalar comparison and homology linearity as fully proved local helpers.
No statement or definition was changed. Searches through leanfinder, loogle,
msearch grep, and local library/Mathlib rg found homology-sequence and linearity
machinery; no preexisting scalar-cone stalk theorem was found.

Edge cases require no extra assumptions: the input may be zero, and the
acyclic-input branch also permits scalar zero. The basic-open branch uses only
the unit germ supplied by membership, without assuming the scalar globally
invertible. An empty scheme has no point binder to instantiate.

The first dry run flagged removal of the public affine-scheme import and local
instance attributes as an interface change requiring a change record. Restored
those existing interface commands; all added imports are proof-only.


## Second reading by V2

1. PASS: compared the delivered module with the repository module using diff,
   and compared the full existing theorem signature byte for byte. The signature,
   public imports, local instance attributes, and all existing interface commands
   are unchanged. No definition or statement change, or change record, is needed.
2. PASS: compiled the final module through lcompile.py, including a scratch copy
   with `#print axioms AlgebraicGeometry.Scheme.scalar_cone_stalk_vanishing`.
   The only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
   No sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   occurs in the delivered module. Read both private proofs and both branches:
   homology linearity descends through localization; germ compatibility identifies
   precisely the scalar of the hypothesis; exactness and cancellation give the
   stated stalk vanishing without a global invertibility assumption.
3. PASS: there are no split-off statements or added holes. The two private helpers
   are proved. Checked zero scalar in the acyclic branch, zero input, negative
   degrees, and the empty scheme; none requires an additional hypothesis. Searched
   the library for homology linearity and stalk scalar action and searched Mathlib
   through msearch grep with different terms; found the short-complex linearity
   and exactness machinery already used, and no replacement for the complete
   scheme scalar/stalk comparison.
4. PASS after import cleanup: the argument takes homology sheaves directly and
   uses the proved module-stalk exactness theorem, avoiding derived stalk models.
   The original proof_deps is empty, so there are no old dependency nodes to prune.
   Inspected sk-thm-picard-duality.json: its realized statement and step lists are
   empty; this proof bypasses no realized unit step. The exactness lemma is a
   generic tool applicable to every ringed-space module short complex.
   Removed the redundant added DerivedCategory.Linear import, already public
   through DerivedGlobalScalar. Tested removal of ShortComplex.Linear too; its
   linearity instances are required, so retained that proof-only import.
5. PASS: compared the old and delivered node JSON. Only proof, proof_deps, and
   proof_origin differ; the statement and Lean signature record are unchanged.
   Each dependency occurs in the actual argument: module_stalk_exact supplies
   exactness and derived-global-scalar supplies the scalar and its linear action.
   No new nodes or modules require records.

Second reading changed only the redundant proof-only import and this report.
One original hole closed, zero holes added; no original dependency module pruned.
