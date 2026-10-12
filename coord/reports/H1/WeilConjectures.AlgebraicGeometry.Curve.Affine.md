## What changed

Replaced both original sorries in `WeilConjectures.AlgebraicGeometry.Curve.Affine` without
changing any existing signature or definition. Added three proof-only imports.
The second reading narrowed public imports to the definitions and instances needed by
statements, and made six existing imports proof-only.

`exists_addEquiv_pic_quotient` now chooses the smooth compactification, constructs the
Jacobian and its `IsJacobian` instance from the existing representability theorem, and applies
`Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient`. The boundary generating set is finite:
closed boundary points inject into the finite boundary, and each point determines at most
one degree-zero Picard class. `AddSubgroup.fg_iff` proves finite generation of its closure.

`subsingleton_sheafH_two_lowerStar` now uses a finite-stalk filtered presentation and proves
that its second-cohomology diagram consists of zero objects. It supplies the existing
normalization theorem and constant-sheaf vanishing theorem to the finite-stalk step, then
uses `IsColimit.isZero_pt` and `Functor.isZero` to conclude. The two substantial remaining
parts of the original argument are public theorems in separate new modules, each with its
own DAG node, source and proof in words. This is a finite-case/filtered-colimit reduction;
neither new theorem restates arbitrary-torsion second-cohomology vanishing.

Updated the proof fields of `lem-sc-pic-affine` and `lem-sc-affine-generic-second` to match.
Single-file and sandbox compilation passed without warnings.

Repair of return X-3e0c3: restored the stated proof-dependency imports in both new
sorry-bearing modules. Added PicAffineBaseChangeCompatibility to the change record
and corrected the direct-importer count to six in the record and second reading.

## Proved and sorry left

Both original sorries were replaced by complete combining proofs:

- `AlgebraicGeometry.IsConnectedCurve.exists_addEquiv_pic_quotient` uses the existing
  sorry-backed `AlgebraicGeometry.IsConnectedCurve.pic_affine_quotient` of node
  `lem-sc-pic-affine-quotient`. That existing declaration is not changed by this delivery.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar` uses the two new
  obligations below and the already proved normalization and constant-coefficient results.

No sorry remains in the item's module. Exactly two new sorries remain:

- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_finite_stalk`,
  node `lem-sc-affine-generic-finite-second`, in
  `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond`.
- `AlgebraicGeometry.Scheme.exists_generic_torsion_finite_stalk_cohomology_colimit`,
  node `lem-sc-generic-torsion-finite-stalk-colimit`, in
  `Sheaf.AlgebraicGeometry.Curve.GenericTorsionColimit`.

These are reductions through named theorems with sorry, not axiom-free closure of the
transitive dependency graph. Edge cases checked in stating the new lemmas: the zero finite
module admits the empty filtration; the zero torsion module has the zero stable subgroup
as an index; arbitrary torsion stalks need not be finite or of scheme-sized cardinality;
primary decomposition occurs only in the finite case. The colimit lemma has no smoothness,
curve-dimension, or vanishing assumption.

## No longer needed

The three added imports in Affine are used only in proofs. Six existing proof-only
imports are now plain imports: AbelianVariety.Final, Curve.SerreDuality,
GlobalSectionsBijective, Regular, Sites.ArtinSchreier, and Sites.GmPicard. Explicit public
imports of AbelianVariety.Basic and QuotientGroup.Basic provide the types
and instances that the unchanged statements need.

In GenericFiniteSecond, removed the redundant EtalePoint import and replaced ArtinSchreier
with Sites.Kummer, which defines constantZMod. In GenericTorsionColimit, replaced the unused
Sites.CohomologyColimit import with SheafCohomology.Basic and the Grothendieck sheaf/Ext
instance imports required to elaborate Sheaf.functorH in the statement.

For this argument, `lem-exc-field-discrete-modules` and its module
`Sheaf.AlgebraicGeometry.FieldDiscreteModules` are no longer needed: the new steps use
`lem-exc-abelian-sheaves-gmodules` directly for abelian sheaves, without choosing a finite
coefficient ring. No claim is made that another target branch stops using that module.

The old `lem-weil-pbc-cohomology-filtered-colimit` is also no longer needed for this
argument: the existing coefficient-sized `lem-weil-pbc-etale-directed-cohomology-colimit`
supplies precisely the directed-colimit comparison at universe u+1.

All remaining old proof dependencies of `lem-sc-affine-generic-second` remain needed, either
as explicit inputs from Affine or inside the finite-stalk and colimit obligations. Moving
them under those obligations is not pruning them. The boundary quotient, compactification,
Jacobian, abelian-variety estimate, and divisible-quotient torsion nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

The original generic-second proof described the union of finite stable submodules and the
passage through direct image and cohomology as elementary. The existing declarations do
not assemble this cocone. The new colimit obligation makes the required canonical maps and
colimit property explicit. Its index is allowed in universe `u+1`, the universe of the
geometric stalk. The existing stated cohomology filtered-colimit theorem uses an index in
universe `u` and derived global sections, whereas this step needs `Sheaf.functorH`; the second reading found an existing directed-colimit declaration at the coefficient
universe, `Scheme.etaleCohomology_isColimit_of_isDirected`. The new obligation should use
that declaration and the natural Ext/derived comparison, rather than repeat the qcqs proof.
It cannot merely apply the smaller-index filtered-colimit signature.

The finite-module step takes the normalization and constant-sheaf results as explicit
inputs. This avoids a module cycle: those two results live in the importing Affine module.
Its remaining task is the trace/filtration argument for finite stalks, not their geometric
construction or the constant case.

The unit's route is retained. New generic tools used in the colimit obligation are
`lem-exc-etale-sheaves-gsets-point` (generic-fibre sections as invariants) and
`lem-weil-pbc-sheafH-ext-derived-comparison` (naturality for `Sheaf.H`). The open-subgroup
fixed-field theorem supplies the field extension corresponding to the Sylow subgroup.
No chapter or unit record was changed.

## New nodes

`lem-sc-affine-generic-finite-second` packages proof paragraphs 1--3 of
`lem-sc-affine-generic-second`: finite primary decomposition, prime-to-ell trace retraction,
finite pushforward and induction on a trivial-quotient filtration. Its hypotheses include
the existing normalization and constant-vanishing inputs, both supplied by the main proof.
The statement is restricted to finite geometric stalks.

`lem-sc-generic-torsion-finite-stalk-colimit` packages paragraph 4: finite stable subgroups
of a torsion Galois module, transport to sheaves, generic direct image and filtered-colimit
cohomology. It applies in every degree on a qcqs integral scheme and asserts a presentation,
with no cohomology vanishing conclusion. Both nodes inherit `sk-prop-cd-affine` and cite the
original blueprint proof. No definition or statement change record is needed.

## Earlier second reading (a previous round; superseded)

1. Compared Affine with the repository version and checked the declaration table: every
   existing signature and definition is byte-for-byte unchanged. Only proof bodies and
   import visibility changed. The two new modules introduce precisely their named
   statements. No statement or definition changed. The public-import cleanup has its own change
   record, coord/changes/Affine-proof-imports.md; all six direct importers compile
   against the sandbox Affine.
2. All three modules compile locally without errors or warnings. Searched every delivered
   Lean file for forbidden declarations and sorry: exactly the two named split theorems
   remain, with no hollow definition. A scratch copy printed axioms for all six Affine
   declarations and both new theorems: only propext, Classical.choice, Quot.sound and
   sorryAx occur. normalizationIn has no sorryAx; other declarations still depend on
   open upstream proofs, as the report states.
3. Read both split statements and their docstring proofs against the DAG. They are true
   reductions, rather than restatements of arbitrary-torsion vanishing. Checked zero
   stalks, empty filtrations, prime-to-characteristic and characteristic-primary parts,
   degree-zero cohomology, and a zero generic sheaf. A finite torsion Galois orbit
   generates a finite stable subgroup, and the index universe matches the coefficient
   universe. Fresh LeanFinder, Loogle and Mathlib grep searches, plus rg in Sheaf and
   WeilConjectures, found no duplicate of either combined statement. They did reveal
   the existing coefficient-sized directed-cohomology theorem, now cited in the colimit
   node and docstring. Closing either remaining geometric obligation needs substantial
   sheaf/Galois constructions, so neither can be finished in a few minutes.
4. Read the quotient proof from compactification through the Jacobian and finite boundary
   generators, and the zero-colimit proof from the target downward. Both take genuine
   reductions through the existing declarations. Corrected proof-only public imports
   and narrowed imports in the new modules. No longer needed now identifies both
   pruned old nodes; every other removed immediate dependency moved into one of the
   split nodes. The unit's route is retained; its existing realized field is empty
   and no unit record was changed.
5. The original nodes change only proof, proof_deps and proof_origin; their union-of-uses
   fields match the proof steps. Checked the new nodes' source, statement dependencies,
   creation record, blueprint origin, chapter/unit, searches and verbatim Lean statement.
   Repaired the colimit node's last step and dependencies to cite the existing directed
   theorem at the required universe and the natural Ext comparison.

Changed by this reading: import visibility and narrower imports; the colimit docstring and
DAG now reuse the existing coefficient-sized directed-colimit theorem; updated this report
and pruning list. Existing statements, definitions and combining proof bodies were preserved.
Curve.Kummer remains public because direct-importer compilation showed its exported
primitive-root theorem and constant-sheaf comparisons are needed downstream. The import
change record is coord/changes/Affine-proof-imports.md.

## Second reading by H1

1. Compared the delivered Affine module with the repository version. Existing declaration
signatures and definitions are unchanged byte for byte; only proof bodies, import visibility,
and the two explicitly recorded new declarations differ.

2. Compiled all three delivered modules with `lcompile.py --all`. They compile without errors
or warnings. The only remaining `sorry`s are the two named split theorems, with no hollow
definitions or forbidden declarations. Their axioms are limited to the permitted axioms plus
`sorryAx` inherited by those split statements.

3. Read both split statements and their docstrings and checked edge cases including zero
finite stalks, empty filtrations, prime-to-characteristic trace steps, and zero torsion. They
are genuine reductions and do not restate the arbitrary-torsion target. Searches in Mathlib,
Sheaf, and WeilConjectures found no duplicate declarations.

4. Checked both combining proofs from their imported normalization, compactification, Jacobian,
finite-stalk, and colimit inputs. The proofs use the shortest available existing constructions;
proof-only imports are plain imports and unused dependencies are listed above. The unit route
and its realized record are preserved. The colimit split uses the coefficient-sized directed
cohomology theorem and the finite-stalk split carries the normalization and constant-sheaf
inputs explicitly.

5. Checked that the original nodes' proof, proof dependencies, and proof origins match the Lean
proofs, and that each new node has a matching verbatim Lean statement, source, blueprint,
creation record, chapter, and unit. No target statement or definition was changed.

Changed by this second reading: added this required review section; no Lean or DAG changes were
needed after the previous repair.
