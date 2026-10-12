## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase` by a complete
Lean reduction, preserving its signature and every existing public import. The private
`exists_immersion_power_of_affine_cover` follows the proved source argument in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple`, extending its conclusion to
retain the isomorphism supplied by `ProjectiveSpace.twistRestrictHom`. It proves the
finite-generation, denominator-clearing, coordinate-chart and immersion steps, including
the base equation. The packaged source theorem omits the twist witness, so simply applying
that theorem would not prove this item's full conclusion.

The private `positiveTensorPower_iso_tensorPow` proves the convention comparison by
induction using the unitor and symmetry. The final proof multiplies the two positive degrees,
uses `tensorPowMulIso`, transports the twist through coordinate reindexing, and compares
`tensorPullback` with Mathlib's `pullback` by uniqueness of left adjoints. The trivial private
`closure_div_eq_top_of_eq_one` repeats the source's inaccessible private normalization step.

Added two new statement modules: `AmpleFinitePowerCover` isolates step 1, independently of
any base morphism, and `ProjectiveSpaceFiniteIndexIso` isolates finite-coordinate renaming
with compatibility for O(1), independently of any ample module. Both have named sorries,
source references and complete proofs in words. Neither restates the original conclusion.
Updated the item's DAG proof, dependencies and origin to match this route. No definition,
existing statement, target or universe changed. The file-local namespace opening was
extended for the proof helpers; its static-check classification is documented in the
change record below.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_immersion_affine_base`: its direct sorry is
removed; it is proved from the following two new statements and the existing library.
Its private helpers are fully proved. The result is a reduction, not a claim that the entire
transitive dependency closure is axiom-free; in particular the existing ample-separatedness
statement is still a dependency.

Every direct sorry introduced by this delivery:

- `AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_common_power_cover`
  (node `lem-weil-pbc-ample-finite-common-power-cover`), in `AmpleFinitePowerCover`.
- `AlgebraicGeometry.ProjectiveSpace.exists_finite_index_iso`
  (node `lem-weil-pbc-projective-space-finite-index-iso`), in `ProjectiveSpaceFiniteIndexIso`.

All three modules compile together without warnings using the prescribed local compiler.
The common-power cover explicitly includes the empty-scheme case using one zero section.
The index comparison assumes a nonempty finite coordinate type; this is supplied by the
nonempty cover index, even when the source scheme is empty. Zero base rings and empty base
schemes are not excluded. The final degree is positive by `Nat.mul_pos`.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing`: replaced by the proved
  native projective-space `homOfIsFreeGenerator` and `twistRestrictHom` construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: available through existing
  statement imports; no additional direct proof import is needed.
- `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`: available through the
  proof import of `ProjectiveSpace.OfAmple`; the cover statement imports only `ZeroLocus`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: already available through the
  existing public statement imports.

The first removed import prunes node
`lem-weil-pbc-sections-morphism-to-proj-polynomial-ring` from this item's proof route.
Its unproved polynomial-Proj construction, chart/twist comparison and sheaf-gluing
subtree are not needed through this item; this does not assert that other targets do not
use them. In particular no identification of polynomial Proj over A with the base-change
projective-space model is required.

The old route's `lem-weil-pbc-morphism-factors-through-open-subscheme` and
`lem-weil-pbc-closed-immersion-affine-cover-criterion` are not needed as separate steps:
the already-proved `isImmersion_homOfVector_divBasicOpen` and target-locality argument
supply the immersion directly. `def-weil-affine-spectrum` is not used for a separate
identification of Gamma(Spec A) with A; the source argument uses Gamma(S) over an arbitrary
affine base. These nodes were removed from the item's proof dependencies. The explicit
quasi-compactness dependency belongs to the new common-power cover rather than the item.
No unit statement or realized unit step is bypassed; this node is below the unit level.

## Where the brief, the DAG or earlier work was wrong

The planned section-morphism dependency returns a map to polynomial Proj, whereas this
item's target is the integral-model base-change projective space. The source files themselves
list the comparison between these models as unfinished work. The native projective-space
construction avoids that additional bridge. The source's proved OfAmple theorem packages
only the immersion and base equation, although its proof constructs the needed twist
isomorphism; this delivery retains that witness explicitly.

Absolute ampleness here uses germ nonvanishing loci and variable positive tensor degrees;
the source immersion construction takes finitely many section morphisms in one power,
with loci expressed using zero-locus supports. The first new statement makes that missing
conversion explicit instead of assuming the two inputs are definitionally equal.

Searches used LeanFinder, Loogle, msearch grep and local rg across Mathlib and the source.
LeanSearch was attempted twice and returned Internal Server Error; the unavailable result
is recorded, with no invented search verdict. No statement was found false. Existing
docstrings retain their original proof-plan description; the updated DAG and this report
describe the implemented native projective-space route.

## New nodes

`lem-weil-pbc-ample-finite-common-power-cover`, module
`Sheaf.AlgebraicGeometry.AmpleFinitePowerCover`, is exactly the finite common-power affine
cover step of Stacks 01VS from absolute ampleness. It includes the local rank-one
identification of germ nonvanishing with complement of zero-locus support and the empty
case, and leaves no base-change or immersion conclusion to assume.

`lem-weil-pbc-projective-space-finite-index-iso`, module
`Sheaf.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso`, is the coordinate-renaming
isomorphism of finite projective spaces, over the same base, preserving O(1). Its proof is
variable renaming on the integral model, chartwise gluing, and base change. This comparison
is separate from producing the immersion or choosing an ample tensor power.

Change record: `coord/changes/ample-immersion-affine-base-proof-opens.md` documents the
file-local addition of `Limits MonoidalCategory` to the existing namespace opening.
The preflight classifies command changes as interface changes. The record includes the
two textual users found by the prescribed downstream scan and explains why all 191
transitive importers retain the same declaration types. No user adaptation is required.
All added imports of the original module are proof-only imports.


## Second reading by C1

1. Compared the delivered original module against the repository with `diff -u` and
   checked the existing theorem signature byte for byte: identical. Existing public
   imports and docstrings are unchanged. No definition or target statement changed.
   The added lexical namespace openings have their existing change record. Verdict: pass.
2. Compiled all three modules locally, in import order, without errors or warnings.
   Independently appended `#print axioms` in scratch copies for the main theorem,
   both split statements, and all three private helpers. The helpers use only
   `propext`, `Classical.choice`, `Quot.sound`; the main theorem and split statements
   additionally use `sorryAx`, as reported for the open dependencies. Exactly two
   direct sorries remain, each the complete proof of its named public split theorem.
   No forbidden declaration, hollow definition, or concealed admission was found.
   Verdict: pass as a reduction, not as a transitively closed proof.
3. Read both new statements and their docstring proofs. The finite common-power cover
   follows from compactness, positive-degree tensor exponent laws, and the rank-one
   stalk calculation; the single zero section handles the empty scheme. Finite
   coordinate renaming preserves the structure map and O(1), including cardinality
   one, arbitrary base schemes, and the empty base. Nonemptiness of the coordinate
   type is supplied by the covering indices. Neither lemma restates the immersion
   theorem, and neither adds a condition to that theorem. Independent LeanFinder
   search for finite nonvanishing ample-section families returned affine-basic-open
   covering lemmas only; Loogle for projective-space isomorphisms returned no hits.
   Additional msearch grep and local rg checks found no exact existing replacement.
   The remaining gluing and stalk-convention arguments are not few-minute closures.
   Verdict: pass.
4. Compared the long private construction with the proved source `OfAmple` argument:
   it retains the twist witness that the packaged theorem omits. Read the final
   composition of tensor exponent, twist, coordinate renaming, pullback composition,
   and adjoint-uniqueness isomorphisms; all orientations and the base equation agree.
   The removal list covers every old proof dependency dropped: affine spectrum,
   explicit quasi-compactness (moved into the cover step), the polynomial-Proj
   section morphism, open-subscheme factorization, and the affine closed-immersion
   criterion. Inspected `dag/units/sk-thm-p1.json` and its `realized` statement and
   steps: the changed nodes are below those steps and none is bypassed. Verdict: pass.
5. Checked the three node records against their declaration signatures and the Lean
   proof. Each `proof_deps` is exactly the union of its proof steps' `uses`.
   The original statement, statement dependencies, source, and unit are unchanged;
   new nodes have the required creation, provenance, source, search, and Lean fields.
   The updated proof origin describes the implemented source construction. Verdict: pass.

Changed only the common-power cover's public import from
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` to its smaller
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus` dependency, which supplies the
zero-locus definition used in the statement; compilation confirms that no broader
import is needed. Updated the corresponding import explanation above. No proof or
statement repair was necessary. Scratch axiom copies were removed before delivery.
