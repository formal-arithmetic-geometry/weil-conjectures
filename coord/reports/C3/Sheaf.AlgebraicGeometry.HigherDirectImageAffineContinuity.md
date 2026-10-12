## What changed

Replaced the sole sorry of
`Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity` by a compiling proof.
The theorem's signature and existing docstrings are unchanged. The proof transports
sections and equations across `eK` and `eB`, uses subtraction to turn eventual-zero
into eventual equality, constructs the filtered colimit of underlying types, and
reflects it to modules. It uses Mathlib's module filtered-colimit preservation at
the required smaller indexing universe.

Added `HigherDirectImageAffineClassDescent` and
`HigherDirectImageAffineClassVanishing`, one geometric obligation per module.
Their statements concern the actual canonical transitions; they do not take the
presentation diagram K, cocone B, or the equations hK/hB as hypotheses.
Descent asserts only existence of section representatives. Vanishing asserts only
that a specified stage section with zero limit image becomes zero later. Neither
alone supplies the colimit universal property. The main proof combines both and
handles all the arbitrary object isomorphisms of the original statement.

The node copy records this actual assembly. The unit record
`dag/units/sk-lem-failure-field.json` was checked: this item realizes no separately
locked unit statement or step. The higher-image continuity route is kept below it.

## Proved and sorry left

Hole closed by decomposition (from the two named geometric obligations):
`AlgebraicGeometry.Etale.nonempty_isColimit_higher_image_affine`.
No sorry remains in the item module.

The delivery adds exactly two sorries:
- `AlgebraicGeometry.Etale.exists_higher_image_affine_class_rep`, node
  `sbc-lem-higher-image-affine-class-descent`.
- `AlgebraicGeometry.Etale.exists_higher_image_affine_class_eq_zero`, node
  `sbc-lem-higher-image-affine-class-vanishing`.

Accounting: one existing hole closed and two new holes added; net -1. This is a
decomposition, not a complete proof of the geometric continuity theorem.

Both are public theorems with proof exactly `by sorry`, source and complete proof
in their docstrings. Neither is a definition or a restatement of the universal
property. They include every integer q and arbitrary commutative coefficients.
For q<0 all sections vanish, and any stage (or the identity transition) suffices.
The cofiltered index is nonempty; singleton identity systems reduce to the
identity map. Empty affine V and the zero ring give only the zero section. No
extra hypotheses excluding these cases have been introduced.

## No longer needed

Removed direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`.
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`.
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`.
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The first four remain proof-plan imports of the new geometric obligations;
the last is already provided by the public statement imports. No former
geometric node or module is claimed globally pruned: their arguments are still
needed below the two section lemmas. The item now has only those two proof
nodes as direct proof dependencies, plus Mathlib's elementary assembly.

The old direct proof dependencies removed from the item's `proof_deps` are:
- `lem-weil-pbc-injective-module-abelian-acyclic`.
- `sbc-lem-higher-direct-image-presheaf`.
- `lem-weil-pbc-filtered-category-exists-directed-final`.
- `lem-weil-pbc-colimit-constant-connected-diagram`.
- `lem-weil-pbc-inverse-image-composition`.
- `lem-weil-pbc-etale-cohomology-limit-complex-systems`.
- `lem-weil-pbc-sheaves-colimit-sheafification`.
- `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`.
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`.
All remain below the two new obligations; none is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The existing higher-image presheaf statement supplies an abelian sheaf
isomorphism, not a module-valued natural comparison with the specified
transitions. The complex continuity statement supplies a general abelian
cohomology cocone, not a higher-image section cocone. Their application thus
requires the module/abelian comparison and naturality described in the old plan;
these are retained in the two new geometric obligations, rather than asserted
as immediate applications.

Also, the existing injective-module acyclicity declaration uses coefficient
rings in Type u and ULift, while this item allows arbitrary rings in Type (u+1).
Its mathematical proof applies, but formal use requires a universe-compatible
comparison (or the module free-sheaf/derived-Hom route). No claim is made that
the supplied declaration directly matches the larger-universe signature.

LeanSearch returned Internal Server Error. LeanFinder, Loogle, Mathlib grep,
both library roots, and the whole DAG were searched. The second reading found
`exists_higherDirectImage_affine_section_eq_zero` in
`HigherDirectImageAffineSectionVanishing`: it concerns affine sections of abelian
higher images, requires a directed preorder and nonnegative degree, and uses
a varying coefficient diagram. It is a related intermediate theorem, not an
exact duplicate of the general module-valued section statement here. The stalk
class lemmas also require a directed index. Applying these declarations here
would still require directed reindexing, a module/abelian comparison natural for
the specified transitions, and treatment of negative degrees. Sources read online: Stacks Tags 09Z1, 03Q8 and 0738.

## New nodes

`sbc-lem-higher-image-affine-class-descent` in
`dag/nodes/sec-smooth-base-change/`: canonical section existence on affine
etale objects, with finite-cover gluing as the final step. Its module is
`Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassDescent`.

`sbc-lem-higher-image-affine-class-vanishing` in the same directory:
canonical eventual zero of a fixed stage section, with a finite cover and
separatedness as the final step. Its module is
`Sheaf.AlgebraicGeometry.HigherDirectImageAffineClassVanishing`.

No statement or definition changed, and no change record is needed.

## Second reading by C3

1. Compared the complete continuity module with the repository by `diff -u`.
   Only proof imports and the theorem body change. Its existing signature and
   docstring are byte-identical; no definition or public import changes. The two
   new modules introduce only the reported theorems. Verdict: pass.
2. Compiled all three modules in dependency order with `lcompile.py --all`:
   clean, approximately 6, 6, and 8 seconds. Read the transport through eK/eB,
   the use of hB, subtraction, hK, and forgetful-colimit reflection. No forbidden
   declaration or hollow definition occurs. Scratch `#print axioms` for all three
   declarations gives exactly propext, Classical.choice, Quot.sound, sorryAx.
   The only delivered holes are the two named geometric obligations. Verdict:
   valid assembly, conditional on those obligations; not an axiom-free result.
3. Read Stacks Tags 09Z1, 03Q8, 03FD, and 0738(2),(4). The qcqs hypotheses are
   on the composites to S; after base change to affine etale U their domains
   are qcqs. Affine transitions persist under base change. Pulling G from W
   supplies the constant coefficient system on the limit. Tag 03FD supplies
   the module-to-abelian cohomology argument without flatness. Tag 0738(4)
   supplies finite-cover gluing for descent; (2) supplies eventual equality,
   hence eventual zero. The two conclusions are strictly separate parts of
   the colimit argument. Both have proof docstrings and matching nodes.
   Tested singleton identity systems (identity comparison), empty V and zero
   ring (zero sections), and q<0 (zero higher images). IsCofiltered excludes an
   empty index. No hypothesis on S being affine is used. Repeated LeanFinder
   with "Higher direct image affine section stage representative eventual
   equality filtered cocone": only structure-sheaf limit lemmas matched.
   Loogle did not resolve the filtered-colimit name; grep found its Mathlib
   uses. Searched both library roots and the source checkout with rg and read
   the existing affine-section vanishing theorem: its coefficient category,
   index and degree differ as explained above, so it is not a direct
   replacement or a few-minute proof of the new theorem. Verdict: true,
   sourced, strictly partial obligations, with the noted formal comparisons
   still open; no complete new obligation was closed in this reading.
4. The existing geometric dependencies do not directly match the module-valued
   transition signature. The explicit 49-line assembly correctly uses the two
   smaller obligations and Mathlib's filtered-type colimit criterion; it does
   not merely apply a renamed copy of the item. The statement import remains
   public; the three assembly imports and geometric plan imports are private
   to their modules. Enumerated every former direct proof dependency above.
   Inspected sk-lem-failure-field.json: realized.statement is [] and its sole
   realized step is []; this item is not a locked realization. The higher-image
   continuity route below that unit is retained. Verdict: pass, decomposition
   only, with no global pruning claimed.
5. Matched the existing node's three proof steps to section descent, eventual
   zero, and type-to-module reflection in Lean. Its proof_deps is exactly the
   two new nodes; proof_origin names the actual assembly. Each new node's
   Lean signature, chapter, unit, source, created record and blueprint ancestor
   agree with its module and role. Their proof_deps are the union of step uses.
   Verdict: pass.

Changed the report to identify this as one hole closed, two added (net -1),
corrected the overlooked upstream affine-section vanishing theorem, and listed
all former direct proof dependencies. Corrected the new nodes' search summaries
with the same upstream finding. No Lean proof or statement needed repair.
