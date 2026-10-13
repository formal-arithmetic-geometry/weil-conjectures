## What changed

Proved `AlgebraicGeometry.Scheme.scalar_unit_abelian_comparison_bijective` in
`Sheaf.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily` without changing any existing
signature, visibility, definition, or public import. Added proved private helpers for the
Ext comparison, evaluation at one, degree-zero bijectivity, compatibility with Ext composition,
forgotten-injective vanishing, and the degree-one diagram chase. The only added import is the
proof import `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`.

The shorter route is the degree-one dimension shift in [Stacks Tag 03FD](https://stacks.math.columbia.edu/tag/03FD).
For `0 → F → I → Q → 0` with I injective, compare module Ext from the unit and abelian Ext
from the constant integers. The degree-zero comparison evaluates at 1 and is bijective.
Exact forgetting and Ext composition preserve both squares. Injective vanishing on the
module side and the existing forgotten-injective acyclicity theorem on the abelian side
make the two diagram chases prove bijectivity in degree one. Finally compose with
`moduleExtEquiv`, using only its additive-equivalence bijectivity.

Updated the item's `proof`, `proof_deps`, and `proof_origin` to this route. Registered the
generic Mathlib covariant Ext exactness theorem as a new leaf because the existing
`lem-weil-pbc-ext-long-exact-second-variable` only states its ring-module specialization.
The existing `lem-weil-pbc-ext-covariant-boundary-exact` leaf is also explicitly reused for
the kernel-image lift at the cokernel term. No new Lean module or unproved intermediate
theorem is added. The blueprint unit's cube
statement and its realized route are untouched.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.scalar_unit_abelian_comparison_bijective`
(blueprint `new-sc-scalar-unit-comparison-family`).

No `sorry` remains in the delivered Lean module. No hole was added, and no statement was
split off. Every private helper is proved. This closes the item from existing dependencies;
it does not assert that the transitive import closure is already sorry-free. In particular,
`moduleExtEquiv` still comes from the existing `exists_moduleExtEquiv` theorem.

The complete module compiled cleanly with lcompile.py. The construction requires no
nonemptiness hypothesis: global-section evaluation at the top open and the injective/cokernel
sequence apply also to the empty scheme and zero coefficient modules. No hypotheses on the
characteristic, finiteness, or separatedness were introduced.

## No longer needed

No imports removed and no original proof-dependency node pruned; all three original
proof-dependency modules/nodes remain used. Thus actual import/node pruning is none.

The full common-resolution identification, and the cocycle characterization in
`exists_moduleExtEquiv`, are not needed by this proof. The existing field-linear operations
module remains necessary for the definition and for `moduleExtEquiv`. No new common-resolution
normalization lemma is created or imported. The unrelated arbitrary natural comparison
modules `Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural` and
`Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree` are not needed or imported by the new proof;
this is not a claim that they leave the targets' overall closure.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original full-resolution plan was sufficient in principle,
but stronger than needed in degree one. The direct Ext diagram chase avoids identifying
an arbitrarily chosen natural isomorphism with the explicit comparison.

`injective_module_abelian_acyclic` concludes vanishing for `Sheaf.H'` at an object, whereas
the item uses global `Sheaf.H`. The proof explicitly constructs the required isomorphism
between the free abelian representable of the top open and the constant integer presheaf,
sheafifies it, and transports Ext vanishing. It does not assume these cohomology conventions
are definitionally equal.

The local blueprint-ancestor helper returns None for this item's module-based creation
chain. The new Mathlib leaf uses the recorded ancestor `thm-sc-theorem-of-cube` and route
from the existing parent node `lem-sc-scalar-unit-cohomology-pullback-comparison` instead.
No existing blueprint fields were changed. Second reading found that the generic
`covariant_sequence_exact₃` clause was already recorded by
`lem-weil-pbc-ext-covariant-boundary-exact`; its reuse is now recorded in `proof_deps`.
The full six-term Mathlib leaf remains distinct and supplies `covariant_sequence_exact₁`.

## New nodes

`lem-sc-abelian-ext-covariant-exact`, at
`dag/nodes/sec-abelian-varieties/lem-sc-abelian-ext-covariant-exact.json`, records the existing
Mathlib `CategoryTheory.Abelian.Ext.covariantSequence_exact` and its witness forms used by
the proof. It is the six-term exact window for any abelian category with small Ext,
not restricted to ModuleCat over a ring. Source: [Stacks Tag 06XP](https://stacks.math.columbia.edu/tag/06XP),
paragraph after Lemma 13.27.3. Loogle and LeanFinder matched it, source grep verified the
signatures, and LeanSearch was attempted but returned Internal Server Error. Blueprint
search found no arbitrary-abelian-category version; the existing ring-module version
cannot be applied to the category of sheaves of modules. This node introduces no Lean
file, no definition, and no sorry. There are no change records because the public interface
is unchanged.


## Second reading by Q3

1. Interface preservation: PASS. Read the complete repository/sandbox diff. Both existing
   declaration signatures, the complete `scalarUnitAbelianComparison` definition, visibility,
   docstrings, and public imports are byte-for-byte unchanged. The sole added import is plain
   `import` and needed for the proof. There are no adaptations or change records.
2. Proof and trust: PASS. Compiled the delivered file cleanly with `lcompile.py` (34 seconds).
   A scratch copy with `#print axioms` for both public declarations and all six private
   helpers compiled cleanly (32 seconds). All private helpers use only `propext`,
   `Classical.choice`, `Quot.sound`. The two public declarations additionally use `sorryAx`
   through the existing `exists_moduleExtEquiv`; no new hole or forbidden declaration exists.
   The private comparison is constructed explicitly. The inherited choice of `moduleExtEquiv`
   is permitted: its cocycle formula fixes its value on every homology class, since every
   class is represented by a cycle and unit morphisms represent all global sections.
3. New statements: PASS. No sorry statement is split off. Read every proved helper and the
   new Mathlib leaf against the source theorem. Degree zero is evaluation at one; the two
   boundary squares commute by Ext composition and exact forgetting. The diagram chase
   uses both injective vanishing assertions in the correct categories. The empty scheme,
   zero coefficient module, and split short exact sequences introduce no exception. Loogle
   (`unitHomEquiv`), LeanFinder (acyclic injective comparison), and broad source/DAG searches
   found no shorter explicit-map theorem. Found and reused the existing exact₃ DAG leaf.
   The new six-term leaf includes exact₁ and is therefore distinct. Verified its source in
   [Stacks 06XP](https://stacks.math.columbia.edu/tag/06XP) and the comparison argument in
   [Stacks 03FD](https://stacks.math.columbia.edu/tag/03FD).
4. Route and pruning: PASS. This is the direct degree-one dimension shift below the unit
   level. All three original proof dependencies remain used; none is omitted from
   `## No longer needed`. The public imports are used by the existing exposed definition,
   including exact forgetting from the sheafification module. The plain acyclicity and
   exact-sequence imports are necessary. Read `dag/units/sk-prop-av-cube.json`: its statement,
   step and `realized` fields are untouched; no cube-level step is bypassed. The explicit
   free-abelian-representable/top-open isomorphism correctly transfers H' to H.
5. DAG agreement: PASS after repair. Compared the original and delivered nodes: only the
   owned proof fields changed. The four proof steps describe the actual helpers and final
   composition; `proof_deps` equals the union of their uses. The new leaf has its source,
   self-contained statement, searches, origin, creation, blueprint ancestry, unit/chapter,
   and existing Mathlib Lean record. Its generality matches Mathlib's arbitrary abelian C.

Second-reading changes: added the existing covariant-boundary exactness leaf to the item's
proof step and dependency list, documented that reuse in the report and new leaf's searches,
and recorded this review. No Lean proof, definition, signature, or import was changed.
One original hole closed, zero holes added, zero split off; pruning none.
