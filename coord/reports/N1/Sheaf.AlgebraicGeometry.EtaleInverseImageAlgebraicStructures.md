## What changed

Replaced the only `sorry` of
`Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures` with a complete Lean
reduction, preserving the original theorem's signature and its public imports.

The parent now proves finite-limit preservation of `Scheme.etaleSetPullback f` by
composing sheaf inclusion, left Kan extension, and sheafification. The Kan-extension
instance comes from
`WeilConjectures.Mathlib.CategoryTheory.Functor.Flat.preservesFiniteLimits_op_lan_of_flat`;
its size hypothesis is supplied by the AB5 instance for types and
`AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1}`. This works for arbitrary `f`.

Two new independent modules isolate the remaining coefficient-specific parts:
`EtaleInverseImageAbelianLift` supplies the abelian comparison, restricted hom-set
bijection, and three operation formulas; `EtaleInverseImageRingLift` supplies the ring
functor, adjunction, comparison, restricted hom-set bijection, and five operation
formulas. Neither repeats the original statement: neither asserts finite-limit
preservation, the other coefficient's lift, right-image comparison witnesses, or any
unit equation. Both take the already-proved finite-limit assertion as input.

The parent constructs both right-image comparisons by `Iso.refl`, proves their section
formulas by `rfl`, and derives both unit equations from the hom-set formulas evaluated
at identity morphisms. The private, proved helper `unit_of_homEquiv` performs the
adjunction calculation and cancellation of inverse comparison components. It has no
`sorry`. The original theorem then assembles both independent lifts and these proved
clauses. The updated parent node follows this proof.

Added proof-only imports for the AB5 instance, the large-category Kan-extension
instance, and the two new modules. The new modules import the existing generic
algebraic-object statements for the route described in their docstrings. All files
compile locally in import order; the required delivery dry run is the final validation.

## Proved and sorry left

`AlgebraicGeometry.etaleInverseImageAlgebraicStructures`: its original `sorry` is
removed, proved from the two independent lift theorems. Finite-limit preservation,
both right-image section identities, and both unit equations are proved in the parent.
`AlgebraicGeometry.unit_of_homEquiv` is a proved private helper.

The delivery leaves exactly two named `sorry` declarations, each in a new module:

- `AlgebraicGeometry.etaleInverseImageAbelianLift`, node
  `lem-weil-pbc-etale-inverse-image-abelian-lift`.
- `AlgebraicGeometry.etaleInverseImageRingLift`, node
  `lem-weil-pbc-etale-inverse-image-ring-lift`.

Each has proof exactly `:= by sorry`, a complete proof in words, source and blueprint
tag, and a corresponding node with its exact Lean signature and proof dependencies.
The parent still transitively rests on these unfinished proofs, and on unfinished
infrastructure already in the library; it is a reduction, not an axiom-free completion
of the entire inverse-image theory.

## No longer needed

Removed the parent's direct proof imports
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects` and
`Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`. They are still needed by
both new lift modules, so this is a relocation of proof dependencies, not global
pruning. The parent's direct dependence on
`lem-weil-pbc-conjugate-iso-unit-equation` is likewise deferred to the abelian lift.

No node or module is claimed to be globally unnecessary: the original route through
finite limits, algebraic objects, lifting, and uniqueness is retained. All public
imports of the original module remain because this delivery changes proofs only in
that module. The new lift modules contain no unused `R` or `Ra` local definitions and
omit the copied affine-etale import; the abelian lift also omits the ring-colimit import.

The old parent's `proof_deps` entries no longer used directly are
`lem-weil-pbc-adjunction-lifts-group-ring-objects`,
`lem-weil-pbc-sheaf-algebraic-structures-objects`,
`lem-weil-pbc-conjugate-iso-unit-equation`, and
`def-weil-pbc-abelian-etale-sheaves`. The first three are retained through the
coefficient lift nodes; the fourth describes the coefficient category in statements.
Continuity and the recorded inverse-image adjunction remain direct dependencies.
No global node pruning is claimed.

The second reading removed from the new ring module the public imports
`Mathlib.Algebra.Category.Ring.FilteredColimits` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and replaced
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients` with
`Mathlib.Algebra.Category.Ring.Limits`. The ring statement needs ring limits for
forgetting, but constructs no coefficient sheafification or abelian upper star.

## Where the brief, the DAG or earlier work was wrong

The originally recorded Mathlib presheaf-left-exactness match assumes small categories.
The chosen étale site has larger object universes than hom universes, so that exact
instance cannot prove the goal directly. The source library already supplies the
universe-compatible `preservesFiniteLimits_op_lan_of_flat`; no new finite-limit
statement or strengthening of any hypothesis is necessary.

The generic algebraic-object lemmas do not directly state the coefficient-specific
section formulas and comparison with the recorded abelian `upperStar`. Their
specialization, transport through the sheaf/internal-object identifications, and
identification of sectionwise right images are the remaining work isolated in the
new nodes. Existing `sorry` dependencies were treated as usable statements throughout.

LeanSearch returned Internal Server Error for both new-node queries; its unavailability
is recorded without a search verdict. LeanFinder, Loogle, and local grep were also run.
The local clone does not contain `literature/stacks-project/sites.tex`; the already-cited
source was checked at the Stacks Project's official pages for Tags 00YV and 00X2.

The two new statements were checked against the identity morphism, empty schemes,
zero abelian sheaves, and zero rings: no étaleness, separation, nonempty-site,
nontrivial-ring, or characteristic hypothesis was introduced. Constants use the
chosen terminal sheaf and binary operations its product projections, including in
these degenerate cases. Both retain all section and operation formulas of their
respective coefficient clauses. The parent node realizes no unit statement or step;
`dag/units/sk-def-exchange.json` has no proof steps, and its route is unchanged.

## New nodes

`lem-weil-pbc-etale-inverse-image-abelian-lift` in
`dag/nodes/sec-proper-base-change/`: the abelian specialization and comparison of
steps 4–5 of the parent, from Stacks 00YV and uniqueness of adjoints as in 00X2.
Its module is `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLift`.

`lem-weil-pbc-etale-inverse-image-ring-lift` in
`dag/nodes/sec-proper-base-change/`: the independent ring specialization of step 4
of the parent, from Stacks 00YV. Its module is
`Sheaf.AlgebraicGeometry.EtaleInverseImageRingLift`.

No definition, existing statement, target signature, or change record was altered.

## Second reading by N1

1. **Unchanged public statements: pass.** Compared the parent with the repository
   using `diff`, then compared the existing theorem signature as bytes, from
   `theorem` through the beginning of `:= by`. They agree exactly. Its original
   public imports and docstring agree; only proof imports, a private proved helper,
   and the proof body changed. No definition changed and no change record is needed.
   The other two modules and nodes are new.
2. **Proof and axioms: pass as a reduction.** Independently compiled all three files
   in import order with `lcompile.py --all`. A scratch copy printed axioms for the
   parent, helper, and both lifts: the helper uses only `propext`, `Classical.choice`,
   `Quot.sound`; the other three use those plus `sorryAx`, as reported. Inspected all
   delivered Lean for forbidden declarations and definitions containing `sorry`:
   none. The only two literal `sorry`s are exactly the named lift theorems. Read the
   helper's adjunction rewrite and checked the parent uses hom-set compatibility at
   identities, cancels comparison inverses, and chooses reflexive right comparisons.
3. **Split statements: pass.** Read both full signatures, docstrings, node statements
   and plans against the generic internal-object identification and lifted-adjunction
   statements. Each is a proper coefficient-specific part of the argument; neither
   assumes or restates the whole parent. Checked product/terminal comparison
   directions and the necessity of the hom-set compatibility. For identity scheme
   maps they reduce to the usual operations and adjunction. On the empty scheme,
   zero abelian sheaves, and zero rings the same terminal/product universal
   properties apply; no nontriviality or nonemptiness is needed. Checked the cited
   [Stacks 00YV](https://stacks.math.columbia.edu/tag/00YV) and
   [00X2](https://stacks.math.columbia.edu/tag/00X2). Repeated searches with different
   wording through `msearch.py` (LeanFinder, Loogle, grep), and searched upstream and
   local Lean. Found sheaf/module forgetful comparisons and general preservation
   of sheafification, but no theorem supplying all the displayed coefficient
   operations and restricted adjunction. Closing either lift requires substantial
   transport work; it is not a few-minute omission.
4. **Top-down route and pruning: pass after repair.** The parent actually proves
   finite-limit preservation with the universe-compatible Kan-extension instance,
   then obtains the two independent lifts and proves the remaining identities.
   Removed unnecessary imports from the new ring module as listed above. Kept the
   existing parent's public imports. Completed the list of removed direct node
   dependencies, distinguishing relocation from global pruning. Inspected
   `dag/units/sk-def-exchange.json`: the parent realizes neither its statement nor
   a proof step, and its `realized` route is preserved.
5. **DAG agreement: pass after repair.** Existing parent node changes only `proof`,
   `proof_deps`, `proof_origin`; its statement and `lean` record are unchanged.
   Checked both new nodes' source, search records, creation/blueprint/chapter/unit
   fields, Lean signatures and plans. Corrected the parent plan's Kan-extension
   identifier to `CategoryTheory.preservesFiniteLimits_op_lan_of_flat` and retained
   direct continuity and inverse-image-adjunction dependencies actually used in
   constructing the set adjunction and deriving the abelian unit equation. The
   proof-dependency list is the union of its steps' uses.

Second reading changed the ring imports, the parent's DAG dependency bookkeeping
and declaration reference, and this report's complete direct-pruning accounting.
No theorem statement or proof body needed repair. One original sorry is reduced to
zero in the parent; two independent named obligations remain, so this is not an
axiom-free completion. Final validation is the delivery dry run and server checks.
