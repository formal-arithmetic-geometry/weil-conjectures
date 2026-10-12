## What changed

Proved the body of `CochainComplex.quasiIso_telescopeColimit`, with its signature,
definitions and all public imports unchanged. Added only the proof import
`Sheaf.Algebra.Homology.TelescopeShiftMono` and a private, fully constructed
`IsColimit` helper `telescope_cokernel`. The helper explicitly converts every
cokernel cofork to a cocone, using induction on the natural-number indexing category.
The final proof constructs the short exact sequence and applies Mathlib's
`mappingCone.quasiIso_descShortComplex`; the two canonicality identities follow
from `inr_descShortComplex` and `inl_desc`. No witness is selected from an
unproved existence theorem.

The two delivered Lean files compile cleanly with lcompile.py --all.
Second reading narrowed the new helper module's imports to the additive and
colimit constructions used by its signature; it needs neither complex nor
sheaf abelianness merely to state monicity. The DAG
copy now follows this proof. A new Mathlib leaf records the exact cone theorem.

## Proved and sorry left

Closed the original hole in `CochainComplex.quasiIso_telescopeColimit`
(node `lem-pc-complex-hocolim-colimit`). Added one hole:
`CochainComplex.telescopeShift_mono`, in
`Sheaf.Algebra.Homology.TelescopeShiftMono`
(node `lem-pc-telescope-shift-mono`). This is a decomposition, with net hole
change zero: the remaining assertion concerns only injectivity of one minus
shift, and contains no cone, colimit comparison map or quasi-isomorphism.
The cokernel universal property and the assembly into the original conclusion
are fully proved. There are no other delivered sorries.

## No longer needed

Removed no existing public imports, to preserve the existing interface.
In the new `TelescopeShiftMono` module, removed
`Mathlib.Algebra.Homology.HomologicalComplexAbelian` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`; the former is replaced by
`Mathlib.Algebra.Homology.Additive` and
`Mathlib.Algebra.Homology.HomologicalComplexLimits`, which supply subtraction
and the coproduct appearing in the statement. This prunes no existing
project module.
The node no longer needs `def-weil-abstract-derived-category` or
`lem-weil-pbc-complex-ses-triangle` as direct proof dependencies: the exact
Mathlib cone-projection theorem handles the comparison at the level of complexes.
The new Mathlib leaf still has the abstract-derived-category definition as a
statement dependency, so this is not a claim that its module is globally pruned.
No original proof-dependency module was imported and subsequently removed.
The explicit contractible-kernel construction and derived-category triangle
assembly are not needed by this proof. No claim is made that another target
stops reaching the corresponding old nodes.

## Where the brief, the DAG or earlier work was wrong

The DAG plan correctly identifies the missing injectivity argument, but its
cokernel and cone-comparison steps can be implemented directly by universal
properties and the already proved Mathlib short-exact cone theorem. No
statement or definition was changed, and no forced adaptations are necessary.

The new monicity assertion was checked on the zero diagram, zero transition
maps (where one minus shift is the identity), and diagrams whose transition maps
are not injective. Its finite triangular-matrix argument requires no monicity
of transitions. Its full proof in words uses the exact sequential colimits of
sheaves of modules supplied by `lem-pur-ringed-site-grothendieck-abelian`.
This is a generic tool from another unit, below the unit's own route; the target
unit's `realized` lists contain no binding for this telescope lemma.

Sources read: Stacks tags 0949 and 093W online (the repository's listed
literature/stacks-project/derived.tex is absent on this machine), and pinned
Mathlib HomotopyCategory/ShortExact.lean, especially descShortComplex at line 53
and quasiIso_descShortComplex at line 137. Searches were run through msearch.py:
LeanSearch was unavailable (HTTP internal server error); LeanFinder found no
one-minus-shift monicity theorem and did find quasiIso_descShortComplex; Loogle
confirmed the latter's exact type; grep confirmed its source. Blueprint searches
for one minus shift, 093W and mapping cone returned no duplicate blueprint node.

## New nodes

`lem-pc-telescope-shift-mono`: the strictly smaller remaining monicity obligation,
with its own module, complete finite-initial-sum proof in words, and Stacks 093W
as source. Its one sorry is named above.

`lem-pc-cone-short-exact-quasi-iso`: a Mathlib leaf for the canonical
cone-projection theorem already proved in Mathlib. It adds no module or hole.


## Second reading by U3

1. PASS: Compared the delivered target module with the repository using `diff -u`.
   Both public definitions, all surrounding variables, and the entire existing
   theorem signature are byte for byte unchanged. The only original theorem
   body change replaces its sorry with the reduction. The new private
   `telescope_cokernel` constructs actual universal-property data; it makes no
   choice from an unproved existence theorem. There are no statement changes
   or change records.
2. PASS as a decomposition: Compiled both modules in import order with
   `lcompile.py --all`, with no errors or warnings. Inspected every proof from
   the target downward, including successor-to-arbitrary-arrow induction in
   the cokernel cocone, its factorization and uniqueness, short exactness, and
   both cone restriction identities. The only delivered sorry is the entire
   proof of `CochainComplex.telescopeShift_mono`. Scratch copies with
   `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound` for
   the two original definitions; the two telescope theorems additionally use
   `sorryAx`. No forbidden declarations or holes in definitions occur.
3. PASS: The split monicity statement has no additional assumptions on the
   transitions and is strictly one part of the original argument. Checked
   n = 0, n = 1, zero complexes, zero transitions, and noninjective transitions.
   Projecting the finite-stage map onto its first n terms gives identity minus
   a nilpotent shift, so the proposed retraction and exact-colimit proof are
   valid. Read Stacks [093W](https://stacks.math.columbia.edu/tag/093W) and
   [0949](https://stacks.math.columbia.edu/tag/0949) and the pinned Mathlib cone
   theorem. Independent LeanFinder, Loogle, and grep searches used injectivity,
   successor maps, nilpotence, and Sigma.desc, and found no applicable telescope
   theorem. The existing private `telescope_injective` in
   `Sheaf.CategoryTheory.DerivedModuleFiltrationTelescope` concerns concrete
   module direct sums, not sheaves; transferring it would still require the
   sheaf argument. The hole cannot be closed by a short existing-lemma
   application. Its complete sourced proof and matching node suffice for
   another worker to continue.
4. PASS after import cleanup: The Mathlib short-exact cone projection is the
   direct route to the original conclusion. Every old proof dependency absent
   from the new route is listed under No longer needed. The target unit
   `sk-thm-picard-semicon` has empty realized bindings for its statement and
   step, and a search of all unit records found neither the telescope item nor
   the removed short-exact triangle dependency as a bound unit step. This
   reduction therefore bypasses no mandated unit route. Preserved the original
   public import interface. In the new module, removed the unused abelianness
   imports; the remaining imports supply structures and instances used in its
   signature (removing filtered group colimits prevents coproduct synthesis,
   and removing ring limits prevents sheaf composition synthesis).
5. PASS: Compared the original and delivered node plans, checked the new nodes'
   Lean signatures, sources, searches, provenance, chapter, unit, and status.
   The target plan follows the explicit cokernel construction, the monicity
   obligation, and Mathlib's canonical cone projection. Its proof_deps are
   exactly the union of step uses. The monicity node records its finite-stage
   argument and the already proved Grothendieck-abelian ingredient. The Mathlib
   leaf adds no hole and identifies the actual morphism used in Lean.

Second reading changed only the new module's imports and this report. No proof,
statement, definition, or node needed mathematical repair. One original hole is
closed and one strictly smaller hole is added: net zero, a decomposition rather
than a completed axiom-free proof of the item.
