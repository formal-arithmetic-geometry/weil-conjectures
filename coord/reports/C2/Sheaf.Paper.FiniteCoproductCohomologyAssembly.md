## What changed

Proved `AlgebraicGeometry.Etale.finiteCoproductCohomologyAssembly` with its signature unchanged.
A proved private helper `mapExt_family_bijective` establishes the general componentwise Ext
bijection by induction on degree, injective presentations, and the right-exact five lemma.
The theorem uses `sheaf_clopen_product` for full faithfulness, the coproduct universal property
to establish that the coprojections are open immersions, and the proved abelian-sheaf theorem
`injective_upperStar_obj_of_etale_addCommGrp` to preserve injectives. The product of constant
sheaf precomposition equivalences identifies the composite definitionally with `cohomologyMap`.
Updated the node proof and dependencies to this route. All new Lean is proof code.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Etale.finiteCoproductCohomologyAssembly`.
No holes added or split off. The private helper is fully proved. The existing dependency
`AlgebraicGeometry.Etale.sheaf_clopen_product` still contains its original sorry; this delivery
uses its equivalence assertion and does not claim to discharge it. Local compilation is clean.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.DerivedFiniteProduct`,
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (the latter already available publicly).
The replacement proof does not need nodes `lem-weil-pbc-derived-finite-product`,
`lem-weil-pbc-bounded-below-injectives-kinjective`, `def-sp-left-exact-additive`,
`def-weil-pbc-global-sections-functor`, `def-weil-pbc-etale-cohomology`, or
`lem-weil-pbc-module-sheaves-enough-injectives` as proof dependencies. Enough injectives is
available through the established source-library instance. Below the unused derived-product
node, this argument also does not need `Sheaf.CategoryTheory.FiniteProductInjectiveResolutions`,
`Sheaf.CategoryTheory.FiniteProductFunctorLeftExact`, or
`Sheaf.Algebra.Homology.FiniteProductCohomology` and their corresponding three nodes.
These are local pruning claims: other targets may still use these modules.

## Where the brief, the DAG or earlier work was wrong

The planned derived-product theorem states an unspecified natural isomorphism and does not
identify its coordinates with the displayed canonical cohomology maps. In addition the library
uses Ext-based `Sheaf.H`, whereas the plan uses derived global sections. The explicit Ext
induction avoids both bridges. No statement was changed or disputed.
The generic tool `lem-weil-pbc-etale-restriction-injectives` is used through its already proved
abelian-sheaf analogue; its exact-left-adjoint argument is the same. It belongs to another
unit and is needed only as this established tool. The item's unit realized list is empty,
so this change bypasses no realized unit step. Empty index types and empty components cause
no exception: degree-zero full faithfulness and coordinatewise choices cover these cases;
for a singleton the proof specializes to the single restriction equivalence.

## Second reading by C2

1. PASS: compared the delivered module with the repository using `diff` and checked the
   existing theorem signature byte for byte. The signature, original docstring, and public
   imports are unchanged; only proof imports and proof code differ. No definition or target
   statement changed, so no change record is required.
2. PASS: launcher compilation succeeds without warnings. A scratch copy with `#print axioms`
   shows only `propext`, `Classical.choice`, and `Quot.sound` for the private Ext helper and
   `injective_upperStar_obj_of_etale_addCommGrp`. The assembly theorem additionally uses
   `sorryAx`, as expected from the explicitly reported open `sheaf_clopen_product` dependency.
   The delivered module contains no `sorry`, prohibited declaration, or data definition.
   The injective presentation is chosen only within a proved proposition, from the helper's
   enough-injectives hypothesis; it introduces no data chosen from a postponed existence proof.
3. PASS: there are no split-off statements or new holes. Read the private helper completely:
   degree zero uses full faithfulness; dimension shifting uses the injective presentation,
   exactness, coordinatewise preimages, and the right-exact five lemma. Empty and singleton
   index families work without a nonemptiness assumption, and the argument covers degree zero
   as well as successor degrees. Empty scheme components introduce no extra condition.
4. PASS: searched Mathlib by alternative Ext/product patterns through `msearch.py`, and
   searched the library and upstream Ext files. Mathlib's
   `Functor.mapExt_bijective_of_preservesInjectiveObjects` handles one fully faithful functor,
   not this componentwise family; using it on the product category would also require an
   identification of its Ext groups with coordinate Ext groups. No ready-made replacement
   for that identification was found. The existing direct induction supplies it without
   additional holes. Proof-only imports are plain `import`; both remaining proof imports
   are used. All six removed original proof dependencies appear under `No longer needed`.
   Read `dag/units/sk-prop-cd.json`: no realized statement or step is removed or bypassed.
5. PASS: the existing node changes only `proof`, `proof_deps`, and `proof_origin`. Its
   dependencies equal the union of the step citations. The proof describes the actual
   open-immersion transport, proved abelian restriction theorem, Ext induction, and constant
   sheaf precomposition. Checked the latter against the definition of `cohomologyMap`:
   the composite has exactly the canonical coordinates in the target. The restriction node
   is used via its proved abelian analogue, explicitly identified in the node and report.

Second reading changed only this report, adding independent verification and the precise
axiom results. No Lean or node repair was necessary. One original hole is closed; zero holes
are added. This is a proof relative to the existing open clopen-product dependency, not an
axiom-free closure of that dependency.
