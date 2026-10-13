## What changed

Proved `Algebra.pointedEtale_essentiallySmall` in
`Sheaf.RingTheory.PointedEtaleEssentiallySmall` with its signature and visibility unchanged.
Added proof-only imports `Mathlib.Algebra.Category.CommAlgCat.FiniteType` and
`Mathlib.CategoryTheory.Comma.StructuredArrow.Small`.

The proof constructs a fully faithful functor to the category of finitely generated
R-algebras with a map to K. Etale implies finite presentation and hence finite type.
The inverse on hom sets retains the same algebra map and commuting triangle.
Mathlib supplies essential smallness of finitely generated algebras, essential smallness
of their costructured arrow category, and transfer along the fully faithful functor.
Updated the existing node's proof, proof_deps and proof_origin to record this route.
No definitions, statements, public imports or existing attributes were changed.

## Proved and sorry left

Closed the sole hole: `Algebra.pointedEtale_essentiallySmall`
(node `lem-sc-pointed-etale-essentially-small`). This is a complete proof from Mathlib,
not a decomposition. Holes closed: 1. Holes added: 0. No sorry remains in the delivery.
The local single-file compile passed; the delivery dry run checks declaration axioms.

## No longer needed

The planned dependency `lem-weil-pbc-affine-etale-essentially-small-cover` is unnecessary
for this proof. Its Mathlib realization in `Mathlib.AlgebraicGeometry.Sites.AffineEtale`
is not imported. The original module contained no proof-dependency import to remove;
both original public imports remain to preserve the public interface.
There are no other planned proof dependencies and no new Sheaf dependencies.
This is pruning below the unit level: `dag/units/sk-thm-br.json` has no realized statement
or step assigned to this node, and its Brauer/Tsen route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's affine-scheme smallness dependency is an unnecessarily indirect route.
Mathlib already provides the finite-type algebra smallness and pointed-category results.
The claim is true even without the local-ring, field and separable-closure hypotheses;
all existing hypotheses were retained. The proof also handles empty pointed categories
and the zero etale algebra automatically, through the fully faithful transfer theorem.
No statement error or tool failure was encountered.

## Second reading by K1

1. Interface: PASS. Compared the sole delivered Lean module with the repository by
   diff. The complete signature of `Algebra.pointedEtale_essentiallySmall`, including
   every local-ring, field, separable-closure, algebra and scalar-tower hypothesis,
   the universe `u`, and the let-bound category, is byte-for-byte unchanged. Both
   public imports, visibility, and attributes remain unchanged. No change record
   or forced adaptation is needed.
2. Proof: PASS. Independently compiled the module without errors or warnings and
   compiled a scratch copy with `#print axioms Algebra.pointedEtale_essentiallySmall`.
   It lists only `propext`, `Classical.choice`, and `Quot.sound`. No sorry, axiom,
   unsafe, opaque, implemented_by or extern declaration occurs. The functor sends
   an object to its actual underlying algebra and pointing; finite type is a proof
   obtained from Etale.finitePresentation. Its morphism inverse is Over.homMk of
   the same algebra map, using CostructuredArrow.w. The two inverse laws and functor
   laws are checked by Lean; no data is chosen from an unproved existence result.
3. Split statements: PASS (none). There are no new declarations, nodes or holes.
   Read Mathlib's FGAlgCat finite-type skeleton proof, CostructuredArrow.essentiallySmall,
   and essentiallySmall_of_fully_faithful. Their universe parameters give precisely
   EssentiallySmall.{u}, not merely smallness in a larger universe. The construction
   requires neither nonempty objects nor a pointing of the zero ring: the zero
   algebra has no unital map into the field K and introduces no exceptional case.
4. Route and pruning: PASS. Independently searched the library for smallness of
   etale categories and used LeanFinder with the query "essential smallness of a
   full subcategory of finite type algebras with morphisms to a fixed algebra".
   Its results confirm the FGAlgCat route. No existing exact pointed theorem or
   shorter applicable route was found. Both added imports are proof-only and needed
   for their smallness instances; the original imports supply public signature
   notions. The only old proof dependency,
   `lem-weil-pbc-affine-etale-essentially-small-cover`, is completely listed under
   No longer needed. Read sk-thm-br.json: neither the unit statement nor any of
   its realized steps is this node, and its Brauer/Tsen route is preserved.
5. DAG: PASS. Compared both node files. Only proof, proof_deps and proof_origin
   changed; the statement, stmt_deps and lean signature record agree with the
   unchanged declaration. The new proof describes exactly the actual fully faithful
   functor and names the Mathlib declarations supplying finite type and smallness.
   No Sheaf proof dependency remains.

Changed only the module docstring to add its missing source and blueprint reference;
the proof needed no repair. Holes closed remain 1, holes added remain 0.

Source check: read [Stacks Tag 04GW](https://stacks.math.columbia.edu/tag/04GW).
It describes the pointed etale category via triples and proves filteredness and the
strict-henselization colimit. The old node's source-place phrase "finite-presentation
smallness paragraph" is inaccurate: there is no such paragraph in that tag. This
smallness claim is an auxiliary fact for that category, proved here by Mathlib's
explicit finite-type skeleton. This pre-existing citation imprecision does not
change the statement or proof; the source field is outside this proof-only delivery.
