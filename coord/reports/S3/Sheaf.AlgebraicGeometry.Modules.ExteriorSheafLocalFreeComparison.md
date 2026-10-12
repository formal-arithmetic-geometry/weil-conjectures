## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_local_free_comparison` in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison`, preserving its
signature, universe, visibility and both conclusions. All supporting constructions and
lemmas are private to this module and proved. The proof first constructs a natural
sectionwise exterior basis comparison, then proves that the restricted sheafification
unit is an isomorphism using local bijectivity on the over site.

Added the proof-only import `Mathlib.LinearAlgebra.ExteriorPower.Basis`. Existing
public imports stay. The second reading removed the redundant new imports
`Mathlib.CategoryTheory.Preadditive.Biproducts` and
`Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`; their APIs are already available
through the retained imports.
Updated the node's proof and proof_origin to describe the compiled proof; proof_deps stay
unchanged. No definitions or statements of existing declarations changed, and no other
modules require adaptation.

The exterior restriction calculation has a scoped 800000-heartbeat limit for elaborating
the scheme and over-site module interfaces. The unused-variable linter is disabled only
for the existing theorem because its quantified containment map `g` intentionally does
not occur in the sectionwise bijectivity conclusion; the binder is preserved verbatim.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_local_free_comparison`
(node `lem-sc-exterior-sheaf-local-free-comparison`). No holes added, no split-off
statements, and no `sorry` remains in the delivered module. This is a proof, not a
decomposition. The proof does not use any unproved project theorem.

Validation: the complete module compiles cleanly with lcompile.py in 40.6 seconds
(including the axiom probe; the prior compile took 46.3 seconds).
`#print axioms` reports exactly `propext`, `Classical.choice` and `Quot.sound`.
Import-direction checks passed for the initially added imports. The delivery dry run checks
all declarations and their axioms. Edge cases are covered uniformly: the exterior basis
and finite coproduct constructions work with an empty index set, the degree-zero
singleton index, and zero section rings; no nonzero-ring or rank bound is introduced.

## No longer needed

No existing import, proof-dependency node or module is removed. The second reading
removed two redundant imports added by the writer:
`Mathlib.CategoryTheory.Preadditive.Biproducts` and
`Mathlib.CategoryTheory.Sites.PreservesLocallyBijective`. Both steps of the existing proof
plan remain. Determinant-coordinate calculations are unnecessary glue:
naturality is checked directly on the increasing exterior basis vectors. No determinant
coordinate module is imported or added. All four existing proof-dependency nodes remain
used through their definitions or Mathlib realizations.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The DAG's local sheafification
comparison is supplied directly by Mathlib's locally bijective map APIs, rather than by
an unproved localization comparison theorem. The generic sheafification-interface node
is a Mathlib leaf and needs no new project import.

Read the increasing-wedge basis passage in Stacks Project algebra.tex,
section-tensor-algebra (Tag 00DM), and the motivating determinant inversion in
duality.tex, lemma-smooth-proper (Tag 0BRT), from the available local literature mirror.
The latter motivates the comparison but does not itself state this coordinate lemma,
as the existing node already records. The unit record `sk-thm-picard-duality` has empty
realized statement and step lists; the original local comparison route is retained.


## Second reading by S3

1. PASS: compared the delivered module with the repository using diff and checked the
   existing theorem signature byte for byte. Its universe, visibility, hypotheses,
   containment binder and both conclusions are unchanged. There are no changed public
   definitions, additional public declarations or forced adaptations. Only proof,
   private proved helpers, documentation and proof-only imports changed.
2. PASS: independently compiled the complete module cleanly with lcompile.py (48.0 s).
   Scratch copies with redundant imports removed also compiled cleanly (40.7 s and
   42.2 s), and `#print axioms` reported exactly propext, Classical.choice and Quot.sound.
   Scanned the delivered source: no sorry, axiom, unsafe, opaque, implemented_by, extern
   or kernel-check bypass. The private data are constructed using proved colimit and
   basis equivalences. Exterior restrictions use a proved unique characterization,
   rather than an arbitrary witness of an unproved existence theorem.
3. PASS: no split-off statements or new holes. Read every private helper, including the
   evaluated cofan universal property, canonical basis-vector comparison, semilinear
   naturality and local unit argument. Finite evaluation uses additivity and preservation
   of products, not preservation of arbitrary coproducts. The constructions cover rank
   zero, degree zero, degree above rank and zero rings uniformly, with no hidden
   nonzero-ring hypothesis.
4. PASS: independently searched lean/Sheaf and lean/WeilConjectures for exterior bases,
   free-sheaf evaluation and local unit comparisons, and used leanfinder with a new
   query about evaluation and canonical sections. Read the upstream
   SheafOfModules.freeSectionsLinearEquiv and sectionsLinearEquivOfIsoFree. These give
   function-valued section coordinates; replacing the present cofan route would still
   require canonical-generator compatibility and naturality, so the already proved
   direct colimit comparison is retained. The proof uses Mathlib's exterior basis and
   locally bijective map APIs directly, with no unproved project theorem. Removed both
   redundant new imports after checking compilation without them. No old proof_deps
   were bypassed; No longer needed now records the import removals. The unit
   sk-thm-picard-duality has empty realized lists; the existing local two-step route is
   preserved.
5. PASS: compared the node records. Only proof and proof_origin changed; statement,
   stmt_deps, lean signature and the remaining fields are unchanged. The recorded steps
   describe the actual basis and locally bijective restriction proof. proof_deps equals
   the union of step uses, and all four dependency ids exist and are used as definitions
   or Mathlib realizations. No new nodes or change records are needed.

Second-reading changes: removed the redundant proof-only imports of Biproducts and
PreservesLocallyBijective, corrected the report's import inventory, and appended this
review. The mathematical proof required no repair. Hole accounting remains one closed
(exteriorSheaf_local_free_comparison), zero added, zero split off.
