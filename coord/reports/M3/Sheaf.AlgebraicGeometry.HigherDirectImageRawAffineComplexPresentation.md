## What changed

Closed the local hole in
`AlgebraicGeometry.Etale.exists_raw_affine_complex_presentation` by a compiling decomposition
of the source argument. Its signature, the presentation inductive and every existing public
import remain unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.RawRestrictedCohomologyNaturalIso` and
`Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystem`.

The new module `Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology` constructs five actual
objects/maps: `rawAffineComplexPullback`, `rawAffineRestrictedCohomology`,
`rawAffineRestrictedMap`, `rawAffineRestrictedCoefficient` and
`rawAffineRestrictedCohomologyMap`. The first formula is exactly the presentation's prescribed
hP equation. The restriction map is a pullback map; its coefficient map uses both inverse-image
composition comparisons and the original coefficient morphism. Nothing is chosen from an
unproved existence theorem, and no definition contains a hole.

The geometric lemma realizes source steps 1 and 2 using restricted single-complex cohomology.
It has no raw-Hom group in its statement and fixes both the lower bound to zero and the
cohomology pullback to the actual canonical definition. The independent natural-comparison
lemma realizes step 3 for every morphism and coefficient map, without affine, qcqs, directed
system or limit hypotheses. The parent proof composes the two sets of additive isomorphisms,
constructs the full presentation, proves hP by reflexivity and proves compatibility by the
geometric leg equation followed by comparison naturality under the limit isomorphism.
Updated the parent node's proof, proof_deps and proof_origin to reflect this Lean argument.

## Proved and sorry left

Closed one original local hole:
`AlgebraicGeometry.Etale.exists_raw_affine_complex_presentation`
(node `lem-sbc-higher-direct-image-raw-affine-complex-presentation`). No sorry remains in the
item module. This is a decomposition, not a completed axiom-free proof of the mathematical
result: two lower obligations were added, so holes closed minus holes added is -1.

The only new holes, each a public theorem with source and full proof in its docstring, are:

- `AlgebraicGeometry.Etale.exists_raw_restricted_cohomology_natural_iso`
  in `RawRestrictedCohomologyNaturalIso.lean`, node
  `lem-sbc-raw-restricted-cohomology-natural-iso`.
- `AlgebraicGeometry.Etale.exists_restricted_affine_complex_system`
  in `RestrictedAffineComplexSystem.lean`, node `lem-sbc-restricted-affine-complex-system`.

All four sandbox modules compile in import order through the prescribed lcompile launcher.
The original proof was compiled first with existential P and a, and again after making P
canonical and a=0. Both versions of the reduction compiled. Final local compilation and the
axiom/static checks are also performed by deliver3.py --no-push.

## No longer needed

Removed proof-only imports: `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction` and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. No module is claimed to leave the target closure.
The original seven direct proof dependencies are now responsibilities of the two lower
obligations, rather than direct steps of the parent proof: inverse image, composition,
cohomology, derived adjunction, sheafification, bounded-below injective representatives and
K-injective Hom. They are not pruned from the mathematical argument.
The generic P and arbitrary lower-bound witnesses are unnecessary in the geometric lemma;
the parent supplies the canonical map and bound zero directly. This is not module pruning.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original dependency statements do not themselves supply the
varying-site geometric complex system or the natural raw-Hom/restricted-cohomology
identification. The delivered nodes isolate those steps rather than treating the existing
sheafification comparison as an isomorphism on raw groups. The unit record
`dag/units/sk-lem-failure-field.json` has no realized node that this reduction bypasses.

Searches were run through msearch.py and recorded in searches.jsonl. Lean Finder returned
unrelated etale-algebra facts for the raw comparison and affine structure-sheaf limit facts
for the geometric system. Loogle returned unrelated single-cohomology facts and generic
right-derived units. Mathlib grep and searches in both library roots found generic pullback,
single-complex and derived-category ingredients, and module-coefficient free-sheaf results;
no complete abelian-coefficient statement was found. LeanSearch returned Internal Server
Error for all three queries and is recorded as unavailable, never as a negative result.
Blueprint searches for restricted cohomology and single complexes both returned zero matches.

The sources read were Stacks Tags 03Q8, 09Z1 and 0EZM, and the cited Cohomology on Sites Tags
072W and 0BKV. The explicit derived-unit naturality is an agent elaboration of the parent's
step 3, not a verbatim lemma in those sources.

Edge cases checked mathematically: if U is empty, both restricted cohomology and raw Hom
are zero; if coefficients are zero, all constructions and maps are zero; for p=0 the
comparison reduces to the free-sheaf sections adjunction. An identity triangle gives an
identity after the two inverse-image comparisons. The geometric construction works for a
singleton directed index and allows repeated stages. Its original nonempty/directed and
qcqs hypotheses are retained. No IsColimit B or class-descent claim was introduced.

## New nodes

`def-sbc-raw-affine-restricted-cohomology` records the actual restricted cohomology and maps
in `RawAffineRestrictedCohomology.lean`; there are no postponed proofs in these definitions.

`lem-sbc-raw-restricted-cohomology-natural-iso` records source step 3 as a comparison family
natural for all structure morphisms and coefficients. This is a separate obligation from the
construction of a scheme limit or a coefficient colimit.

`lem-sbc-restricted-affine-complex-system` records source steps 1 and 2: affine base change,
restriction, degree-zero complexes, the coefficient colimit and canonical cohomology cocone.
The statement contains no raw derived Hom, and proves no cohomology continuity.

All three nodes inherit the parent's chapter and unit, with blueprint provenance through the
parent to `sbc-lem-higher-direct-image-limit`. There are no change records or forced
adaptations because no existing definition, statement, signature or visibility was changed.

## Second reading by M3

1. Compared the delivered parent module with the repository version. Existing declaration
signatures, the presentation inductive, and public imports needed by statements are unchanged;
the proof-only import set changes only as documented above. Verdict: pass.

2. Compiled all four sandbox modules with the prescribed lcompile launcher. The parent has no
`sorry`; the two split obligations are named public theorems and are the only remaining holes.
No forbidden declarations or hollow definitions occur. Verdict: pass, with the two documented
split obligations retaining `sorryAx` until proved.

3. Checked the split statements against the source arguments and searched the library and
Mathlib for duplicates. Both are strictly lower obligations: one constructs the restricted
complex system and one supplies raw-to-restricted naturality. Their docstrings give complete
proof arguments and their DAG nodes match their signatures. Verdict: pass.

4. Read the proof from the target downward. It uses the two new obligations, keeps the unit's
geometric route, fixes canonical pullback and lower bound zero, and avoids an unsupported
continuity claim. The removed proof-only imports `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` are no longer needed; all other
imports remain required. Verdict: pass.

5. Compared the parent node proof, dependencies, and origin with the Lean proof, and checked
that the three new node records carry matching statements, routes, and provenance. Verdict:
pass.

Changed in this second reading: added this review record, corrected the no-longer-needed
import list above, and made no mathematical or signature changes.
