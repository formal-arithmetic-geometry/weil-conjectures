## What changed

Replaced the hole in `AlgebraicGeometry.Etale.exists_restricted_affine_coefficient_system`
by a reduction using concrete fibre products and concrete degree-zero single complexes.
The original theorem signature and public imports stay unchanged.

Added `Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientConstruction`. It constructs
`restrictedAffineDiagram`, `restrictedAffineCone`, `restrictedAffineK`,
`restrictedAffineSingle`, `restrictedAffineG`, and `restrictedAffineL` directly.
The geometric limit is obtained from the right-adjoint over-category pullback functor,
connected-limit preservation by the forgetful functor, and pullback symmetry.
Compactness, quasi-separatedness and affine transitions follow from Mathlib base change.
The actual image coefficient cocone is colimiting by colimit preservation of restriction
and the single functor and by the double-opposite equivalence.

Added `Sheaf.AlgebraicGeometry.RestrictedAffineSingleCoherence`, imported only for the
proof. Its remaining theorem provides inverse-image coherence and an equality of complex
maps, before applying the derived quotient or cohomology. The main theorem applies those
functors to this equality and constructs the cohomology comparisons as identity
isomorphisms. It proves negative-degree vanishing directly from the single complexes.
No arbitrary existence witness is used to define any object. The coherence theorem takes
names for the concrete constructions and equalities identifying them. This avoids costly
unfolding of the scheme and inverse-image implementations in its coherence formulas;
specialization uses only reflexivity. Its heterogeneous complex-map equality becomes an
ordinary equality in the main proof.

## Proved and sorry left

Upper hole closed: `AlgebraicGeometry.Etale.exists_restricted_affine_coefficient_system`
(node `lem-sbc-restricted-affine-coefficient-system`). No sorry remains in the item.

One hole added and left:
`AlgebraicGeometry.Etale.exists_restricted_affine_single_coherence`
(node `lem-sbc-restricted-affine-single-coherence`). This is a decomposition, not an
axiom-free completion of the original theorem. It omits the geometric limit, qcqs and
affine assertions, colimit universal property, negative-degree vanishing, and all
cohomology statements. In particular it has no cohomological degree parameter.

The construction module has no sorry. Its proved declarations are
`restrictedAffineConeIsLimit`, `restrictedAffineDiagram_compact`,
`restrictedAffineDiagram_quasiSeparated`, `restrictedAffineDiagram_affine`, and
`restrictedAffineLIsColimit`.

## No longer needed

No existing public import was removed, and no existing dependency module was pruned.
The original direct proof dependencies `def-pc-fibre-product`,
`def-weil-pbc-inverse-image`, `lem-weil-pbc-inverse-image-composition`, and
`lem-weil-pbc-left-adjoint-preserves-colimits` are no longer direct dependencies of the
item: their uses are now recorded in the construction and coherence nodes.
`def-sbc-raw-affine-restricted-cohomology` remains a direct dependency.

Second reading removed eight redundant proof imports from the new construction module:
`Mathlib.Algebra.Homology.HomologicalComplexLimits`,
`Mathlib.CategoryTheory.Limits.Final`, `Mathlib.CategoryTheory.Comma.Over.Pullback`,
`Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`,
`Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.CategoryTheory.Filtered.Connected`, and
`Mathlib.CategoryTheory.Adjunction.Limits`.
All are already publicly available through `RawAffineRestrictedCohomology`; this
removes redundant import lines without pruning any module from the import closure.
No new continuity theorem, cohomology diagram, or cohomology cocone is needed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original existential proof binders trigger the unused
variable linter once the theorem is proved, since their required evidence is not used in
the final morphism equation. Their names and types are preserved, with that linter disabled
only for this theorem. There are no compiler warnings. Tags 09Z1 and 0EZM specify the mathematical coefficient
construction but omit its formal categorical transport details. The remaining new hole
isolates these details rather than any cohomology-continuity assertion. The concrete
single-complex cocone makes the limit cohomology comparison definitionally an identity;
there is no need to choose a separate colimit comparison isomorphism.

The unit record `sk-lem-failure-field` has empty realized lists. This delivery changes no
unit route and implements the existing node's three steps.

Edge cases checked in the signatures: the coherence lemma needs no limiting cone, affine
etale object, affine transition, or qcqs assumptions; an empty restricted scheme and zero
coefficient sheaves still give the same pullback, single-complex and cocone constructions.
The geometric limit proof explicitly uses connectedness of the nonempty directed index,
whereas the coefficient colimit uses only the double-opposite equivalence.

## New nodes

`def-sbc-restricted-affine-coefficient-construction` records the concrete scheme and
coefficient objects and their proved geometric and colimit properties in
`lean/Sheaf/AlgebraicGeometry/RestrictedAffineCoefficientConstruction.lean`.

`lem-sbc-restricted-affine-single-coherence` records the remaining underived complex-level
coherence theorem in `lean/Sheaf/AlgebraicGeometry/RestrictedAffineSingleCoherence.lean`.
Its source and complete natural-language construction are in its docstring and DAG proof.
The explicit equality parameters identify fixed data; they are not an additional geometric
assumption or a repackaging of the original coefficient-system existence theorem.
There are no interface changes or forced adaptations, and no change record is required.

## Second reading by S1

1. PASS: Compared the delivered item with the repository by diff and mechanically compared
   the full existing theorem signature byte for byte. Only its proof, a proof-only import,
   and a declaration-local unused-variable linter option changed. No existing definition,
   statement, public import or target changed; no interface change record is required.
2. PASS: All three modules compiled through lcompile.py. The only textual sorry is the
   whole proof of the public named coherence theorem. No forbidden declarations or hollow
   definitions occur. The concrete diagram, cone, K, G and L use actual pullbacks, functors
   and the actual colimit cocone. The proof extracts existential coherence witnesses only
   inside the theorem, never to define data. A scratch module's #print axioms checked all thirteen delivered declarations:
   all eleven construction declarations use only propext, Classical.choice and
   Quot.sound; the coherence theorem and original theorem additionally use sorryAx.
   The delivery tool also runs its per-declaration axiom probe.
3. PASS: Read the complete coherence statement, its docstring argument and node. After
   substituting the five equalities, psi is the restricted coefficient map on single
   complexes. The cone comparison is the single image of restricted eH followed by the
   inverse of the two composition comparisons in rawAffineRestrictedCoefficient and the
   inverse single-complex comparison. Its inverse cancels those isomorphisms against the
   cocone injection. Unit/associativity and naturality give the transition equations.
   This works for a one-object index, zero sheaves, and an empty etale scheme; it requires
   no affine or limit hypothesis. Nonempty directedness is used by the separate geometric
   limit proof. Fresh LeanFinder, Loogle and grep searches, and library searches for
   cartesian coefficient systems and single-complex composition, found components but no
   theorem assembling this statement. It is strictly a part of the argument: it contains
   no geometric witnesses, limiting or colimiting proof, lower bound or cohomology, and
   has no p parameter. One upper hole closed and one lower hole added is decomposition,
   net zero holes, not an axiom-free completion. Closing the remaining simultaneous
   coherence laws is not a short repair; no additional holes were introduced.
4. PASS after repair: The main proof uses Mathlib limit preservation, base change,
   single-complex colimits and vanishing, then the underived coherence lemma and the
   defining cohomology equation. No continuity theorem is invoked. Removed eight redundant
   proof imports, corrected the no-longer-needed direct dependency list, and checked
   dag/units/sk-lem-failure-field.json: its realized lists are empty and remain unchanged.
   No unit route is bypassed and no old module is pruned from the closure.
5. PASS after repair: The item node records its three actual proof steps and their union
   of dependencies; the new coherence node records the remaining hole and its route.
   The construction node originally had an empty proof despite proved limit and colimit
   results: supplied three construction/property proof steps and their dependency union.
   New-node source, creation, blueprint, search and Lean records were checked.

Second reading changed only redundant proof imports, the construction node's proof and
proof_deps, and this report (including the direct dependency pruning accounting).
The original theorem's signature and all concrete definitions are unchanged.
