## What changed

Proved `CategoryTheory.exists_ringedKoszulDualBasis` without changing its signature.
The basis is the canonical ordered negative-tensor basis composed with the existing
negative-to-dual isomorphism. Its coproduct property uses the already stated
supported-subset coproduct directly, with a proved zero-length case. The actual
one-step transition is calculated recursively on its two factors; the full
transition follows by induction on `n ≤ m`. The existing duality equations give
the prescribed empty-coordinate unit.

Added `Sheaf.CategoryTheory.RingedNegativeKoszulBasisUnitor` for the exact
unit normalization, `Sheaf.CategoryTheory.RingedNegativeKoszulSignedDifferential` for the signed
erased-index boundary, and
`Sheaf.CategoryTheory.RingedNegativeKoszulExteriorDifferential` for the comparison
with actual exterior coefficients. Its proof evaluates scalar endomorphisms at one, transports
the existing Koszul-direction tensor formula along the left unitor, and identifies
its coefficients with the actual exterior contraction using increasing wedges.
The auxiliary algebra, scalar, and unitor calculations are proved private helpers.
No existing public statement or definition changed. The tensor and algebra calculations are in separate proved modules to keep each
file within the 60-second compile limit. Large negative-tensor definitions are
locally irreducible while proving these lemmas; this changes no imported
interface. The final imports added to the item are the supported-basis coproduct, negative-to-dual duality, and the new
boundary-comparison module, all private proof imports.

Validation uses the remote single-file compiler and the delivery tool's interface
probe and preflight. The assigned theorem signature and all node attachments
were checked verbatim; all lines are at most 100 characters.

## Proved and sorry left

Closed the original hole in `CategoryTheory.exists_ringedKoszulDualBasis`
(`lem-sfb-ringed-koszul-dual-basis`): 1 of 1 original holes.
The new theorems `CategoryTheory.ringedNegativeKoszulBasis_leftUnitor`
(`lem-sfb-negative-koszul-basis-unitor`),
`CategoryTheory.ringedNegativeKoszulBasis_signed_d`
(`lem-sfb-negative-koszul-signed-differential`) and
`CategoryTheory.ringedNegativeKoszulBasis_exterior_d`
(`lem-sfb-negative-koszul-exterior-differential`) are proved.
No holes added; no `sorry` remains in any delivered Lean module. This is a
proof from the existing declarations with no new holes.
Existing imported dependencies of the plan, notably the supported-basis coproduct
and the Koszul-direction differential, remain separate stage-3 obligations.

## No longer needed

The main proof does not use the full
`exists_ringedSignedKoszulFiniteCoordinates` package
(`lem-cbc-signed-koszul-finite-coordinates`,
`Sheaf.CategoryTheory.SignedKoszulFiniteCoordinates`). The original file had no
proof imports to remove; the planned import of this package is unnecessary. Neither its arbitrary coefficient complexes,
its constructed transitions, nor its quasi-isomorphism preservation enter this
argument. The negative basis coproduct and Koszul-direction differential suffice.
The actual tower transitions are proved directly from their definitions.
The algebraic exterior differential and free-basis declarations remain needed
below the new boundary-comparison lemma. No existing module or node is withdrawn;
no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: CategoryTheory.ringedNegativeKoszulBasis_d_succ`
in `Sheaf.CategoryTheory.SignedKoszulSummandDifferential` omits both the
`m+1` power and the earlier-index sign on its right-hand side. On the point site
with O = Z, one factor with section 2 and m = 1 has actual differential 4,
whereas the displayed formula gives 2. For two factors with both sections 1,
m = 0, and I = {0,1}, the actual boundary is e_{1} - e_{0}, whereas the
formula gives e_{1} + e_{0}. The separate
`ringedNegativeKoszulSummand_D₂_succ` has the correct powers and signs and is
the declaration used here. The disputed module is held by C4, so it is not
edited outside the forced-adaptation rule; this report requests that its holder
or the maintainer add the dispute marker at that declaration and repair it.

## New nodes

`lem-sfb-negative-koszul-exterior-differential` records the proved equality
between the actual boundary on one specified negative pure tensor and its actual
exterior coefficients. It asserts no coproduct, choice of basis, duality,
transition, or unit compatibility. It is a strictly smaller calculation used by
the item. Its source is Stacks Tags 0622 and 0664 and Tag 0A0E, and its proof
records the signed-tensor and ordered-exterior calculations. No change record
is required: no existing interface changed.

`lem-sfb-negative-koszul-signed-differential` records the proved signed
negative-basis boundary, independently of exterior coefficients. It applies the
existing Koszul-direction differential to O[0] and transports the specified
inclusions along the left unitor. It has the same Stacks sources. It contains no
new hole and is a separate module for the compile-time bound.

`lem-sfb-negative-koszul-basis-unitor` records the proved equality between the
canonical negative basis followed by the inverse left unitor and its prescribed
pure-tensor summand in O[0] tensor N. It uses the generic monoidal unit identities,
with the single-complex degree transport. Its source is Stacks Tags 0664 and
0A0E. This proved calculation is separate to keep each file under the compile
limit; it adds no hole.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
