## What changed

Replaced the hole in `AlgebraicGeometry.derived_open_hom_scalar_mayer_vietoris`
with a proof from the direct-image Mayer--Vietoris triangle on the open union.
Its signature and visibility are unchanged. Four proved private helpers establish
nested-restriction compatibility with precomposition, transposition of the constructed
restriction arrow, additive boundary construction, Hom exactness, and naturality
under every source endomorphism. Scalar compatibility is the specialization to
`schemeDerivedScalar X r (𝟙 E)`.

Removed the proof import `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`.
Added proof imports `Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction` and
`Sheaf.AlgebraicGeometry.DerivedOpenUnionAdjunctionTriangle`. The latter is a new
module containing only the remaining geometric triangle theorem; its middle arrow
is explicitly constructed from restriction of the union counit, rather than chosen.
Added the proof import `Mathlib.CategoryTheory.Adjunction.Additive` for additive
Hom equivalences. Updated the parent DAG proof and its dependencies to this route.

## Proved and sorry left

Closed: `AlgebraicGeometry.derived_open_hom_scalar_mayer_vietoris`
(node `lem-sc-derived-open-hom-scalar-mayer-vietoris`), one original hole.
No `sorry` remains in the assigned module or its four private helpers.

Added: `AlgebraicGeometry.derived_open_union_adjunction_triangle`
(node `lem-sc-derived-open-union-adjunction-triangle`), exactly one whole-proof
`:= by sorry` in its own new module. This is a decomposition: one hole closed,
one added, net zero holes. The new theorem asserts distinguishedness of a triangle
of derived direct-image objects with a specified arrow. It has no source E,
Hom-exactness clause, additive boundary, or scalar-compatibility clause. The parent
constructs the boundary and proves both requested clauses in Lean.

The existing right-adjoint theorem is used as stated. No witness of an arbitrary
mere existence theorem is used to define data: the chosen right adjoints are
unique up to the adjunction-compatible natural isomorphism. The two geometric
arrows are eliminated inside the proof, and the additive boundary is constructed.

## No longer needed

Removed import/module: `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`.
Pruned parent proof dependency `lem-pc-open-derived-restriction-comparison`.
Its quasi-coherence, support, orthogonality, and zero-object comparisons are not needed.
Only the lower right-adjoint/localization theorem is imported directly.

The parent no longer uses the exactness theorem
`AlgebraicGeometry.derived_hom_mayer_vietoris`
(`lem-sc-derived-hom-mayer-vietoris`, module `Sheaf.Paper.DerivedHomMayerVietoris`),
or the lower-shriek Hom triangle theorem
`SheafOfModules.open_hom_triangle_realization`
(`lem-sc-open-hom-triangle-realization`, module
`Sheaf.Algebra.Homology.OpenHomTriangleRealization`), as proof dependencies.
These modules are still reached through the statement definitions, including
`derivedOpenHomRestriction`; this is not a claim that they leave the entire target
import closure. No public imports of the assigned module were removed. The new triangle module
publicly imports only the derived-category definitions its statement needs. The unit record has no realized
nodes for this local argument, and the unit statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned existing interfaces do not state the naturality of a selected Hom
boundary. In particular `open_hom_triangle_realization` only gives an existential
additive shifted Hom equivalence, with no source-naturality law for it. Its proof's
naturality cannot be taken as part of that theorem's public contract. The delivered
route uses right adjunctions and proves the needed naturality directly, avoiding
an unsupported appeal to that proof.

Validation: both delivered modules compile in dependency order. The parent needs
1,600,000 elaboration heartbeats for the four large adjunction specializations;
the 800,000 setting was tested and exhausted its heartbeat budget. Successful
compiles remain below the 60-second file limit. The private generic calculation
keeps the actual category-theory proof separate from these specializations.

Read Stacks Tags 08BW, 08BV and 08EJ, and downloaded/read `cohomology.tex`,
`lemma-exact-sequence-j-star`, in the sandbox scratchpad because the local repository
has no Stacks source checkout. Tag 08BV imposes neither compactness nor
quasi-coherence; the existing scheme triangle interface imposes both and therefore
cannot be applied to these arbitrary opens and coefficients. Its K-injective
short-exact presentation remains useful to prove the new geometric theorem on
the union subscheme.

Edge cases of the new statement were checked mathematically before writing it:
if U is empty (or V is empty), b is an isomorphism onto the nonzero summand and
the overlap vertex is zero; if U=V, b is the diagonal and the triangle is split;
if both are empty all vertices are zero. For k=0 the first vertex is the right
image of E'[-1], and integer shift addition gives the same formula for negative k.
Arbitrary supplied adjunctions are transported with their units and counits, so
these checks do not assume canonical choices.

## New nodes

`lem-sc-derived-open-union-adjunction-triangle`, in
`dag/nodes/sec-picard-framework/lem-sc-derived-open-union-adjunction-triangle.json`,
states only the inverse-rotated geometric direct-image triangle on an arbitrary
open union with a constructed second arrow. Its docstring and DAG give the
K-injective/short-exact-complex proof, transport to arbitrary specified right
adjoints, and shift comparison. It serves the existing Mayer--Vietoris globalization
step of `lem-sc-finite-duality`, in the same chapter and unit. Searches were run
through msearch: LeanSearch was unavailable (HTTP 500), LeanFinder returned sheaf
Mayer--Vietoris squares rather than derived module triangles, and Mathlib grep found
generic triangle exactness, which is used. Blueprint/tag searches found no exact
whole-blueprint node for this unrestricted localized-adjunction interface.
No existing statement or definition changed; no change record or forced adaptation
is required.

## Second reading by X3

1. Compared the parent Lean module and node by diff with the repository baseline.
The existing signature and docstring are byte for byte unchanged; the public import
is unchanged. The only new declarations in the parent are four proved private helpers.
No existing definition or statement changes, so no change record is needed. Verdict: pass.

2. Compiled both modules in dependency order: triangle 8.8 seconds, parent 40.6 seconds,
without errors or warnings. Scratch copies with explicit `#print axioms` show only
`propext`, `Classical.choice`, and `Quot.sound` for all four private helpers. The parent
and new geometric theorem additionally use `sorryAx`, as expected from the open geometric
statement. The only direct hole is the named public theorem
`AlgebraicGeometry.derived_open_union_adjunction_triangle`. No forbidden declaration,
hollow definition, or data chosen from arbitrary mere existence was introduced. Right
adjoints are unique up to the adjunction-compatible isomorphism; the existential d and c
are eliminated inside a theorem proof, not used to define a public object. Verdict: pass
as a decomposition, one hole closed and one added, net zero.

3. Read the new theorem and its complete proof docstring against the downloaded
`cohomology.tex`, especially `lemma-exact-sequence-j-star` and `lemma-adjoint`.
For a K-injective representative on W, restriction preserves K-injectivity and injective
terms are flasque; hence the sectionwise sequence on Z intersect W is short exact.
Pushing its triangle to X and inverse rotating yields the displayed vertices, with the
shift comparison giving N[1]. Adjunction-compatible right-adjoint isomorphisms carry the
unit arrow to precisely the constructed b, including arbitrary supplied adjunctions.
If U or V is empty, b is an isomorphism onto the surviving summand; if U=V it is diagonal
and the triangle is split; if both are empty all terms vanish. Negative k and k=0 use
integer shift addition, not a boundedness assertion. The statement is a geometric part
of the argument, without E, Hom exactness or scalar equivariance, not a restatement.
Independent LeanFinder query about distinguished triangles of right adjoints on open
unions found site/sheaf adjunctions but no matching derived triangle. Loogle verified
`Adjunction.homEquiv_naturality_left_symm`; Mathlib grep for right-adjoint triangle/cover
and `coyoneda_exact₂` found the generic exactness used here, not the new geometry.
Repository searches and reading the existing scheme triangle, Hom sequence and
`open_hom_triangle_realization` confirmed that none has this interface: the scheme
triangle requires compactness and quasi-coherence, and the lower-shriek interface does
not specify naturality of its shifted Hom equivalence. Verdict: pass; the remaining
geometric hole is not a few-minute proof from these interfaces.

4. Checked the proof from its conclusion back to its geometric input. The boundary is
explicit postcomposition with d transported by additive adjunction bijections. Exactness
uses Mathlib directly; naturality follows by precomposition and associativity, for every
endomorphism of E before specializing to scalars. All proof imports are used and are
plain imports; the new module publicly imports only its statement definitions. The
report lists every old proof dependency removed: restriction comparison, the old Hom
Mayer--Vietoris theorem and the lower-shriek triangle. The latter two remain in the
statement import closure and are not claimed as modules removed from that closure.
Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists are
empty, and this local reduction changes no unit statement or step. Verdict: pass.

5. Compared the parent node diff and read the new node in full. Only the parent's proof,
proof_deps and proof_origin change. The steps match the four helpers and the actual
adjunction/triangle inputs; the Mathlib leaves identify the exact-functor comparisons
and `Triangle.coyoneda_exact₂` used. The new node records source, proof steps and their
dependency union, searches, creation provenance, blueprint origin, chapter/unit and
Lean declaration. Its stated geometric route matches its docstring. Verdict: pass.

Changed during second reading: added this review record only; no Lean or node repairs
were necessary. Scratch axiom probes were removed after validation.
