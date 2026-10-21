## What changed

Reduced `CategoryTheory.CoefficientBidual.compatibility` to two separate source results:
normalized exactness of one contravariant internal Hom, and the degree-one equation for the
actual evaluation transpose. Added their two proof-only imports and the Mathlib opposite-functor
and double-opposite shift APIs. The single-Hom proof privately imports the proved ordinary
source comparison and uses the existing complex-linearity API to check its ordinary coherence stage. Both new modules keep the concrete Hom functor locally
irreducible to avoid unfolding its chosen implementation while using the projection API. All
existing public signatures, definitions and public imports are unchanged.

The private `signed_bidual_exact` is fully proved: compose the single dual with its opposite,
expand the two shift comparisons, and obtain the required leading minus from the degree-one
normalization. The private `commShiftCore_neg` and `commShift_of_one` are fully proved using
zero/addition coherence, shift faithfulness and integer induction. The main theorem then applies
the existing proved triangle assembly, including all three squares, all integer shifts and all
three two-out-of-three cases. The existing scalar and linearity proofs are retained. The complete three-module packet
compiles cleanly with `lcompile.py --all`; all existing public imports and the two original
theorem signatures were also checked verbatim against the shared source.

The single-Hom module also contains a complete private ordinary-stage construction, with no
holes: the raw source isomorphism, its quadratic correction, the shift-zero and shift-addition
laws, and the formula on every Hom-product projection. Here the naive opposite-shift parameter
is m, with correction m(m-1)/2; the actual opposite parameter n=-m gives n(n+1)/2. The
remaining theorem still needs transport, localization and the cone exactness argument.

The evaluation module also contains a proved private ordinary bidual chain map for every
coefficient complex I, its naturality, and the resulting natural transformation
`generalOrdinaryBidualTransformation`. The general Hom-differential evaluation formula retains both terms;
the chain-map proof explicitly cancels the target differentials and uses the Koszul sign
identity. It also proves `ordinaryBidual_shift_one`: the actual comparison from
`SignedDoubleHomCone.comparison` intertwines this chain map with its degree-one shift, by
product projections and the sign identity whose exponents differ by 2p. These ordinary
constructions have no zero-differential or injectivity hypothesis. Identification with the
derived evaluation transpose and descent through the normalized comparisons remain open.

## Proved and sorry left

This is a decomposition, not an unconditional proof and not positive net hole progress.
The body of `CategoryTheory.CoefficientBidual.compatibility` is now complete from the two
strictly smaller source results; its one original hole is removed. No axiom is introduced.
The other original hole is unchanged:

- `CategoryTheory.CoefficientBidual.slice_compatibility`, node
  `lem-coef-rational-bidual-triangle-compatibility`.

Two new holes remain, each a public theorem in its own module, with a full proof in words:

- `CategoryTheory.signedDerivedInternalHom_exact`, node
  `lem-coef-signed-derived-internal-hom-exact`.
- `CategoryTheory.coefficientBidualEvaluation_shift_one`, node
  `lem-coef-bidual-evaluation-shift-one`.

Original module: two holes before, one after. Packet: three holes after, two added; net minus one.
The new exactness result concerns only a single Hom with an arbitrary target and contains no
bidual/evaluation conclusions. The evaluation result is one morphism equality in shift one;
it contains no exact structure, integer coherence, triangles, restriction or scalar localization.
The categorical combination of these statements is actual checked Lean, not a renamed main lemma.

## No longer needed

No module can be withdrawn: unfinished DAG parents still require this node. No existing import
was removed. The redundant new import `Mathlib.CategoryTheory.Triangulated.Opposite.Functor`
was removed: `Opposite.OpOp` already supplies it. The new ordinary-stage import
`Mathlib.Algebra.Homology.Linear` was also removed after compiling without it; its used API
is already available through the public dependencies. No declaration of the adopted source library
was changed or removed.

The ambient proof no longer directly constructs a double-Hom cone isomorphism or descends it;
exactness follows by composition from the normalized single-Hom lemma. Its evaluation-model
calculation is isolated in the degree-one lemma. The Hom/tensor/resolution dependencies remain
needed by the latter, and the original double-Hom cone and slice restriction dependencies remain
needed by the evaluation or unfinished slice argument. Thus no global dependency pruning is
claimed. Steps 9–13 of the earlier route are retained, with their proof dependencies.

## Where the brief, the DAG or earlier work was wrong

A representative-level cone check corrected the initial draft of the new single-Hom lemma:
for Mathlib's opposite triangle convention the correction is n(n+1)/2, with a minus at
degree one and no minus at degree minus one. The twofold composite still has precisely
the required signedShift. The corrected node, docstring and Lean normalizations agree.

The existing independent-universe `RingedHomUniverses.ringedInternalHom_exact` supplies an
existential shift structure without an equation relating it to `sourceShift`. Its statement
therefore cannot identify the precise signed shift required here. The new single-Hom lemma
records that missing normalization instead of using an unspecified exact structure.

The ordinary coefficient-target bidual normalization in `RingedSiteDualityMaps` is conditional
on ordinary Hom computing derived Hom. That condition does not hold for arbitrary complexes.
The degree-one lemma consequently uses an arbitrary K-injective coefficient resolution,
K-flat tensor-Hom transposition and quasi-isomorphism descent, as the current DAG requires.

Initial preflight rejected the search records because LeanFinder and Loogle count as one
kind; the missing kind was LeanSearch. Both nodes now record actual LeanSearch queries and
source inspection of the closest candidates. The cochain reindexing and opposite-triangle
APIs do not state either normalized derived-Hom source result.

No target, mathematical statement or definition changes. Local elaboration scopes and new
private proof helpers are recorded in `coord/changes/Q7-coefficient-bidual-proof-scopes.md`.

## New nodes

`lem-coef-signed-derived-internal-hom-exact` is the signed, normalized version of contravariant
exactness in Stacks 08JC. Its proof supplies integer coherence by the triangular exponent
n(n+1)/2 and checks the cone differential and connecting arrow. Edge checks include shifts
0, 1 and -1, the zero complex, arbitrary target complexes and characteristic two.

`lem-coef-bidual-evaluation-shift-one` isolates the evaluation-transpose calculation in Stacks
08J9/0A97 and the signed double-Hom comparison. The exponents differ by 2p for every integer
p,t, including negative degrees; it makes no reflexivity assertion. Zero complexes, coefficient
objects in degree zero and characteristic two satisfy the displayed formula as well.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
