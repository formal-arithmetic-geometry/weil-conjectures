## What changed

Filled the five construction lemmas in
`Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` without changing any existing
signature, definition body, public import, or docstring.

The scalar chain map is constructed degreewise from multiplication by the actual
uniformizer section. Naturality follows from the constant-presheaf-to-completion
transformation, scalar linearity from commutativity, and compatibility with the
differential from its linearity. Degreewise sectionwise extensionality proves
uniqueness, so the existing definition now chooses from a proved unique existence
statement. The transition square is the endomorphism power recursion. The cone
transition preserves the degree-zero inclusion by the mapping-cone API. A proved
private product-extensionality lemma shows that the product augmentation composed
with one-minus-shift vanishes; this proves both signed and unsigned zero-cochain
lift conditions.

Server validation through `lcompile.py` passed cleanly (10.9 seconds).

The five-way theorem remains the original named theorem with its original proof
plan and sorry. This is a partial delivery of a module with several holes, with
no new holes or split statements. The main theorem's DAG route remains unchanged.

## Proved and sorry left

Closed five of the six original holes:

- `WeilConjectures.integralKoszulScalar_existsUnique`.
- `WeilConjectures.integralKoszulStep_square`.
- `WeilConjectures.integralKoszulUnit_compatible`.
- `WeilConjectures.integralKoszulIntrinsicUnit_condition`.
- `WeilConjectures.integralKoszulLimitUnit_condition`.

One original hole remains:
`WeilConjectures.roosIntrinsicCompletenessEquivalence`, node
`lem-pur-roos-intrinsic-completeness-equivalence`.

Added zero holes and zero split statements. The private helper
`integralKoszulProductUnit_comp` is fully proved. These arguments also cover the
zero complex and empty site: the scalar and transition equations are sectionwise
identities, and the product argument uses only its universal property.

## No longer needed

Removed these proof-only imports, which none of the completed construction proofs
uses:

- `Sheaf.Paper.CompletedCoefficientPresentationTransport`.
- `Sheaf.Paper.CompletedKoszulQuotientComparison`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.StrictRoosDerivation`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.

No mathematical dependency node or module is withdrawn or claimed globally
unnecessary. The still-unproved five-way theorem retains its planned dependencies
in the DAG; the eventual proof should import whichever of them it uses. All public
imports are retained, including the general intrinsic-completion and Koszul
reconstruction interfaces. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The final theorem is not an immediate application of the attached reflector.
The node `lem-weil-pbc-ringed-koszul-completion-reflector` attaches
`AlgebraicGeometry.Scheme.wfCompletionReflector`. Its published conclusion is
complete output and a Hom bijection, with `WfIsComplete` defined through an
invertible intrinsic unit. It does not itself give the local RHom vanishing
criterion of clause (ii). The original generic
`CategoryTheory.ringedKoszulCompletionReflector` does state that criterion, but
requires a small site with equal object/Hom/coefficient universes. The direct
`ConstantCompletion.koszul_quotient_reflector` also states the criterion, with
the same small-site universe requirement. The present
site has sizes t+1/t and coefficient universe max u (t+1), so one must explicitly
transport to a small model, compare the one-generator dual-Koszul tensor tower
with the present mapping cones, and preserve the normalized units.

The other comparison interfaces also require transport: `purCoefficientModel`
uses a scheme and field in the same universe, while
`completedKoszulQuotientComparison` fixes the coefficient universe one above the
scheme's. Neither can be applied verbatim to these independent-universe integral
models. I did not weaken or specialize the five-way statement to bypass those
comparisons, and did not introduce a renamed or repackaged copy of its hole.

Searches used all three requested modes through msearch.py (leanfinder, loogle,
grep), followed by direct searches of Mathlib and both library roots. The useful
short route for the construction lemmas is the existing mapping-cone, endomorphism
power, presheaf-module naturality and product APIs. No source-library file changes
are needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
