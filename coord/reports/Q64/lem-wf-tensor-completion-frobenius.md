## Worker report

Retained and checked the saved module `Sheaf.Paper.WfTensorCompletionFrobenius`
against the current node and dependency sources. The first resumed dry run compiled
both views of the module but rejected one overlong docstring line (line 204).
Wrapped that line. The saved node attachment and report described an older, shorter
version of the module; replaced the attachment's signature verbatim with the actual
`wfTensorCompletionFrobenius` signature and listed all 21 explicit declarations.
No statement, dependency, proof, or other non-Lean node field is changed.

The module renders every clause of the node as follows.

* `D : FiniteFieldDatum.{u}` supplies p, q, k₀ and its specified algebraic closure k.
  `c : D.CoefficientDatum` supplies the prime l, l≠p, and Qbar. The finite
  coefficient field `E : Padic.FiniteCoefficientFields c.l c.Qbar` supplies the
  actual extension, integer ring and uniformizer through `pbcStageDatum` and
  `pbcStageUniformizer`. `X₀ : Over (Spec (.of D.k₀))`, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` render separated finite type.
  The geometric fibre is always `(D.geometricFiber X₀).left`.
* `WfTensorCompletion.Integral` abbreviates the existing
  `PbcBoundedConstructibleComplete` category, including its completed-coefficient
  and etale-origin conventions. The inputs of `integral` are arbitrary pairs
  from this integral category; they need no Weil maps. `ordinaryAmbient` is the
  published `wfOrdinaryDerivedTensor` over the actual completed coefficient
  sheaf B, restricted along the full inclusions. `completedAmbient` is that
  functor followed by the existing Koszul reflector `wfCompletion` and its
  full inclusion. These abbreviations introduce no alternative tensor or
  completion construction.
* The theorem `integral` says both tensors are bounded constructible complete,
  the actual `wfCompletionUnit` is invertible, and its square commutes for
  every integral pair of arrows. This is the canonical, natural comparison
  chi in the first clause, with the quotient/Koszul identification described
  in its proof docstring. It also supplies the proof fields needed for the
  real restricted functors `ordinary`, `completed` and natural transformation
  `chi`. No definition has sorry data.
* `ordinaryMu` restricts `proEtaleCanonicalTensorComparison` and `completedMu`
  restricts the published `wfIntegralTensorPullback`. `pullback` is precisely
  `pbcIsoIntegralPullback` along `D.geometricFrobenius X₀`. The theorem
  `integral_equivariance` accepts arbitrary integral Weil isomorphisms phi, psi
  and states `(ordinaryMu ≫ tensor(phi,psi)) ≫ chi =
  pullback(chi) ≫ completedMu ≫ completedTensor(phi,psi)`. Thus it renders
  chi ∘ varphi_T = varphi_hatT ∘ Phi*(chi), with categorical composition
  written left-to-right as required by Lean.
* `Rational` and `localization` abbreviate `PbcRationalCategory` and
  `pbcRationalization`, whose objects are unchanged integral objects.
  `RationalComparison` packages the two localized bifunctors, their natural
  isomorphism and the two Frobenius tensor comparisons. Its `Normalized`
  predicate fixes the two functors on localization and every comparison
  component to the actual localized integral component. `HEq` accommodates
  dependent object equalities; it does not permit arbitrary component maps.
  Functoriality fixes inverses of the scalar-denominator endomorphisms, hence
  all localized arrows, from the indicated equalities.
* `wfTensorCompletionFrobenius` asserts existence and uniqueness of this
  normalized rational package, its displayed tensor Weil equation for every
  `K L : WeilD D c X₀ E`, and an isomorphism of the actual fixed-pair Weil
  objects whose underlying map `e.hom.hom.f` is exactly `R.chi.hom.app`.
  The helper definitions `ordinaryPair` and `completedPair` use the specified
  tensor comparison followed by tensor of the input Weil maps. Uniqueness
  expresses the normalization of the canonical localized functors and maps.
* `wfTensorCompletionCommonField` quantifies over arbitrary E,F,G and inclusions
  `h : E ≤ G`, `k : F ≤ G`, transports both Weil inputs with the existing
  `weilScalarExtension`, and gives the prescribed chi Weil isomorphism at G.
  Its `ebar` clause is exactly its image under `(weilScalarSystem D c X₀).ι G`,
  so it also renders the common-stage algebraic-closure coefficient assertion.
  The assumption `R.Normalized` identifies the canonical package whose
  existence is supplied by the preceding theorem.

All four postponed theorems (`integral`, `integral_equivariance`,
`wfTensorCompletionFrobenius`, `wfTensorCompletionCommonField`) are clauses or
restrictions of this same DAG statement. Each has its source/blueprint docstring
and a natural-language proof plan. They are recorded in lean.declarations;
all their proofs are exactly `sorry`. The auxiliary definitions restrict or
package the already recorded constructions; no separate mathematical notion or
new DAG node is needed.

Dependency declarations read and used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the imported coefficient
  integer-ring, uniformizer and finite-stage constructions.
* `Sheaf.Paper.TwFrobeniusAction`: `WeilConjectures.twFrobeniusAction`, read
  for the geometric Frobenius convention; the actual geometric automorphism
  in this statement is `D.geometricFrobenius`, not a cohomological action.
* `Sheaf.Paper.PbcWeilCategory`: `WeilD`, `WeilDQbar`,
  `weilFrobeniusPullback`, `weilScalarExtension`, `weilScalarSystem`.
* `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization`.
* `Sheaf.SixFunctors.ConstructibleTensorCompletion`:
  `WeilConjectures.constructibleTensorCompletion` (the quotient-tower
  comparison, with specified mapping-fibre components).
* `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete` and its explicit Koszul unit.
* `Sheaf.Paper.WeilTensorProduct`: `wfOrdinaryDerivedTensor`, `wfTensorModel`,
  `wfIntegralTensorPullback`, `wfIntegralConstructibleInclusion`,
  `wfUniformizer_generates`, and the recorded tensor Frobenius construction.
* The reflector imported by that module is
  `Sheaf.Paper.WeilCompletedTensorReflector`: `wfCompletion`,
  `wfCompletionUnit`, `wfCompletionReflector`. The raw localization is
  `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`.
  The remaining explicit imports are the node's stated proof dependencies:
  integral constructible preservation, extension integers DVR, and constant
  completion equivalence.

Source checked: current blueprint main-20261015, sec-six-functors,
sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md, especially its sentence
about equivariance for Weil complexes; the node's five proof steps spell out
the prerequisite comparison formalized here. No source correction is needed.

Edge cases checked: zero objects and empty scheme are permitted; no nonzero
or boundedness hypothesis beyond membership in the required integral category
is added. The Koszul generator is `Fin 1`, appropriate to the chosen single
uniformizer. The integral theorem does not assume Weil structures, and the
integral equivariance theorem handles all integral Weil structures. The rational
theorem handles all rational Weil maps, including ones with denominators and
no integral invertible lift. The common-field theorem includes E=F=G with
reflexive inclusions and every larger common G. No identity-Frobenius exclusion,
extra universe equality, or arbitrary replacement of a canonical map occurs.

Searches retained from the saved investigation:

* `msearch.py Q64 lem-wf-tensor-completion-frobenius leanfinder
  "canonical ordinary completed tensor comparison Frobenius equivariant"`
  returned classical `AdicCompletion` naturality results, not a theorem
  about derived sheaves or Weil categories.
* `msearch.py ... loogle "CategoryTheory.IsIso, AdicCompletion, Frobenius"`
  had no valid match (`Frobenius` is unknown). The node's existing searches
  also include the valid `AdicCompletion.ofTensorProduct_naturality` query:
  ordinary algebraic adic completion, not this derived-sheaf comparison.
* `msearch.py ... grep
  "wfTensorCompletionFrobenius|tensor.*completion.*Frobenius" Sheaf`
  returned zero hits; the node records Mathlib CategoryTheory and Algebra
  searches with no matching statement.
* Rechecked with `rg` over shared `lean/Sheaf`, slopmaster2
  `WeilConjectures`, and its pinned `Mathlib` for
  `wfTensorCompletionFrobenius|wfTensorCompletionCommonField|namespace WfTensorCompletion`:
  zero hits. The existing `wfTensorFrobenius` defines the completed tensor's
  Weil structure; it does not assert this ordinary/completed comparison.

## Second reading by Q64

Reopened the saved Lean file alongside the current node and dependency
signatures. The previous report and JSON signature described only invertibility
and a completion-unit square on rational Weil carriers; that description did
not match the actual saved module and missed the source's integral naturality,
actual tensor Weil equation, and rational/common-field clauses. The saved
module already contains all these clauses, so retained its mathematical code
and repaired the metadata/report to describe it faithfully. The first dry run's
sole Lean diagnostic was the long docstring line; wrapped it without changing
any declaration. Checked all finite-field, coefficient and scheme binders,
integral inputs, unit naturality, the two canonical tensor comparisons, the
orientation of the Weil equation, the underlying map of the Weil isomorphism,
and both finite and common-stage rational conclusions as mapped above.
This is the dispatcher's requested self-check of a retained packet; no other
agent was started. No STATEMENT-DISPUTED flag or node correction remains.

Validation: the next dry run completed compilation and reached preflight, which
requires the signature text to stop before the `:=` delimiter. Removed that
delimiter from lean.statement. A full-file scratch profiling compile passed
both views (57.9 seconds for the library view); its development-only profiler
option is absent from the delivered module.
