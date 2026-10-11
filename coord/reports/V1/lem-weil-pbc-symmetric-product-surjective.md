## Worker report

The module `Sheaf/AlgebraicGeometry/SymmetricProductSurjective.lean` states
`AlgebraicGeometry.symmetricProduct_surjective`.  It is the Lean encoding of the
surjectivity claim for the symmetric-product morphism, with the positive integer written
as `m + 1`.  The n-fold fibre product is represented by `X : Over S`, its projections by
`pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift (Fin 2); S) ↘ S))`, and its universal product
property by `hprod : IsLimit (Fan.mk X pr)`.  The morphism is the recorded
`ProjectiveSpace.homOfGeneratingSections` attached to the symmetric-product line bundle
and coordinate sections.

The hypotheses and clauses render as follows.

* `S : Scheme.{v}` is the base scheme.
* `m : ℕ` represents `n ≥ 1` by `n = m + 1`.
* `X : Over S` is the product scheme over `S`.
* `pr` gives all factor projections to `P¹_S`.
* `hprod` states that these projections form the required product cone.
* The existential `hL` states invertibility of the tensor product line bundle
  `symmetricProductLineBundle (fun i ↦ (pr i).left)`.
* The existential `hs` states that the coordinate sections generate that line bundle via
  the epimorphism `freeHomEquiv.symm (...)`.
* The conclusion `Surjective (...)` is the definition-node notion of surjectivity applied
  to the morphism classified by those sections.  The coordinate index is
  `ULift (Fin (m + 2))`, i.e. the homogeneous coordinates `0, …, n`.

The module imports `Sheaf.AlgebraicGeometry.SymmetricProductProperties`, using its
`symmetricProductLineBundle`, `symmetricProductCoordinateSection`, and the
`ProjectiveSpace.homOfGeneratingSections` declaration from
`Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`.  The product notation
uses Mathlib's `CategoryTheory.Limits.Fan` and `IsLimit`; surjectivity is Mathlib's
`AlgebraicGeometry.Surjective` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

Edge cases checked: `m = 0` gives the required `n = 1` case; all coordinate indices are
finite and nonempty (`Fin (m + 2)`); no assumption on `S` is added; and no finiteness,
Noetherian, or characteristic hypothesis is introduced.  The existential line-bundle
and generation hypotheses are exactly the data supplied by the symmetric-product
properties node, rather than additional geometric assumptions.

Searches made:

* `msearch.py ... grep 'symmetricProduct_surjective' WeilConjectures`: no hits.
* `msearch.py ... leanfinder 'surjectivity of symmetric product morphism projective lines'`:
  only unrelated Proj chart, symmetric-algebra, and affine-space surjectivity lemmas; no
  scheme symmetric-product morphism.
* `rg` over `lean/Sheaf`: found only `symmetricProduct_properties` and the supporting
  symmetric-product definitions; no existing surjectivity statement.
* The node's recorded Mathlib leaf `AlgebraicGeometry.Surjective` was checked in
  `Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean` and is exactly the required
  underlying-point surjectivity predicate.

No new nodes or dependency modules were needed.  The theorem proof is intentionally
`sorry` at stage 2; its docstring records the geometric-point and binary-form
factorization proof route from the source.

## Earlier second reading (a previous round; superseded)

I reread the node and the complete signatures of every statement dependency.  The
specialized blueprint objects are represented by the existing `Over S` product encoding:
`X`, `pr`, and `hprod` carry precisely the product and its projections.  The recorded
`symmetricProduct_properties` declaration supplies the invertible line bundle and
coordinate-section epimorphism used by the classified morphism.  The conclusion applies
Mathlib's exact `AlgebraicGeometry.Surjective` predicate to that morphism.  No hypothesis
or coordinate index is omitted from the Lean signature, and the source's separate
finiteness assertion is not included.


## Second reading by V1

I independently read the sandbox node and module, all six statement-dependency
nodes and their recorded declarations, and the supporting sections definitions.
No statement correction, new node, or dependency module is present in this delivery.

The repository's literature files are not populated on this machine. I read the
local Stacks source copies `/home/ubuntu/c1-stacks-review/etale-cohomology.tex`,
lines 18539–18606 (label `lemma-reduce-to-P1`, Tag 0A4F), and
`/home/ubuntu/c1-stacks-review/constructions.tex`, lines 2785–2850
(labels `lemma-projective-space` and `definition-projective-space`, Tags 01NE/01NF).
The former states this map for every scheme S and n ≥ 1; it imposes no field,
Noetherian, characteristic, or finiteness hypothesis on S. Its coefficients are
indexed in reverse order; the node explicitly adopts the blueprint's ascending
powers, and the Lean uses exactly that order. Reversing the target coordinates
is an automorphism, so this agrees with the source's surjectivity assertion.

Object/hypothesis/conclusion inventory and matching verdicts:

1. Arbitrary base scheme S: `(S : Scheme.{v})`. Exact; v is arbitrary.
2. Positive integer n: `(m : ℕ)` with n = m + 1. Exact: every positive
   integer occurs and n = 0, excluded by the node, does not occur.
3. P¹_S and Pⁿ_S, with their maps to S: `ℙ(ULift.{v} (Fin 2); S)`
   and `ℙ(ULift.{v} (Fin (m + 2)); S)`, with `↘ S`. Exact homogeneous
   coordinate counts 2 and n + 1. I opened upstream ProjectiveSpace.lean:
   `ProjectiveSpace` is the pullback of S and the integral polynomial Proj;
   its `over` instance is the first projection and `toProjInt` the second.
4. The n-fold fibre product and its projections: `(X : Over S)`,
   `pr : Fin (m + 1) → (X ⟶ Over.mk (... ↘ S))`,
   `hprod : IsLimit (Fan.mk X pr)`. Exact: each Over morphism makes the
   projection commute with `X.hom`, the node's p_n. The limiting fan is
   precisely the universal property of the product over S, hence describes
   the iterated fibre product up to its unique projection-preserving
   isomorphism. I opened Mathlib's `Fan.mk` and the recorded `pullback`,
   `pullback.fst`, `pullback.snd`, and `pullback.lift` declarations. No
   arbitrary family of maps or extra geometric restriction is substituted.
5. L_n and pulled-back x_i,y_i: `symmetricProductLineBundle
   (fun i ↦ (pr i).left)`. Exact. In SymmetricProductSections.lean,
   `symmetricProductFactor` uses `Scheme.Modules.tensorPullback` on
   `ProjectiveSpace.twist ... 1`; the factor sections pull back T_0,T_1
   via its adjunction. `positiveTensorFamily` is the ordered, left-associated
   tensor of all n factors. Upstream twist and twistOneSection are the
   integral twisting module and coordinates pulled back by `toProjInt`.
6. F_j: `symmetricProductCoordinateSection (fun i ↦ (pr i).left)`.
   Exact: its definition sums the tensor monomials indexed by subsets J
   of cardinality j, choosing T_0 in J and T_1 outside J. I also opened
   SymmetricProductPolynomial.lean: it takes the coefficient of t^j in
   the product of x_i*t+y_i, using the recorded polynomial definition.
7. Invertibility and generation supplied by the properties node:
   `∃ (hL : (...).IsInvertible) (hs : Epi (...freeHomEquiv.symm ...))`.
   Exact construction data, not additional hypotheses. I opened the full
   `symmetricProduct_properties` signature: it supplies these very proofs.
   Both are propositions, so choices of proofs cannot change σ; the
   existential supplies the witnesses needed to type its recorded definition.
8. The specified morphism σ_n: the explicit
   `@ProjectiveSpace.homOfGeneratingSections` with source X.left, base S,
   structure map X.hom, exactly L_n, F_j, hL, and hs. Exact. I opened that
   definition and its selected integral morphism: the data is a classical
   choice from a named existence theorem, followed by `pullback.lift`.
   There is no hollow data or private replacement of the morphism.
9. Every target point has a source preimage: `Surjective (...)`.
   Exact: Mathlib's recorded class in Morphisms/UnderlyingMap.lean has
   sole field `surj : Function.Surjective f`. Finiteness and the informal
   factorization equivalence are not conclusions of the node or this theorem.

Edge cases: m = 0 means n = 1, with one factor and two coordinates, both
covered. There is no empty factor index since the node requires n ≥ 1.
An empty base S and empty source/target are permitted; there is no
Nonempty assumption. Zero sections on the empty scheme cause no obstruction,
and zero coordinate vectors over a nonempty field-valued point are excluded
by generation, as required. All characteristics and nonreduced bases are
covered. ULift places the finite coordinate sets in the same arbitrary
universe as Scheme.{v}; it neither restricts v nor changes their cardinality.
No test-field or scheme quantifier in a smaller universe is introduced.

Independent searches (different conceptual wording from the worker):

- LeanFinder through msearch: “binary forms split into linear factors gives a
  surjection of schemes from a product of projective lines”. Eight hits,
  including ProjIsoSpecTopComponent.toSpec_surjective, affine-space
  surjectivity, and pointsPi lemmas; none states this result.
- Loogle through msearch: `"symmetricProduct"`. Zero hits.
- LeanSearch through msearch: “surjective morphism from product of projective
  lines to projective space coefficients of product of linear forms”. Service
  unavailable (Internal Server Error); recorded without a no-match verdict.
- `rg -i 'symmetric.?product|binary.?form|product.*projective.*line'` in
  upstream WeilConjectures, Mathlib algebraic geometry, and repository
  lean/Sheaf: upstream only mentions the map in base-change proof comments;
  project has the polynomial, sections, properties, and affine-chart modules,
  but no existing surjectivity declaration. The full Mathlib search for
  symmetric products/binary forms found only set symmetric powers, Clifford
  algebra, Dold–Kan bibliography, and polynomial resultants. No match in
  dag/lean_names_upstream.json. These are different notions, not reusable
  declarations of this node.

Mismatch and repair: the signature is correct and was left verbatim unchanged
(including the node's lean.statement). The original proof docstring compressed
six node steps and did not identify their dependencies separately. I expanded
it to six numbered steps: the residue-field geometric point and its components;
coordinates via 01NE and trivialization; factorization including constants and
infinity factors; the product lift; equality of both components using pullback
and the coefficient formula; and the final underlying-point preimage. Each
step now names the node dependencies that justify it. No definition or proof
was added; the only theorem still has `by sorry`. The module has no private
notion, local notation or local instance, unbound variable, or line over 100
characters. The sole import supplies the recorded objects and product interface.

Validation: the original signature compiled cleanly on the server in 2.3 seconds.
The repaired module compiled cleanly on the server in 2.7 seconds, with no
errors or warnings. The signature was checked verbatim against lean.statement.
