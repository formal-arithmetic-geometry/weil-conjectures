## Worker report

The module `Sheaf.RingTheory.CoidealCoinvariantProjection` states
`RelativeHopf.coidealCoinvariantProjection`, with its whole proof postponed by `sorry`.
`RelativeHopf.CoinvariantProjectionConclusions` is a fully defined proposition collecting
the clauses, not a new construction or an assumed projection. There are no new DAG nodes,
no dependency repairs, and no statement correction. Only the item's `lean` record changes.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`, using the `Field` match of def-weil-field.
- The commutative Hopf algebra is `(H : Type v) [CommRing H] [Bialgebra k H]`, together
  with `(S : H →ₐ[k] H)` and the two explicitly bound antipode identities `hSleft`
  and `hSright`. This is precisely the dependency's interface: the bialgebra supplies
  multiplicativity, coassociativity, and both counit identities; S has both antipode laws.
- The unital subalgebra is `A : Subalgebra k H`; `hA : IsRightCoideal k H A` says its
  comultiplication belongs to the image of A tensor H in H tensor H.
- `augmentationIdeal k H A`, `Quotient k H A`, and `quotientMap k H A` are the
  dependency's HA-plus, canonical quotient, and pi. The existential `hJ` supplies
  only the proof that this ideal is a coideal, not an extra hypothesis. Mathlib then
  supplies the canonical quotient coalgebra. There is no arbitrary coalgebra choice.
- The given retraction is `E : H →ₗ[A] A`, with `hE : ∀ a : A, E (a : H) = a`.
  Commutativity makes this the bimodule retraction required for the A-linearity clause.
- Every relative Hopf module is quantified by `X : Type w`, its additive group,
  compatible H-, A-, and k-module structures and three scalar towers, and
  `α : Coaction k H (Quotient k H A) X`. The towers identify the A- and k-actions
  with restriction from H, without requiring any finite-dimensionality or universe equality.
- `κ : CanonicalTensorIsomorphism k H A S X` is exactly the dependency's canonical
  relative Hopf-module isomorphism, including its diagonal action, forward and inverse
  formulas, and coaction squares. It is universally quantified, not arbitrarily chosen
  from Nonempty; its existence and characterization are supplied by the dependency.
- `∃ R : Submodule A X, (R : Set X) = coinvariants ... (quotientMap ... 1) α`
  specifies exactly R(X) = {x | alpha(x) = pi(1) tensor x}. `R.subtype` is j_X.
  Quantifying a submodule with this exact carrier avoids duplicating its definition.
- `∃ p : X →ₗ[A] R` gives the claimed A-linear projection. The formula is the
  pointwise equality `R.subtype (p x) = TensorProduct.lid A X
  ((E.rTensor X) (κ.equiv.symm (α.map x)))`. `E.rTensor X` is E tensor identity
  over A; `TensorProduct.lid A X` is precisely A tensor_A X = X. Thus the formula
  fixes the map uniquely rather than asserting an unconstrained split inclusion.
- `p.comp R.subtype = LinearMap.id` is p_X j_X = identity on R(X).
- `Function.Injective (R.subtype.baseChange H)` is injectivity of 1_H tensor_A j_X.
  `(p.baseChange H).comp (R.subtype.baseChange H) = LinearMap.id` states exactly
  the specified left inverse 1_H tensor_A p_X. The maps here are H-linear, as usual
  for extension of scalars; this is the natural induced action and adds no hypothesis.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, the recorded match for def-weil-field.
- Sheaf.RingTheory.RelativeHopfModuleData: `IsRightCoideal`, `augmentationIdeal`,
  `Quotient`, `quotientMap`, `Coaction`, `coinvariants`, and `tensorAction` (the latter
  is used inside the dependency's canonical-isomorphism structure).
- Sheaf.RingTheory.RelativeHopfModuleKernels: `QuotientConclusions` and
  `relativeHopfModuleKernels`, read in full. They establish the canonical quotient
  and the coinvariant submodule. The latter module is exposed by the public import
  of Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism.
- Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism: `CanonicalTensorIsomorphism`
  and `coidealCanonicalTensorIsomorphism`, read in full, including all its structure
  fields, antipode assumptions, and naturality statement. This is the direct import.
- Mathlib tensor maps `LinearMap.rTensor`, `TensorProduct.lid`, and
  `LinearMap.baseChange` use the actual module tensor products; their signatures and
  generator behavior were read in Map.lean, Associator.lean, and Tower.lean.

Edge cases checked before writing: X = 0 gives zero maps and the identity on its
zero coinvariant submodule; A = k gives the usual Hopf-module projection; A = H
has C = k and all X coinvariant, with E the identity. There is no nonzero X
assumption, dimension bound, characteristic restriction, flatness assumption, or
extra relationship among u, v, w. For H = k[t,t^-1], A = k[t^n,t^-n], and the
relative module X = H, an arbitrary A-linear retraction need not preserve coactions;
the displayed projection is E itself and still takes values in A. No colinearity
condition on E has been added.

Source: I read Bichon's section 2.1, Proposition 2.2 and Lemma 2.6 at
https://arxiv.org/html/2301.05480v2. Lemma 2.6 gives the displayed formula and
concludes with the tensored retraction when E is a bimodule expectation; commutativity
in this node supplies that condition. Its diagram is expanded in the node's five
proof steps, all reproduced in the theorem docstring. WANTED: the cited local PDF
literature/bichon-faithful-flatness_arXiv-2301.05480.pdf remains absent; the HTML
source was available. I also read the current latest blueprint unit
sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md; this item is a supporting
lemma, not a change to that unit's statement.

Searches made with msearch.py (full machine results in sandbox searches.jsonl):

- LeanFinder: "A retraction from a commutative Hopf algebra to a right coideal
  subalgebra projects relative Hopf modules onto their coaction coinvariants".
  Eight hits, including HopfAlgebra.ofAlgHom and structural antipode identities;
  none constructs the required projection.
- Loogle: `"coinvariant"`. Twelve hits, including Representation.Coinvariants and
  Rep.coinvariantsFunctor. These are quotients by action differences, not the
  coaction equalizer here, and do not state this lemma.
- Grep: `coinvariant|conditional.?expectation|HopfModule`, Mathlib/RingTheory.
  Zero hits.
- LeanSearch: "A conditional expectation onto a right coideal subalgebra splits
  the coinvariant submodule of a relative Hopf module". Eight structural Hopf algebra
  hits, none a match.
- Direct rg of the source library and Sheaf for `coideal`, `Coinvariant`,
  `coinvariant`, `relativeHopf`, `RelativeHopf`, and later the two proposed declaration
  names. Found the three dependency modules and unrelated representation/Weil-sheaf
  coinvariants; no existing statement or name conflict.
- `grep -rn lem-sfb-coideal-coinvariant-projection lean/WeilConjectures` and rg of
  dag/lean_names_upstream.json found no existing declaration for the item.

Validation: scompile.py Q15 lem-sfb-coideal-coinvariant-projection compiled the
module against the live server library in both sandbox and library contexts, with
no errors or unexpected warnings (5.1 s and 8.9 s). Every theorem proof is sorry;
the collecting definition contains real proposition data. No STATEMENT-DISPUTED
issue was found.

## Second reading by Q15

I performed a separate second pass with the node and completed module open. This
is a worker self-check; the dispatch brief assigns the independent review to the
maintainer and forbids starting another agent here.

The field, commutative Hopf identities, right coideal subalgebra, and supplied
A-linear retraction with identity restriction match the node. I checked each
binder of the collecting predicate against the dependency: the scalar towers
express restriction, and κ carries both formulas and the actual relative
isomorphism, not a general equivalence. The existential hJ is a proof only, so
it does not add a coideal assumption. I checked that R's carrier is the exact
coinvariant set, that j is its subtype map, and that the formula composes alpha,
κ inverse, E tensor identity, and the A tensor_A X unitor in that order. The
three remaining conclusions are p j = 1, injectivity after tensoring j, and the
specified tensor of p as left inverse. There is no claim that E is a comodule
map and no flatness premise. All five proof steps are in the theorem docstring.
No mismatch or repair was found; no statement or dependency changes were needed.
