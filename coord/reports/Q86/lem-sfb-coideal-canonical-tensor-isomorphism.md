## Worker report

The module `Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism` states
`RelativeHopf.coidealCanonicalTensorIsomorphism`, with its entire proof `sorry`.
`RelativeHopf.CanonicalTensorIsomorphism` is a structure packaging this node's
specified action, coactions and isomorphism; it introduces no independent mathematical
notion and contains no chosen data or postponed proofs. No other node is restated.
The original node is unchanged except for its `lean` record.

Source read: Bichon, arXiv:2301.05480v2, section 2.1 and section 2.2,
Proposition 2.2 and its displayed inverse, at
https://arxiv.org/html/2301.05480v2. The node's commutative case is used throughout.
WANTED: `literature/bichon-faithful-flatness_arXiv-2301.05480.pdf` is the node's
requested local PDF; the full relevant source was read in the arXiv HTML.

Hypotheses and clauses, matched individually:

- The field is `(k : Type u) [Field k]`; H is `(H : Type v) [CommRing H]
  [Bialgebra k H]`. As in the recorded dependency, the algebra-valued antipode
  is `S : H →ₐ[k] H`, with exactly its two Hopf identities `hSleft` and `hSright`.
  Bialgebra supplies the multiplicative comultiplication, counit, coassociativity
  and counit identities. Commutativity makes the antipode an algebra map.
- A is `Subalgebra k H`, hence unital, and `hA : IsRightCoideal k H A` is exactly
  Delta(A) contained in A tensor H, using the dependency's range formulation.
- C, J and pi are the existing `Quotient k H A`, `augmentationIdeal k H A` and
  `quotientMap k H A`. The theorem existentially supplies `hJ`, a proof that J
  is a coideal; this is the conclusion of `relativeHopfModuleKernels`, not an
  extra hypothesis or an arbitrarily chosen coalgebra. The coalgebra on C is
  the canonical Mathlib quotient. Proof irrelevance makes the choice of hJ immaterial.
- Every H-module X is quantified by `Type w`, `AddCommGroup X`, `Module H X`.
  The A- and k-module structures with scalar towers express restriction, not
  additional module-theoretic assumptions: the tower applied to a, 1, x forces
  `a • x = (a : H) • x`. Restriction structures exist for every H-module.
  For naturality Y has an independent universe `w'`.
- `CanonicalTensorIsomorphism.diagonalModule` and `diagonalTower` package the
  target module structure; `diagonal_smul` pins its action explicitly to
  `tensorAction k H C X (Coalgebra.comul h) z`. Thus it is precisely the
  displayed Sweedler diagonal action, rather than tensoring just the action on C.
- `induced` is the existing `Coaction` on the actual `H ⊗[A] X` and
  `induced_formula : IsInduced ...` is the recorded dependency's generator formula.
  Consequently this is L(X), without a separate induction construction.
- `coaction` is the existing relative `Coaction` on `C ⊗[k] X`, with the diagonal
  instance passed explicitly. `coaction_formula` identifies its map with
  `(TensorProduct.assoc ...).toLinearMap` composed with `comul.rTensor X`.
  This is exactly Delta_C tensor 1_X, with the required parenthesization.
- `equiv` is an H-linear equivalence from `H ⊗[A] X` to `C ⊗[k] X`.
  `forward_formula` uses `TensorProduct.map pi ((Algebra.lsmul ...).toLinearMap.flip x)`
  applied to Delta(h), which is sum pi(h_1) tensor h_2 x.
- `inverse_formula` quantifies every finite expansion
  `Delta(h) = ∑ i : Fin n, a i ⊗ b i`, and states exactly
  `equiv.symm (pi h ⊗ x) = ∑ i, a i ⊗[A] S(b i) • x`.
  Every algebraic tensor has such a finite expansion (scalar coefficients absorb
  into a factor). This expresses the Sweedler formula without selecting components.
  Because the left side is the inverse of an actual linear equivalence on the
  quotient tensor product, descent through pi, tensor balancing, and both inverse
  identities are asserted, not assumed or left as an untyped representative rule.
- `hom_isMorphism` and `inv_isMorphism` use the dependency's `IsMorphism` for
  the forward and inverse H-linear maps, so both commute with coactions.
- The second conjunct is the naturality equation for every H-linear f, on
  `h ⊗[A] x`: `(1_C ⊗ f)(kappa_X(h ⊗ x)) = kappa_Y(h ⊗ f(x))`.
  Tensor generators span over k, so this is equivalent to the whole naturality
  square with `L(f) = 1_H ⊗_A f`. H-linearity ensures f is A-linear on restriction.
  Conjugation by the two relative isomorphisms then also gives the relative
  morphism property of `1_C ⊗ f`. The equation holds for any structures satisfying
  the specified formulas; these formulas determine the maps uniquely. There is
  no arbitrary choice of a natural isomorphism.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib `Field`, `Mathlib/Algebra/Field/Defs.lean`, line 180.
- `lem-sfb-relative-hopf-module-kernels`:
  `Sheaf.RingTheory.RelativeHopfModuleKernels`,
  `RelativeHopf.relativeHopfModuleKernels` and `RelativeHopf.QuotientConclusions`.
  Its public import `Sheaf.RingTheory.RelativeHopfModuleData` supplies
  `IsRightCoideal`, `augmentationIdeal`, `Quotient`, `quotientMap`, `tensorAction`,
  `Coaction`, `IsInduced`, and `IsMorphism`; their full definitions were read.
- Proof dependency `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.map`, `TensorProduct.lift`, `TensorProduct.ext'`,
  `LinearMap.rTensor` and `LinearMap.lTensor`. Read the recorded Defs, Basic, Map
  and Tower source. These imports are already public through the statement dependency;
  no redundant additional import is needed.

Edge cases checked mathematically: X = 0; A the scalar subalgebra (J = 0);
A = H (C canonically k); H = k; zero h and x; n = 0 in the inverse expansion;
arbitrary characteristic; unbounded module dimensions; independent k/H/X/Y
universes; no flatness or antipode-stability hypothesis on A. In the empty sum
case Delta(h) = 0 implies h = 0 by the counit, so the inverse formula remains correct.
No nonzero or finite-dimensional module assumptions occur. No statement dispute
or statement correction was necessary.

Searches actually run through the prescribed `msearch.py` (full summaries are in
this sandbox's `searches.jsonl`):

- LeanFinder: "Canonical isomorphism H tensor over right coideal subalgebra A
  with X to quotient coalgebra tensor X with antipode inverse" — eight results,
  tensor unitors and coalgebra tensor constructions; no relative isomorphism.
- Loogle: "HopfAlgebra, TensorProduct" — twelve results, including both antipode
  identities and `HopfAlgebra.ofAlgHom`; no quotient-relative tensor isomorphism.
- grep, RingTheory: `coideal|HopfModule|relative.?Hopf` — thirteen results from
  coalgebra, bialgebra and Hopf quotient files; no relative Hopf module theorem.
- LeanSearch: "Canonical isomorphism of induced modules over a right coideal
  subalgebra with a quotient coalgebra tensor module" — eight results on group
  representation induction/coinduction, which are different objects.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`, including the node id, coideal, relativeHopf,
  and canonical tensor names: only the existing relative Hopf data/kernel modules
  and unrelated tensor comparisons. `grep -rn` of the item id in WeilConjectures
  found no declaration. No exact match was found.

Validation: the final delivered module compiled in both sandbox and library mode
through `scompile.py`, cleanly and within 5 seconds per compile. A separate temporary
probe checked that the diagonal-action equation uses exactly `diagonalModule.toSMul`
and that the equivalence's H-linearity also uses this same action. This exposed and
fixed an initial inference of the ordinary tensor action in the action equation.
The probe is not part of the delivery. All universes and variables are explicit;
`autoImplicit` is false; maximum line length is 93. The only postponed proof is
`RelativeHopf.coidealCanonicalTensorIsomorphism`, whose docstring gives all eight
proof steps from the node. The node's `lean.statement` is the verbatim theorem
signature, and both top-level declarations are listed in `lean.declarations`.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
