## Worker report

The module `Sheaf.Paper.RationalBraidingScalarCompatibility` states
`WeilConjectures.rationalBraidingScalarCompatibility`.  It quantifies a prime `l`, an
algebraic closure `Ω` of `Padic l`, a scheme `W` with residue-characteristic invertibility,
a finite coefficient stage `E`, an inclusion `hEL : E ≤ L`, and the two clauses in the node.

The first clause is the naturality equation for arbitrary rational arrows `a : A ⟶ A'`
and `b : B ⟶ B'`.  Its left side is
`rationalDerivedTensor.map (Prod.mkHom a b) ≫
(pullbackTensorRationalBraiding A' B').hom`; its right side is
`(pullbackTensorRationalBraiding A B).hom ≫
rationalDerivedTensor.map (Prod.mkHom b a)`.  Thus the source and target order and the
Koszul swap are exactly the node's displayed equation.

The second clause uses the prescribed scalar extension
`sfRationalScalarExtension l (Coefficient l Ω E) W 0 _ (Coefficient l Ω L)
(coefficientInclusion l Ω E L hEL)` as `F`, and the prescribed tensor comparison
`rationalTensorScalarComparison l (Coefficient l Ω E) (Coefficient l Ω L)
(coefficientInclusion l Ω E L hEL) W` as `lambda`.  In Lean composition order, the left side
is `F.map sigma ≫ lambda.hom.app (B, A)`, and the right side is
`lambda.hom.app (A, B) ≫ T_L.map sigma`; this is the node's
`lambda_{B,A} ∘ F(sigma) = sigma^L ∘ lambda_{A,B}` with categorical composition written
left-to-right.  The braiding on the right is applied to the actual scalar-extended objects
`F.obj A` and `F.obj B`.

Dependencies used are the canonical declarations from the recorded modules:

* `Sheaf.Paper.FiniteRationalDerivedOperations`, including
  `WeilConjectures.rationalDerivedTensor`,
  `WeilConjectures.sfRationalScalarExtension`, and
  `WeilConjectures.rationalTensorScalarComparison`;
* `Sheaf.Paper.DerivedPullbackTensorConstraints`, including
  `WeilConjectures.pullbackTensorIntegralBraiding` from
  `def-pod-integral-tensor-constraints`;
* `Sheaf.Paper.SfRationalizationKaroubi`, including
  `WeilConjectures.sfRationalConstructibleCategory` and the scalar-extension category;
* `Sheaf.Paper.DerivedPullbackTensorConstraints`, which owns the recorded
  `WeilConjectures.pullbackTensorRationalBraiding` for
  `def-sf-rational-common-tensor-symmetries`.

I checked the identity stage `E = L` (`hEL = le_rfl`), arbitrary finite inclusions including
ramified extensions, zero and identity arrows, zero input objects, and odd-degree Koszul
signs.  The universal quantification leaves all these cases in the statement.

Searches made before writing the module:

* `msearch.py ... leanfinder "Naturality and scalar extension compatibility of the rational Koszul braiding on completed constructible derived sheaves"`: eight generic condensed/symmetric-category hits, no project-specific comparison.
* `msearch.py ... loogle "Functor.map_braiding, CategoryTheory.Functor.map_braiding_assoc, braided scalar extension"`: no hits (the first combined query also reported unknown `Functor.map_braiding`).
* `msearch.py ... grep "rational.*braiding|braiding.*scalar|scalar.*braiding" Mathlib/CategoryTheory`: no hits.
* `msearch.py ... grep "rationalTensorScalarComparison|pullbackTensorRationalBraiding" Mathlib`: no hits.
* `msearch.py ... grep "rationalTensorScalarComparison|pullbackTensorRationalBraiding" WeilConjectures`: no hits.
* `rg -n 'rationalTensorScalarComparison|pullbackTensorRationalBraiding' lean/Sheaf/Paper lean/WeilConjectures`: found only the existing operation and braiding declarations and their consumers; no declaration of this combined naturality/scalar square.

No existing Mathlib or source declaration has the combined statement, so this is a new
statement module.  No new definition node or dependency repair was needed.

## Second reading by NA

I reread the node and the generated Lean signature against each binder and clause.  `Ω`
is an algebraic closure through `IsAlgClosure`; `E` and `L` are exactly finite coefficient
stages with `hEL`; `W` has precisely the residue-field invertibility hypothesis.  The first
conjunct quantifies all four objects and both arrows and has the exact two composites in the
node.  The second conjunct quantifies both input objects, uses the canonical coefficient
inclusion, maps the prescribed rational braiding through the prescribed scalar-extension
functor, and composes with the two components of the prescribed tensor comparison in the
correct directions.  No hypothesis or edge case is added or omitted, and no mismatch was
found.
