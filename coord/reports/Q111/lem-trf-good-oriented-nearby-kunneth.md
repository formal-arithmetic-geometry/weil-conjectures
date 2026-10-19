## Worker report

The module `Sheaf.Paper.GoodOrientedNearbyKunneth` states
`AlgebraicGeometry.OrientedNearbyCycles.isIso_kunneth_of_isPsiGood`.  It uses the
canonical `kunneth` comparison from `Sheaf.Paper.OrientedNearbyCycles` and states
that it is an isomorphism under the node's finite type, finite coefficient,
invertible-annihilator, boundedness, and Ψ-goodness hypotheses.  Its proof is
`sorry`, as required for stage 2.

The Lean rendering of each clause is as follows.  The base scheme and the two
morphisms are `{T₁ T₂ B : Scheme.{u}}`, `f₁ : T₁ ⟶ B`, and `f₂ : T₂ ⟶ B`.
“Finite type” is the conjunction of Mathlib's `[LocallyOfFiniteType fᵢ]` and
`[QuasiCompact fᵢ]` for each leg.  The finite commutative coefficient ring is
`(Λ : Type v) [CommRing Λ] [Finite Λ]`.  “Annihilated by an integer m ≥ 1
invertible on B” is the project's exact `AlgebraicGeometry.HasInvertibleExponent
Λ B` class; its field is `∃ n, 0 < n ∧ (n : Λ) = 0 ∧ IsUnit (n : Γ(B, ⊤))`.
The two bounded derived inputs are `Lᵢ : EtaleDerived Tᵢ Λ` with
`hLᵢ : IsBounded (etaleDatum Tᵢ) (Coeff Λ) Lᵢ`.  Their goodness assumptions are
`hgoodᵢ : IsPsiGood fᵢ Λ Lᵢ`, which quantifies over every scheme base change.
The conclusion is exactly `IsIso (kunneth f₁ f₂ Λ L₁ L₂)`, where `kunneth` is the
specified beta-tensor-beta followed by lax-tensor comparison; its product scheme,
projections, and vanishing-topos maps are therefore the canonical ones from the
dependency definition.

Dependency declaration used: `Sheaf.Paper.OrientedNearbyCycles`, namespace
`AlgebraicGeometry.OrientedNearbyCycles`, declarations `EtaleDerived`, `Coeff`,
`IsBounded`, `IsPsiGood`, and `kunneth`.  The finite-type dependency is the
Mathlib leaf `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` from
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.  The invertible-exponent
class is `AlgebraicGeometry.HasInvertibleExponent` from
`WeilConjectures.AlgebraicGeometry.InvertibleExponent`.

Edge cases checked: `m = 1` (the class permits the zero coefficient ring and the
unit natural cast), `Λ = 0`, identity morphisms, empty schemes, and zero input
complexes.  The statement imposes no nonemptiness, separatedness, properness, or
bounded-below restriction beyond the stated boundedness of each input.

Searches made:

* `msearch.py ... leanfinder "conditional Kunneth formula for oriented nearby cycles finite type Psi good bounded derived complexes"`: eight hits, all unrelated homological-complex or topology declarations; no match.
* `msearch.py ... loogle "AlgebraicGeometry.OrientedNearbyCycles.kunneth, IsPsiGood, HasInvertibleExponent"`: zero hits; the identifier is unknown to Loogle.
* `msearch.py ... grep "nearbyCycles|IsPsiGood|kunneth" Mathlib/AlgebraicGeometry`: zero hits.
* `rg` over `WeilConjectures/` found only unrelated pro-etale Künneth declarations; `rg` over project `lean/Sheaf` found the existing `OrientedNearbyCycles.lean` definition but no theorem asserting its isomorphism under these hypotheses.
* The DAG search found this item's existing dependency definition and no duplicate theorem node.

No statement correction, new node, dependency module, or
`STATEMENT-DISPUTED` marker is needed.

## Second reading by Q111

I reread the item node and the full `def-trf-oriented-nearby-cycles` statement.
The Lean binders preserve both independent scheme/coefficient universes, retain all
four finite-type class hypotheses, render the coefficient condition through the
canonical existential class, and retain both boundedness and both all-base-change
Ψ-goodness hypotheses.  The conclusion uses the exact canonical `kunneth` map,
with no extra clause.  The module compiles cleanly with `scompile.py`; the only
expected postponed proof is the theorem's `sorry`.
