## Worker report

The module `Sheaf/SmoothPurity/InternalAdjunctionEvaluation.lean` states
`AlgebraicGeometry.Etale.internalAdjunctionEvaluation`.  It contains one theorem with
`sorry` and no definitions.  The theorem is the evaluation identity for the canonical
finite-coefficient ordinary étale internal-adjunction isomorphism.

The Lean binders render the statement as follows.  `A : Type (u + 1)` with
`[CommRing A] [Finite A]` is the finite commutative coefficient ring.  `X S : Scheme.{u}`
and `f : X ⟶ S` with `[HasCompactification f]` are the compactifiable morphism; the
explicit `[IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian S]
[CompactSpace S]` are the project encoding of the two Noetherian schemes.  No
projection-formula hypothesis is assumed: the canonical internal adjunction is the
recorded declaration `derivedHomRightDerivedLowerShriekIsoOfFinite A f`, which
obtains invertibility of the projection map from `isIso_projectionMap_of_finite`.  `M` is an
arbitrary object on `X` and `K,Q` arbitrary objects on `S` in the unbounded ordinary
étale `ModuleCat A` derived categories.

The hypothesis `h` has exactly the source and target
`Q ⟶ Rf_* RHom_X(M,Rf^!K)`.  The left hand side first applies the canonical derived
 tensor symmetry `Q ⊗ Rf_!M → Rf_!M ⊗ Q`, then the tensor--Hom inverse transpose of
`h` followed by the canonical internal-adjunction map.  This is the tensor transpose
of `alpha_{f,M,K} ∘ h` with the displayed source order `Q ⊗ Rf_!M`.

The right hand side has each displayed clause of the node: the same tensor symmetry;
`((projectionMap (ModuleCat A) f).app M).app Q`; the inverse tensor--Hom transpose
of the ordinary inverse-image adjunct
`Q ⟶ Rf_* RHom_X(M,Rf^!K)`, namely the map
`Lf^*Q ⊗ M ⟶ f^!K`; `Rf_!` applied to that map; and finally the counit of
`Rf_! ⊣ Rf^!`, `(rightDerivedUpperShriekAdjunction ...).counit.app K`.
The library's tensor functor fixes the object argument on the left, so the canonical
symmetry is written explicitly to render the node's `Q ⊗ Rf_!M` and the projection
map's `Rf_!M ⊗ Q` interfaces.

Dependencies used are:

* `prop-asd-internal-adjunction`, via its recorded declaration
  `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIsoOfFinite` in
  `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`;
* `def-weil-pbc-derived-categories`, `def-kun-derived-tensor`, and
  `def-pur-derived-internal-hom`, through the published `DerivedCategory`,
  `derivedTensor`, and `RHom` interfaces;
* `def-asd-compactifiable`, `thm-amb-etale-exceptional-adjoint`, and
  `def-amb-etale-compact-support`, through `HasCompactification`,
  `rightDerivedLowerShriek`, and `rightDerivedUpperShriekAdjunction`;
* `lem-amb-proper-coproducts-projection`, through `projectionMap`;
* `lem-pur-etale-open-derived-tensor`, through the recorded construction of
  `projectionMap`;
* `lem-kun-tensor-sym` (a statement dependency of the cited
  `lem-amb-proper-coproducts-projection`, whose displayed projection map is defined with
  it), whose published declaration is `AlgebraicGeometry.Etale.derivedTensorSymmetry` in
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`.  It renders the canonical signed
  tensor symmetry explicitly; the item's stmt_deps are unchanged.

Searches performed before writing: `msearch.py Q64 lem-asd-internal-adjunction-evaluation
leanfinder` for the canonical compact-support internal-adjunction evaluation formula
(no matching declaration); `msearch.py ... loogle CategoryTheory.Adjunction.homEquiv`
(only abstract adjunction APIs); `msearch.py ... grep internalAdjunction|internal.*adjunction|exceptional.*counit`
(no matching project/Mathlib declaration); `rg` over `WeilConjectures/` and
`lean/Sheaf` for the item id and internal-adjunction evaluation (no duplicate item
module).  I also inspected the full signatures and docstrings of every recorded
statement dependency and compiled the relevant published source modules with
`scompile.py --source`.

Edge cases checked against the statement and its source: `f = 𝟙` reduces to the
ordinary tensor--Hom evaluation with identity projection and counit; `M = 0`, `Q = 0`,
or `K = 0` makes both composites zero; arbitrary shifts retain the signed derived
symmetry; the zero finite ring gives the trivial module categories; `j = 𝟙` and
`r = 𝟙` give the proper and open parts of the compactification normalization.  No
boundedness, constructibility, Tor-amplitude, invertibility of `|A|`, or pro-étale
completion condition was added.

Compilation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q64
lem-asd-internal-adjunction-evaluation lean/Sheaf/SmoothPurity/InternalAdjunctionEvaluation.lean`
completed with no errors or warnings (the expected `sorry` warning is suppressed by
the project options).

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

Maintainer review fix (NT-cc review, 2026-10-17): the binder
`[IsIso (projectionMap (ModuleCat A) f)]`, not a hypothesis of the node, was removed and
`derivedHomRightDerivedLowerShriekIso (ModuleCat A) f` replaced by the recorded
`derivedHomRightDerivedLowerShriekIsoOfFinite A f` (the same isomorphism, by proof
irrelevance of the `IsIso` instance); the report's claim that `lem-kun-tensor-sym` had been
added to stmt_deps was corrected.  The fixed file compiles without warnings.
