## Worker report

I stated `AlgebraicGeometry.exists_geometricallyIntegral_connectedComponent` in
`lean/Sheaf/TraceFormula/SmoothComponentPureTranscendental.lean`.
The source is Stacks Project `literature/stacks-project/more-morphisms.tex`, Tag 057K,
proof paragraph beginning “Let T be the connected component”; the module and declaration
docstrings identify this source and blueprint node.

The theorem uses `k : Type u` with `[Field k]`, a scheme `C : Scheme.{u}` with
`[C.Over (Spec (.of k))]`, `[LocallyOfFiniteType (C ↘ Spec (.of k))]`,
`[QuasiCompact (C ↘ Spec (.of k))]`, and `[Smooth (C ↘ Spec (.of k))]`. These render,
respectively, the field, the `k`-scheme, finite type (locally finite type plus
quasi-compact), and smoothness hypotheses of the node. The point is `(c : C)`.
The residue-field hypothesis is

```
(htrans : @Algebra.IsPurelyTranscendentalExtension k (C.residueField c) _ _
  ((C ↘ Spec (.of k)).residueFieldAlgebraMap c).toAlgebra)
```

which is the canonical `k`-algebra structure on `κ(c)` induced by the structure morphism,
and uses the existing definition node `def-trf-purely-transcendental-extension`.

The conclusion is

```
∃ T : C.Opens,
  (T : Set C) = connectedComponent c ∧
    QuasiCompact T.ι ∧
      GeometricallyIntegral (T.ι ≫ C ↘ Spec (.of k))
```

The `C.Opens` witness is an open subscheme; equality with `connectedComponent c` renders
“the maximal connected subset containing `c`”. `QuasiCompact T.ι` renders that this open
component is quasi-compact. `T.ι ≫ C ↘ Spec (.of k)` is the structure morphism of the
open subscheme, and `GeometricallyIntegral` renders geometric integrality over `k`.
No hypothesis or conclusion was added beyond the node; the finite-type condition is
written as both Mathlib classes because the recorded finite-type dependency defines it as
that conjunction.

The statement dependencies and declarations used are:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` (imported through the algebraic
  geometry modules).
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Smooth` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-residue-field`: Mathlib `AlgebraicGeometry.Scheme.residueField` from
  `Mathlib.AlgebraicGeometry.ResidueField`; the canonical base-field map is the existing
  `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap` from `WeilConjectures.ZetaSeries`.
- `def-weil-open-immersion`: Mathlib `AlgebraicGeometry.Scheme.Opens.toScheme` and
  `AlgebraicGeometry.Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict`.
- `def-pc-geometrically-irreducible`: Mathlib `AlgebraicGeometry.GeometricallyIntegral`
  from `Mathlib.AlgebraicGeometry.Geometrically.Integral` (the recorded dependency
  repair documents the specialization to a structure morphism over a field).
- `def-pc-integral-scheme`: Mathlib `AlgebraicGeometry.IsIntegral`, used by the
  geometric-integrality class.
- `def-trf-purely-transcendental-extension`: project declaration
  `Algebra.IsPurelyTranscendentalExtension` in
  `Sheaf.FieldTheory.PurelyTranscendentalExtension`.

The proof dependency declarations are not used in the sorry body, but the module imports
all statement-side notions and the canonical residue-field map. The source proof steps
are carried in the theorem docstring: Noetherianity gives openness and quasi-compactness;
pure transcendence gives geometric connectedness; smoothness gives geometric normality;
and normal Noetherian connected base changes are integral.

I checked edge cases from the source and statement: `r = 0` gives the trivial extension
`κ(c) ≅ k`; the component is nonempty because it contains `c`; an empty scheme cannot
supply `c`; and the open-subscheme witness has the same point set as the connected
component. The universes use one common `u` for `k`, `C`, and the residue field, as in the
Mathlib scheme-over-field conventions, and no independent smaller test universe is
introduced.

Searches made:

- `msearch.py ... leanfinder "a smooth finite type scheme over a field has an open quasi-compact
  geometrically integral connected component at a point with purely transcendental residue
  field"`: eight hits, led by `AlgebraicGeometry.IsIntegral` and residue-field infrastructure;
  no theorem for this component statement.
- `msearch.py ... loogle "GeometricallyIntegral, connectedComponent, QuasiCompact"`: zero hits
  (unknown identifier `GeometricallyIntegral` in the Loogle query); no exact declaration.
- `msearch.py ... grep
  "connectedComponent.*GeometricallyIntegral|GeometricallyIntegral.*connectedComponent"
  Mathlib`: zero hits.
- `msearch.py ... leanfinder "purely transcendental field extension finite variables"`: eight
  general transcendence results; no predicate definition.
- `msearch.py ... loogle "PurelyTranscendental, FractionRing MvPolynomial"`: zero hits, unknown
  identifier `PurelyTranscendental`.
- `msearch.py ... grep "PurelyTranscendental|purelyTranscendental" Mathlib`: zero hits.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration of this component
  theorem; the only relevant project notion is the already-recorded
  `Algebra.IsPurelyTranscendentalExtension`.
- `grep -rn "lem-trf-smooth-component-pure-transcendental"` found no existing source declaration.
- DAG search found the existing `def-trf-purely-transcendental-extension` node, so no duplicate
  definition node was created.

The required `scompile.py` check passed with no errors or warnings (the expected
`sorry` warning is suppressed by the project options).

## Second reading by Q23

I reread the target node, all eight statement dependencies, their recorded declarations,
and the module signature. The Lean binders preserve the field, finite-type, smoothness,
residue-field, and point hypotheses. The existential `C.Opens` witness, its equality to
`connectedComponent c`, `QuasiCompact T.ι`, and geometric integrality of the composed
structure morphism account for every conclusion clause. The added statement dependency is
only the pre-existing purely-transcendental definition required by the residue-field
hypothesis. No statement correction, dependency repair, or `STATEMENT-DISPUTED` flag is
needed.


## Maintainer second-reader corrections

The independent maintainer review found the mathematical signature correct. The complete
replacement module keeps that signature and its sole `sorry` proof unchanged. It adds
private imports for the recorded proof dependencies with available declarations, including
`WeilConjectures.Mathlib.Topology.NoetherianSpace` and
`Sheaf.AlgebraicGeometry.RegularNormalDecomposition`, and imports the Mathlib proof tools
privately. Its theorem docstring now spells out all four proof steps and names every
proof-dependency node. These are H8/H9 documentation/import repairs, not a statement change.

The arbitrary-basis pure-transcendence predicate is equivalent here to the node's finite-basis
condition: residue fields of points of a finite type scheme are finitely generated field
extensions, hence an algebraically independent generating set is finite. The component is
closed as well as open; its inclusion is quasi-compact, and the ambient scheme is
quasi-compact, so the asserted inclusion condition supplies precisely the required
quasi-compact component without an extra assumption.
