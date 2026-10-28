# WeilConjectures.NativeCoefficientCohomology.Pairs, exceptionalConstant, twistedConstant

## Reason

Separate the endpoint definitions from their comparison theorem so that the two
independent endpoint lemmas can import the definitions without an import cycle.
The three declaration names, signatures and definition bodies stay identical.
The original module publicly imports the new endpoint module, preserving its public API.
Local auxiliary instances move with their unchanged definitions; the original proof
reactivates nativeStructureOver locally. No definition used by a target changes meaning.

## Old

In lean/Sheaf/WeilSheaf/CoefficientCohomologyComparison.lean:

```lean
abbrev Pairs :=
  Endofunctor.IsoAlgebra (sourceFrobenius P.field P.coefficients.l
    P.coefficients.different P.coefficients.Qbar X₀)

variable (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

/-- The ordinary exceptional constant pair, with the inverse-exchange adjunction mate.
Source: constant-purity Frobenius square, G(theta_0) e.
(blueprint: lem-sf-native-coefficient-cohomology-comparison) -/
def exceptionalConstant : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let G := (operation D l hl Ω X₀ (point D) (pointMap D X₀) c₀ S .closed).G
  let K := unit D l hl Ω (D.geometricFiber (point D)).left
  Endofunctor.IsoAlgebra.mk (G.obj K)
    ((exceptionalIso D l hl Ω X₀ (point D) (pointMap D X₀) c₀ S).app K ≪≫
      G.mapIso (constantWeilAlgebraicallyClosedComplex l D hl (point D) Ω).str)

/-- The purity-source pair, with its canonical constant, Tate and shift Frobenius.
It exists on any separated finite-type model, with no smoothness assumption.
Source: constant-purity Frobenius square, H(Lambda), theta_H,can.
(blueprint: lem-sf-native-coefficient-cohomology-comparison) -/
def twistedConstant (d : ℕ) : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  Endofunctor.IsoAlgebra.mk
    ((source D l hl Ω X₀ (point D) (pointMap D X₀) d).obj
      (unit D l hl Ω (D.geometricFiber (point D)).left))
    (canonicalSourceTheta D l hl Ω X₀ (point D) (pointMap D X₀) d)
```

## New

In lean/Sheaf/WeilSheaf/CoefficientEndpointObjects.lean, reexported publicly by the old module:

```lean
abbrev Pairs :=
  Endofunctor.IsoAlgebra (sourceFrobenius P.field P.coefficients.l
    P.coefficients.different P.coefficients.Qbar X₀)

variable (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)

/-- The ordinary exceptional constant pair, with the inverse-exchange adjunction mate.
Source: constant-purity Frobenius square, G(theta_0) e.
(blueprint: def-sf-coefficient-endpoint-objects) -/
def exceptionalConstant : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let G := (operation D l hl Ω X₀ (point D) (pointMap D X₀) c₀ S .closed).G
  let K := unit D l hl Ω (D.geometricFiber (point D)).left
  Endofunctor.IsoAlgebra.mk (G.obj K)
    ((exceptionalIso D l hl Ω X₀ (point D) (pointMap D X₀) c₀ S).app K ≪≫
      G.mapIso (constantWeilAlgebraicallyClosedComplex l D hl (point D) Ω).str)

/-- The purity-source pair, with its canonical constant, Tate and shift Frobenius.
It exists on any separated finite-type model, with no smoothness assumption.
Source: constant-purity Frobenius square, H(Lambda), theta_H,can.
(blueprint: def-sf-coefficient-endpoint-objects) -/
def twistedConstant (d : ℕ) : Pairs P X₀ :=
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  Endofunctor.IsoAlgebra.mk
    ((source D l hl Ω X₀ (point D) (pointMap D X₀) d).obj
      (unit D l hl Ω (D.geometricFiber (point D)).left))
    (canonicalSourceTheta D l hl Ω X₀ (point D) (pointMap D X₀) d)
```

## Users

`tools/downstream.py` reports 101 downstream modules and three modules mentioning
these endpoint names. The snapshot direct import search finds two consumers; current server preflight
found CoefficientShiftedTateComparison as a third consumer.
Every declaration remains available through the original module, with unchanged bodies.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.WeilSheaf.CoefficientCohomologyComparison | F4 | Publicly reexports the moved definitions; theorem statement unchanged. |
| Sheaf.WeilSheaf.SmoothCoefficientVanishing | K2 | No source change required; original consumer compiled against the delivery. |
| Sheaf.WeilSheaf.SmoothDualizingCohomology | unclaimed | No source change required; original consumer compiled against the delivery. |
| Sheaf.WeilSheaf.CoefficientShiftedTateComparison | V5 | New consumer found on current server; definitions and public API unchanged. Original compiled against the delivery. |

No existing consumer module is adapted or delivered.

## Status

landed 20261028T055647-L-791621 2026-10-28 (merge of deliver/F4/Sheaf.WeilSheaf.CoefficientCohomologyComparison)
