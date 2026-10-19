## Worker report

The module `lean/Sheaf/TraceFormula/PointedGenusZeroProjectiveLine.lean` states
`AlgebraicGeometry.isProjectiveLine_of_genus_zero_degree_one`.  It has no definitions and
its proof is the required `sorry`.  The theorem is the degree-one specialization of
Stacks Tag 0C6T, and concludes an isomorphism in `Over (Spec k)` with
`AlgebraicGeometry.ProjectiveLine (Spec k)`.

The Lean rendering of each hypothesis and clause is as follows.

* `k` is `(k : Type u) [Field k]`, using Mathlib's `Field`.
* `C` is `(C : Scheme.{u}) [C.Over (Spec (.of k))]`; the latter is the structure
  morphism over the field.
* Properness is `[IsProper (C ↘ Spec (.of k))]`, using Mathlib's `IsProper`.
* Integrality, finite type, separatedness, and dimension one are the recorded curve
  notion `[IsIntegralCurve (C ↘ Spec (.of k))]`.
* The canonical map on global functions is
  `h₀ : Function.Bijective (Scheme.globalSectionsRingHom k (X := C))`.
* The vanishing `H^1(C, O_C) = 0`, with the node's ringed-space-module cohomology,
  is `h₁ : Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace 1).obj
  (Scheme.Modules.unit C))`.
* The invertible module is `(M : C.Modules) [M.IsInvertible]`, and its degree-one
  clause is `hdeg : Scheme.Modules.degree k M = 1`.
* “Isomorphic over k to P^1” is
  `Nonempty (Over.mk (C ↘ Spec (.of k)) ≅ Over.mk
  (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))`.

The statement imports the recorded declarations used by these clauses:

* `AlgebraicGeometry.IsIntegralCurve` from
  `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`;
* `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
* `AlgebraicGeometry.RingedSpace.moduleCohomology` from
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`;
* `AlgebraicGeometry.Scheme.Modules.IsInvertible` from
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
* `AlgebraicGeometry.Scheme.Modules.degree` from
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`;
* `AlgebraicGeometry.ProjectiveLine` from
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.

`AlgebraicGeometry.Scheme.globalSectionsRingHom` is the source declaration of the
canonical map in the `h₀` clause.  Mathlib's `Field` supplies the field dependency.
The proof docstring records the source route: finite-dimensional cohomology and
Euler characteristic, the zero scheme of a nonzero section, the monomial basis of the
section ring, the canonical Proj open immersion, and properness plus irreducibility.

I checked the edge cases covered by the statement: the field is arbitrary (including
imperfect fields and characteristic two), no algebraic-closure or smoothness assumption
is added, degree is exactly one, and the curve is nonempty through `IsIntegralCurve`.
The conclusion uses the two homogeneous coordinates `ULift (Fin 2)` in the existing
`ProjectiveLine` definition.  The zero cohomology clause is stated as `Subsingleton`,
which also covers the zero module without choosing an element.

Searches for an existing statement or duplicate notion were made with:

* `msearch.py ... leanfinder "proper integral curve genus zero degree one invertible
  sheaf projective line"`: eight hits, all Weierstrass-curve declarations; no match.
* `msearch.py ... loogle "IsIntegralCurve, ProjectiveLine, Modules.degree"`: no hits;
  Loogle reported unknown identifier `ProjectiveLine`.
* `msearch.py ... grep "genus.*degree.*projective|ProjectiveLine.*IsIntegralCurve"
  AlgebraicGeometry`: zero hits.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for the theorem/item name and for
  `genus_zero_degree_one`: no existing declaration.

The existing `Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero` theorem is a converse
statement about the standard projective line over an algebraically closed field and
has no degree-one classification conclusion, so it is not a duplicate.

## Second reading by NI

I reopened the node and the module and checked every binder against the node.  The field,
proper integral curve, canonical global-sections isomorphism, first-cohomology vanishing,
invertible module, degree-one hypothesis, and projective-line conclusion all occur once.
`IsIntegralCurve` supplies the node's integral curve convention; `IsProper` supplies the
properness clause; `moduleCohomology` is used exactly for the specified cohomology notion;
and `Over` makes “over k” explicit.  No hypothesis or conclusion was added, dropped,
weakened, or strengthened.  No statement correction or new node is needed.

## Saved-packet repair

The initial dry run rejected the trailing `:=` in `lean.statement`; the record now
ends at the conclusion, matching the signature extracted by preflight. The cohomology
import now uses the upstream module recorded in the current dependency node, read
through `scompile.py --source`. I rechecked the current curve, degree, invertibility,
properness, cohomology and projective-line declarations against every hypothesis and
the over-field conclusion. The theorem signature and the node statement are unchanged.
