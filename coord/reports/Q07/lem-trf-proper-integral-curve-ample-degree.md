## Worker report

The module `Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree` states
`AlgebraicGeometry.Scheme.Modules.proper_integral_curve_isAmple_iff_degree_pos` with proof
postponed by `sorry`. It uses the proper-curve data exactly as follows: `k : Type u` with
`[Field k]` is the field hypothesis; `[C.Over (Spec (.of k))]` gives the structure morphism;
`[IsIntegral C]` renders integrality; `[IsProper (C ↘ Spec (.of k))]` renders properness over
`k`; `hdim : topologicalKrullDim C = (1 : WithBot ℕ∞)` renders topological Krull dimension one;
`N : C.Modules` and `[N.IsInvertible]` render the invertible module. The conclusion is the
absolute predicate `Scheme.Modules.IsAmple C N` iff the positivity inequality
`0 < Scheme.Modules.degree k N`, where `degree` is the recorded Euler-characteristic degree.
No smoothness or geometric-integrality hypothesis is introduced.

The statement dependencies used are Mathlib `Field`, `AlgebraicGeometry.IsIntegral`,
`AlgebraicGeometry.IsProper`, and `topologicalKrullDim`; the project declarations
`AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsAmple`,
and `AlgebraicGeometry.Scheme.Modules.degree` are imported from their recorded modules
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`WeilConjectures.AlgebraicGeometry.Ample`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.

Edge cases checked against the node and source: the dimension hypothesis is exactly one (so
zero-dimensional schemes are excluded), no smoothness or geometric integrality is assumed, the
invertible module may have any degree including zero or negative degree, and the absolute
ampleness predicate retains its compactness and affine nonvanishing-locus clauses. The source
proof's tensor-power-zero and nonempty-integral-curve cases are represented by the existing
`IsAmple` and `degree` definitions and are not dropped from the theorem statement.

Searches for an existing declaration (actual wrapper results are in `searches.jsonl`):

- `msearch.py` LeanSearch, query `An invertible sheaf on a proper integral curve is ample if
  and only if its Euler characteristic degree is positive`: eight hits, including
  `AlgebraicGeometry.instIsProperOfIsFinite`, `Module.Invertible.instProjective`, and Proj
  structure-sheaf declarations. None has this statement.
- `msearch.py` LeanFinder, query `An invertible sheaf on a proper integral curve over a field is
  ample if and only if its degree is positive`: eight hits about integral schemes, function
  fields, and Proj affine basic opens; none states the criterion.
- `msearch.py` Loogle, query `"IsAmple"`: zero hits.
- `msearch.py` grep, query `\b(IsAmple|isAmple|ample|ampleness)\b`, subdirectory
  `AlgebraicGeometry`: zero hits in Mathlib.
- `rg` for `isAmple_iff_degree_pos|ample.*degree|degree.*ample|proper_integral_curve_isAmple`
  in the source's `WeilConjectures/AlgebraicGeometry` and the shared `lean/Sheaf/AlgebraicGeometry`
  found the related `AlgebraicGeometry.Scheme.isAmple_iff_degree_pos` in
  `Curve/RiemannRoch.lean`. Reading its full section showed the extra
  `SmoothOfRelativeDimension 1` and `GlobalSectionsBijective` assumptions. It uses
  `AlgebraicGeometry.IsAmple`, whereas this node uses the recorded absolute predicate.
  The nearby Hilbert-degree results prove only the forward implication. The shared library
  contains the consumer `isAmple_iff_normalizedComponentDegree_pos`, not this criterion.
- `grep -rn "lem-trf-proper-integral-curve-ample-degree"` in the source repository returned no
  match. `rg` for the proposed declaration name in Mathlib, the source, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` returned no match.

I read Stacks `varieties.tex`, `lemma-ample-curve` (Tag 0B5X), including its full proof.
All statement dependencies have usable interfaces; no definition or dependency repair is needed.
The three proof dependencies `lem-trf-curve-degree-tensor-additive`,
`lem-trf-curve-section-degree-positivity`, and `lem-trf-ideal-twist-vanishing-implies-ample`
have no recorded Lean module yet and so cannot be imported; their steps and names are retained
in the proof docstring for later stage-3 use. The remaining stated proof dependencies are imported
without `public`, including the current upstream modules when a shared source file is absent.
No node statement was changed and no `STATEMENT-DISPUTED` issue was found.

## Second reading by Q07

I reopened the node JSON and the module. The field, structure morphism, integrality, properness,
one-dimensional Krull hypothesis, and invertibility each match one hypothesis of the node. The
left side uses the canonical absolute `Scheme.Modules.IsAmple C N`; the right side uses the
canonical `Scheme.Modules.degree k N` (`χ(C,N)-χ(C,O_C)`), so every conclusion clause is present.
The module adds no smoothness, geometric-integrality, or auxiliary global-sections condition.
The only elaboration adjustment from the prose is the standard Lean encoding of “proper over k”
as the `IsProper` typeclass on `C ↘ Spec (.of k)` and of “invertible module” as
`[N.IsInvertible]`.


This second pass also checked the dependency definitions themselves: `IsIntegral` includes
nonemptiness and the domain condition, `IsProper` includes universally closed and locally finite
type (with quasi-compactness yielding finite type), `IsInvertible` means Zariski locally rank one,
`topologicalKrullDim` is the chain dimension, `IsAmple` includes compactness and the positive
powers' affine nonvanishing loci, and `degree` is definitionally the difference of Euler
characteristics. The proof docstring was expanded to the node's nine numbered steps and the
module path moved to the required algebraic-geometry topic directory. This is a second reading
by the same dispatcher-started worker; no independent worker was started, as required by the
brief. The maintainer's independent delivery review is still required.
