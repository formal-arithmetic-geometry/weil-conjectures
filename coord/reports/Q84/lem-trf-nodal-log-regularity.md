## Worker report

The module `Sheaf.SixFunctors.TraceFormula.NodalLogRegularity` states
`AlgebraicGeometry.nodal_log_regular`.  It uses the existing divisorial log-pair
predicate and the existing `HasNodalGeometricFibres` definition.  The hypotheses are
rendered as follows: `[IsLocallyNoetherian X] [CompactSpace X]` and the corresponding
classes for `Y` express quasi-compact locally Noetherian schemes; `[IsProper f]`,
`[Flat f]`, and `[LocallyOfFinitePresentation f]` express properness, flatness, and
finite presentation; `hgeom` is the connected nonempty one-dimensional geometric-fibre
and ordinary-double-point condition.  `T`, `hT`, and `hU` give a closed boundary and
its open complement `U`; `hUdense` and `hYlog` state the divisorial fine-saturated
log-regular pair on `Y`.  The hypothesis
`hfsmooth : ∀ x : X, f x ∉ T → x ∈ f.smoothLocus` states that `f` is smooth
over `Y \ T`: every point above the open complement lies in the smooth locus.
`hD` is the effective Cartier center, `hDsmooth` places it
in the smooth locus, and `[Etale (i ≫ f)]` gives the etale marking over `Y`.

The conclusion uses exactly `B = Set.range i ∪ f ⁻¹' T`: it asserts
`IsNowhereDense B`, then supplies an open `V` with `(V : Set X) = Bᶜ`, a dense-range
inclusion `V.ι`, and `IsDivisorialFineSaturatedLogRegularPair X V V.ι`.  Thus every
clause of “B is nowhere dense and (X,B) is log regular” is explicit.  The proof is
`sorry` as required at stage 2.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.LogRegularPair`,
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`;
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`,
  `AlgebraicGeometry.HasNodalGeometricFibres`;
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`;
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`;
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`;
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`;
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Scheme.Hom.smoothLocus` (the pointwise smooth locus);
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`,
  `AlgebraicGeometry.IsEffectiveCartierCenter`.

Edge cases checked: the `HasNodalGeometricFibres` predicate includes nonempty fibres
and allows arbitrary algebraically closed fields in the scheme universe; `T = ∅`
reduces to the smooth-boundary case, while the log-pair density hypothesis excludes
`T = Y` for nonempty `Y`; an empty marking is represented by an empty `D` and empty range; no
characteristic or positive-dimension restriction is added.  The open complement is
bound explicitly, so no choice of a noncanonical open is hidden.

Searches for an existing statement or definition: `msearch.py ... leanfinder
"log regularity of a marked nodal curve over a log regular pair"` returned only generic
smoothness declarations (no match); `msearch.py ... loogle
"IsDivisorialFineSaturatedLogRegularPair, HasNodalGeometricFibres"` returned zero hits;
`msearch.py ... grep "nodal|log regular|IsDivisorial" AlgebraicGeometry` returned
zero hits.  Direct `rg` over `WeilConjectures/` found no `nodal_log_regular`; direct
`rg` over `lean/Sheaf` found only the two dependency definitions.  No existing
statement was found.

## Second reading by Q84

I reread the node and the module line by line.  The two scheme hypotheses, all three
morphism properties, the geometric-fibre condition, closed boundary and complement,
log-regular base pair, smoothness over the boundary complement, effective Cartier
marking, smooth-locus containment, and etale marking each have a corresponding
Lean binder. The conclusion has both the nowhere dense assertion and the explicit open complement carrying the divisorial log-regular
pair.  No hypothesis or conclusion clause is omitted, strengthened, or weakened.


## Repair H3

The returned head `b79d6c216cbe` omitted the node's assumption that `f` is smooth
over `Y \ T`. The retained packet initially passed the mechanical dry run, but its
signature still had that omission. Added
`(hfsmooth : ∀ x : X, f x ∉ T → x ∈ f.smoothLocus)` to the theorem and its
verbatim `lean.statement`, and added the explicit Smooth module import.
The node already includes this hypothesis, so its mathematical statement needs no
correction. Compared with current main, the retained node only adds its Lean record
and the already landed `def-trf-nodal-geometric-fibres` statement dependency.

The Mathlib source defines `f.smoothLocus` as the points where the stalk map is
formally smooth. Under the existing local finite presentation assumption,
`exists_smooth_of_formallySmooth_stalk` identifies these with points having a smooth
neighbourhood. Thus `hfsmooth` expresses exactly smoothness over the complement,
without requiring smoothness above `T`. For `T = ∅`, it requires smoothness everywhere;
for an empty source it is vacuous. The marking's separate `hDsmooth` hypothesis is
retained. Every conclusion clause is unchanged. The self-check now accounts for
this previously omitted hypothesis.

Validation: the repaired module compiles cleanly through `scompile.py`, both as
a sandbox probe and at its library module path. The signature matches the node
record verbatim, all binders are explicit, and the single proof remains `sorry`.
