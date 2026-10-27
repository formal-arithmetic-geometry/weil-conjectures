## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothNongenericPuncturedLineTriviality` states
`AlgebraicGeometry.smooth_nongeneric_punctured_line_triviality`, with its sole proof
`sorry`. No definitions, new nodes, dependency repairs, or statement changes are needed.
Only the item's `lean` field changes. The module includes the five-step proof plan of
the node in its theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- Schemes S and X: `{S X : Scheme.{u}}`. The arbitrary universe u is explicitly bound.
- S locally Noetherian: `[IsLocallyNoetherian S]`.
- S normal in the stated local-ring sense: `hS : ∀ s : S,
  IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)`.
  Both domain and integrally closed are retained; no excellence is imposed.
- Smooth morphism: `(f : X ⟶ S) [Smooth f]`.
- Arbitrary point and its base point: `(x : X)` and `f x`.
- The scheme-theoretic fibre is `f.fiber (f x)`, defined in Mathlib as the pullback
  of f along `S.fromSpecResidueField (f x)`. Thus the node's residue field and
  fibre product are the recorded Mathlib constructions, not substitutes.
- The corresponding point of that fibre is the canonical `f.asFiber x`.
  Its composite with the fibre inclusion is x by `Scheme.Hom.fiberι_asFiber`.
- Dimension at least two: `hdim : 2 ≤ ringKrullDim (X.presheaf.stalk x)`.
- Not generic in any fibre component: `hng : ∀ C : Set (f.fiber (f x)),
  C ∈ irreducibleComponents (f.fiber (f x)) → ¬ IsGenericPoint (f.asFiber x) C`.
  This tests every irreducible component of the actual scheme-theoretic fibre.
- R is the actual local ring `X.presheaf.stalk x`. The existing
  `AlgebraicGeometry.puncturedSpectrum R` is the open complement of
  `IsLocalRing.closedPoint R` in `Spec (CommRingCat.of R)`; that point has ideal
  `IsLocalRing.maximalIdeal R`. Its `.toScheme` is precisely U with restricted
  structure sheaf. The existing definition applies to every local ring despite
  its hosting module's curve-specific title; no dimension-one hypothesis occurs
  in its signature or definition.
- Every invertible O_U-module: `(L : (puncturedSpectrum
  (X.presheaf.stalk x)).toScheme.Modules) [L.IsInvertible]`, using the recorded
  `Scheme.Modules.IsInvertible`, not a second local-freeness predicate.
- Isomorphic to O_U: `Nonempty (L ≅ SheafOfModules.unit _)`. The unit is the
  structure sheaf as a module over itself; `Nonempty` expresses existence of
  an isomorphism, without choosing a trivialization.
- The last sentence is respected literally: there is no closed-point,
  finite-extension, connectedness, quasi-compactness, or global finiteness binder.

Dependency declarations and their source modules were read, including their
signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain`, used as the normal-domain conjunction prescribed by the node record.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its projections.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.fromSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberHomeo`, `asFiber`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (the dependency has
  `mathlib_match`, which is used directly).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches`:
  `AlgebraicGeometry.puncturedSpectrum`, reused unchanged.

Already stated proof dependencies are imported privately:
`Mathlib.RingTheory.Localization.AtPrime.Basic` (`Localization.AtPrime`),
`Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent`
(`AlgebraicGeometry.invertible_affine_limit_descent`), and
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
(`AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
publicly imported tensor pullback). The remaining six geometric/local proof
inputs currently have no recorded Lean module and therefore supply no import.
No import cycle is introduced.

Source check: read the online English EGA translation at
https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html,
Proposition 21.14.3(i), FIRST assertion, and Proposition 21.13.8.
The first gives parafactoriality under exactly these hypotheses, and 21.13.8(ii)
is Pic(U)=0. The separate prime-cycle assertion is not substituted. The web
reader rejected the large page, so it was read using an HTTP request and HTML
text extraction in memory. No external source files were written.

Edge cases checked before drafting:

- Empty X admits no x; empty S also admits no such pointed morphism. Neither
  scheme is required to be globally nonempty.
- Dimension zero or one fails hdim and is not accidentally covered; dimension
  two is included. The dimension expression uses the extended Krull-dimension
  codomain and imposes no finite dimension assumption.
- Generic fibre points are excluded by hng, while arbitrary nonclosed nongeneric
  points and infinite residue extensions remain allowed. For example a
  codimension-two point of affine three-space over a field can have a
  transcendental residue field and is included.
- Disconnected normal locally Noetherian bases and smooth schemes are allowed:
  normality is checked on each base stalk and genericity on each fibre component.
- Singular normal bases are retained: hS is normality, not regularity. Thus this
  is not a replacement by the simpler regular-local factorial case.
- The puncture removes exactly the maximal ideal, not its generic point, a
  chosen principal divisor, or the whole closed fibre.
- The invertibility predicate is locally rank-one freeness, whose quasi-coherence
  is automatic; it places no extra condition beyond the node's invertible module.

Searches for duplicates (2026-10-24):

1. `msearch.py ... leanfinder "Smooth morphism over normal locally Noetherian base
   line bundles on punctured local spectrum at nongeneric fiber point are trivial"`:
   eight hits, on smooth charts and relative smoothness, including
   `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth` and
   `Algebra.IsSmoothAt.exists_notMem_smooth`. None is the punctured Picard theorem.
2. `msearch.py ... loogle '"Picard", "IsLocalRing"'`: zero hits.
3. `msearch.py ... grep 'parafactorial|punctured.*[Pp]icard|[Pp]icard.*punctured'`:
   zero Mathlib hits.
4. `msearch.py ... leansearch "Line bundles on punctured spectra at nongeneric
   fiber points of smooth morphisms over normal locally Noetherian schemes are
   trivial"`: eight unrelated topological vector-bundle trivialization hits.
5. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for parafactoriality,
   nongeneric punctured triviality, and the intended declaration name: no existing
   theorem. The parent `RamanujamSamuelPrimeDivisor.lean` cites this node in its
   proof docstring but does not state it.
6. `rg` over Mathlib, upstream, and project algebraic geometry for punctured
   spectrum definitions found upstream `AlgebraicGeometry.puncturedSpectrum`,
   reused here. `rg` over the DAG for that name found no competing definition.
7. `rg` for fibre definitions found Mathlib `Scheme.Hom.asFiber`, eliminating any
   need for an arbitrary fibre-point binder or helper construction.

Validation: `scompile.py Q20 lem-sfb-smooth-nongeneric-punctured-line-triviality`
compiled the delivery in sandbox module mode (2.8 s) and under its library module
name (2.3 s), with no errors or non-sorry warnings. All variables and the universe
are bound explicitly; the maximum source line width is below 101 characters.
There is no `STATEMENT-DISPUTED` flag or identified node fault.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
