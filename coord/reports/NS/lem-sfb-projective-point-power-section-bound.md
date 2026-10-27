## Worker report

The new module `Sheaf.AlgebraicGeometry.ProjectivePointPowerSectionBound` states
`AlgebraicGeometry.exists_projective_point_power_section_bound`, with one postponed proof
and no new definitions. The natural-language statement is unchanged. No additional node
or dependency repair is required.

The source read is Gieseker, *Lectures on Moduli of Curves*, Proposition 1.0.3,
printed pp.33--34, observations (i)--(iv), in the online transcription named by the node:
https://doczz.net/doc/7664568/lectures-on-moduli-of-curves---school-of-mathematics--tifr .
The DAG explicitly supplies the more general chart/jet argument, rather than assuming
Gieseker's additional family hypotheses. The proof docstring records all six DAG steps,
including the geometric-series localization calculation and the Nakayama argument.

Hypothesis and clause correspondence:

| Natural-language object or clause | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Projective embedding C in P^(r-1) | `n : ℕ`, `C : Scheme.{u}`, `i : C ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))`, `[IsClosedImmersion i]`; here r=n+1 |
| Dimension at most one | `hC : topologicalKrullDim C ≤ 1` |
| Closed point P of C | `P : C`, `hP : IsClosed ({P} : Set C)` |
| P lies on a one-dimensional irreducible component | `hcomp : ∃ Z : Set C, Z ∈ irreducibleComponents C ∧ P ∈ Z ∧ topologicalKrullDim Z = 1`; dimension uses the subtype topology |
| Coordinate Hilbert polynomial delta*m+c, delta positive | `δ c : ℚ`, `hδ : 0 < δ`, and `hpoly : ProjectiveHilbertPolynomial.IsCoordinatePolynomial k n i (Polynomial.C δ * Polynomial.X + Polynomial.C c)` |
| L=O_C(1) | `(Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) 1)` |
| Reduced point ideal ker(O_C -> k(P)) | `(C.fromSpecResidueField P).ker`; the canonical residue-field point is a closed immersion precisely when `{P}` is closed, by `isClosed_singleton_iff_isClosedImmersion` |
| Ideal power I_P^t as an O_C-module | `((C.fromSpecResidueField P).ker ^ t).toModules`; these are ideal powers, not tensor powers of the ideal |
| I_P^t tensor L^(tensor m) | The displayed ideal module tensored with the displayed L's `.tensorPow m`, explicitly typed as `C.Modules` |
| H^0 of this module | `(RingedSpace.moduleCohomology C.toRingedSpace 0).obj ...` |
| Its k-vector-space structure and dimension | `ModuleCat.restrictScalars` along `((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ projectiveSpaceProjection).appTop).hom`, then `Module.finrank k` |
| Positive integers m0,K depending only on the fixed geometric data | `∃ m₀ K : ℕ, 1 ≤ m₀ ∧ 1 ≤ K ∧ ...`, after the fixed-data binders and before m,t |
| All m>=m0 and integer 0<=t<=m | `∀ m : ℕ, m₀ ≤ m → ∀ t : ℕ, t ≤ m → ...`; natural numbers encode exactly these nonnegative integers |
| Bound delta*m-t+K | The displayed finrank cast to ℚ is `≤ δ * m - t + K`; subtraction occurs in ℚ, without truncated natural subtraction |
| Nilpotents, embedded points, disconnected C, arbitrary singularities at P allowed | No reducedness, purity, connectedness, smoothness, integrality, regularity or nodality assumption is present |

The rational coefficients are the coefficients of the already recorded predicate in
`Polynomial ℚ`; no integrality hypothesis is imposed on them. Natural m0 and K encode
exactly integers at least one. The given geometry makes the section spaces finite
dimensional, as also explained in the proof docstring, so their finrank is their ordinary
dimension. No extraneous finiteness hypothesis or extra conclusion is added.

Dependency declarations used, with the signatures and docstrings read in the sources:

- `Field` in `Mathlib.Algebra.Field.Defs` and `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` render the two field nodes.
- `AlgebraicGeometry.Scheme` and its morphisms in `Mathlib.AlgebraicGeometry.Scheme`,
  and `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `AlgebraicGeometry.ProjectiveSpace.twist` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, with the recorded
  `Scheme.Modules.tensorPullback` and `Scheme.Modules.tensorPow` APIs. The latter
  recursively uses the unit in degree zero and tensor product in the successor degree.
- `AlgebraicGeometry.RingedSpace.moduleCohomology` in
  `WeilConjectures.Topology.RingedSpaceModuleCohomology` is the recorded right-derived
  global-sections functor in O-module sheaves. It is used directly, not replaced by
  unstructured abelian-sheaf cohomology. The scalar ring is its actual global ring.
- `topologicalKrullDim` in `Mathlib.Topology.KrullDimension` and
  `irreducibleComponents` in `Mathlib.Topology.Irreducible`.
- `AlgebraicGeometry.ProjectiveHilbertPolynomial.IsCoordinatePolynomial` in
  `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`; its equations,
  coordinatePiece and coordinateDimension definitions were read in full. This is the
  eventual dimension of the coordinate quotient, not an Euler-polynomial substitute.
- `AlgebraicGeometry.Scheme.Hom.ker` and the `IdealSheafData` power operation with
  `ideal_pow` in `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` render both ideal nodes.
  `IdealSheafData.toModules` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` constructs the actual
  kernel module associated to that ideal data.

All already stated proof dependencies have imports: the homogeneous-ideal theorem,
standard charts, closed-point residue-field isomorphism (`Mathlib.AlgebraicGeometry.AlgClosed.Basic`),
localization at a prime, scheme sobriety (`Mathlib.AlgebraicGeometry.Properties`),
and Nakayama. The node `lem-sfb-coordinate-quotient-section-polynomial-tail` currently
has no Lean record or Mathlib match, so there is no recorded module to import for this
proof-only dependency. Its role is retained in the proof docstring.

Edge cases checked before writing: t=0 uses the zeroth ideal power and zeroth tensor
power conventions correctly; t=m is included with ordinary signed subtraction in the
bound. The empty C cannot have P or the specified component. Zero-dimensional C and
ambient P^0 cannot satisfy the component hypothesis; no extra lower-dimension binder is
needed. A point on an isolated zero-dimensional component alone is deliberately excluded
by hcomp. A point on a nonreduced curve or an embedded point lying on a curve component
is admitted. Disconnected extra components only affect the common constant term.
Arbitrary positive characteristic is retained. No universe equality beyond the ordinary
common universe for the field and its schemes is introduced.

Searches actually run with msearch.py for this item:

- LeanFinder: “On a projective curve sections of O(m) vanishing to order t at a point
  have dimension at most degree times m minus t plus a constant”: eight hits on
  Chevalley complexity and Weierstrass division-polynomial degrees, no matching statement.
- LeanSearch: “Dimension of sections vanishing at a point on a projective curve is
  bounded by degree times m minus order of vanishing plus a constant”: eight hits,
  mostly analytic orders and one basic-open vanishing lemma, no matching statement.
- Loogle: `Module.finrank, Ideal.pow` failed because `Ideal.pow` is not an identifier;
  the corrected `Module.finrank` query returned the dimension definition and standard
  finrank comparison lemmas, not this geometric bound.
- Mathlib grep: `point.*power|ideal.*finrank|vanish.*order` in AlgebraicGeometry returned
  one elliptic-curve point-file hit, not this statement.
- Direct rg searches for the same concepts in both `lean/WeilConjectures/AlgebraicGeometry`
  and `lean/Sheaf/AlgebraicGeometry` found twist, divisor, and other point constructions,
  but no such uniform estimate. Searching the item id in WeilConjectures found no match.
  The upstream-name index was also searched for point/section names. Existing notions
  were reused throughout, and no helper definition was introduced.

Validation: scompile.py compiled both its sandbox module and the delivered library module
cleanly. The initial elaboration required an explicit `: C.Modules` on the tensor expression
so Lean selects the existing scheme-module monoidal structure rather than attempting to
infer a structure on the definitionally equal ringed-space module category. No definition,
universe, or mathematical assumption was changed by this type annotation.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
