## Worker report

The module `Sheaf.AlgebraicGeometry.SemitraitPotentialReducedNormalization` states
`AlgebraicGeometry.exists_finite_extension_semitrait_normalization`, with `sorry` as its
whole proof. Its three definitions only assemble existing canonical constructions:
`semitraitNormalization f L` is the componentwise normalization of the reduction of
`Z ×_Spec(R) Spec(integralClosure R L)`; `semitraitNormalizationMap` is the normalization
map composed with the reduction immersion; `semitraitNormalizationStructure` composes
that map with the second pullback projection. No choice of an unspecified model or map
occurs. The theorem docstring carries every proof step from the node.

Hypotheses and clauses, read against the node:

- The commutative Noetherian integrally closed domain R is rendered by `CommRing R`,
  `IsDomain R`, `IsNoetherianRing R`, and `IsIntegrallyClosed R`.
- Dimension one is exactly `hdim : ringKrullDim R = 1`; semilocality is
  `Finite (MaximalSpectrum R)`.
- K is a fraction field through `Field K`, `Algebra R K`, and `IsFractionRing R K`.
  S is the actual `Spec (.of R)`, rather than a separately chosen isomorphic scheme.
- The finite family has arbitrary index universe v: `I : Type v`, `Finite I`,
  `Z : I → Scheme.{u}`, and the specified structure maps `f`.
- For each i, `Flat (f i)`, `LocallyOfFiniteType (f i)`, `QuasiCompact (f i)`, and
  `IsSeparated (f i)` state exactly the flat finite-type separated hypotheses.
  The definition of `IsSeparated` is that `pullback.diagonal (f i)` is a closed immersion.
- `hgeom` quantifies over each field extension E/K and every point of the base-changed
  generic fibre. Its stalk must satisfy both `IsDomain` and `IsIntegrallyClosed`.
  The generic fibre is formed first over K and then over E, using the second projection.
- The conclusion existentially supplies L, its field structure, its K- and R-algebra
  structures, `IsScalarTower R K L`, and `FiniteDimensional K L`. The scalar tower only
  states that the R-action is the composite R → K → L, as required for this base change;
  it does not assert an additional mathematical hypothesis on the input.
- R_L is Mathlib's actual `integralClosure R L` subalgebra. T is its spectrum.
  No excellence or finiteness of the R-module R_L is included.
- N_i is exactly `semitraitNormalization (f i) L`, whose definition uses the recorded
  reduction and componentwise normalization, including the empty-component coproduct.
- `IsFinite` and `Surjective` are applied to the canonical normalization/reduction map,
  not to an arbitrary map or only to a structure morphism.
- The next conjunction quantifies over all stalks of N_i and requires `IsDomain` and
  `IsIntegrallyClosed`. It permits disconnected and empty normal schemes.
- `Flat`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` applied to
  `semitraitNormalizationStructure (f i) L` state the four properties over T.
- `GeometricallyReduced` of that structure map means that every field-valued pullback
  is reduced. This is equivalent to every field-valued fibre being geometrically
  reduced: further field extension composes the field-valued map to T. In the reverse
  direction use the identity extension. Thus the node's full clause is retained.
- The final `IsIso` is the base change of the actual canonical map by
  `Spec L → Spec R_L`, formed with `Over.pullback` and `Over.homMk ... rfl`.
  Its target is `(Z_i ×_S T) ×_T Spec L`, canonically `(Z_i)_L`; its source is `(N_i)_L`.
  Consequently this is the node's generic-fibre map, not an abstract existence of an iso.
- The existential L precedes `∀ i`, so the same extension works for the entire family.

Edge cases checked before writing: I may be empty (`Finite`, no `Nonempty`); Z_i and
individual fibres may be empty; no `IsIntegral` hypothesis or conclusion on a whole
scheme excludes disconnected or empty cases; L/K may have degree one; inseparable field
extensions and arbitrary characteristic are allowed. Field tests live in the scheme/ring
universe u, never in an independent smaller universe. All ring and scheme constructions
remain in u, and the family index is independent. Since finite extensions have small
models in the universe of K, choosing L in u does not restrict the existence assertion.
There are no auto-bound variables or universe variables, no let binders in the statement,
and no new axiom. No statement correction or mathematical dispute was needed.

Dependency declarations read in their recorded source modules and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed` (domain condition and stalkwise conjunction as in its recorded inline form).
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType` (also `QuasiCompact`; finite type is the conjunction).
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-weil-pbc-scheme-reduction`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` (also `Scheme.nilradical` and `subschemeι`).
- `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`, `AlgebraicGeometry.Scheme.reducedNormalization` (also `Scheme.fromReducedNormalization`).
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.

All proof dependencies with recorded Lean modules are imported without `public`;
statement dependencies are imported publicly. Still-unstated proof dependencies are
listed by name in the proof docstring; they introduce no missing notion in the statement.
The withdrawn `CompactObject.lean` example was inspected along with its current upstream
binding; the delivery uses the required module/public-section format.

Searches for an existing statement and for duplicate helper names:

- msearch LeanFinder: "finite field extension normalization semilocal Dedekind scheme
  geometrically reduced fibres" returned eight hits on geometric reducedness and
  categorical normalization, none stating the finite-extension theorem.
- msearch Loogle: "AlgebraicGeometry.Scheme.reducedNormalization, IsDedekindDomain,
  IsGeometricallyReduced" returned no hits (the project-specific normalization name is
  unknown to the Mathlib search service).
- msearch grep in Mathlib/AlgebraicGeometry: "semitrait|potential.*[Rr]educed|
  [Gg]eometrically[Nn]ormal" returned no hits.
- msearch LeanSearch: "normalization finite field extension Dedekind base geometrically
  reduced fibres" returned eight hits, including algebraic geometric reducedness and
  normalization of a morphism, but no matching statement.
- rg in WeilConjectures and Sheaf searched semitrait, potential reducedness, geometric
  normality/reducedness, and the exact item id. No matching theorem exists. The related
  `integralClosure.semilocal_normalization_dim_one` concerns the base ring's normalization
  in its own fraction field, not normalized families or a potential reduced-fibre result.
- rg in Mathlib/AlgebraicGeometry, WeilConjectures, Sheaf, and the upstream names index
  checked the chosen declaration names. No duplicate names were found. A search for
  `nilradical.subscheme.reducedNormalization` and its corresponding map found no existing
  assembly helper. Existing reduction and normalization definitions are reused directly.

Primary source checked: Anantharaman's original scan, Appendix II, Theorem 1 and
Corollary 2, printed p.73 (PDF page index 69):
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf . The finite-type corollary gives the
finite field extension. Applying it to the finite disjoint union gives simultaneous L;
the node's subsequent normality, surjectivity, separatedness and generic-isomorphism
clauses are the canonical normalization consequences described in its proof.

Validation: the final module passes the server compile with no errors or warnings.
`deliver2.py --no-push` printed `OK (dry run)` for commit 8215a2f79ac: the
server preflight passes and every delivered file compiles. The sole theorem remains
intentionally `sorry`, as required by stage 2.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
