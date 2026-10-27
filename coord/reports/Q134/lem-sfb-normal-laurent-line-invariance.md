## Worker report

Stated `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorPullback_identity_relativeSplitTorus`
in `Sheaf.AlgebraicGeometry.NormalLaurentLineInvariance`. Its only theorem proof is `sorry`.
There are no new definitions, dependency replacements, or statement corrections.
The docstring carries all seven accepted proof steps, including the locally Noetherian
component reduction, the Laurent localization and fibre calculations, application of the
generic-line theorem, the section argument, and disjoint-open gluing.

Clause-by-clause correspondence:

- A scheme X: `(X : Scheme.{u})`.
- Locally Noetherian: `[IsLocallyNoetherian X]`; there is no global Noetherian or
  quasi-compact assumption.
- Every local ring is an integrally closed domain: `hX : ∀ x : X,
  IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
  Both domain and integral-closure conditions are retained, using the normal-ring
  node's recorded inline normal-domain form.
- A nonnegative integer r: `(r : ℕ)`, with zero allowed.
- D is the ring of finite Laurent sums with unique coefficients and convolution
  multiplication: this is the existing `AddMonoidAlgebra A (Fin r → ℤ)` inside
  `relativeSplitTorus X r`. Its elements have finite support on the integer exponent
  vectors, and basis monomials multiply by addition of exponent vectors.
- The scheme Y, its coefficient projection q, and evaluation-at-one section e use
  the already landed `AlgebraicGeometry.relativeSplitTorus`. Explicitly Y is
  `(relativeSplitTorus X r).X.left`, q is `(relativeSplitTorus X r).X.hom`, and e is
  `(η[(relativeSplitTorus X r).X]).left`. The identity section is part of the existing
  group-scheme data; it is not an arbitrary section or an extra hypothesis.
- To compare the node's presentation with the existing construction, put
  A = Gamma(X, O_X). The latter is X times Spec(A[Z^r]) over Spec A. The canonical
  coefficient isomorphism A tensor_Z Z[Z^r] ≅ A[Z^r] sends a tensor sum(c_m z^m)
  to sum(a c_m z^m), with inverse sum(a_m z^m) mapped to sum(a_m tensor z^m).
  Thus the two fibre-product presentations represent the same scheme over X.
  On an affine open Spec R the ring is R[Z^r]. The projection is induced by the
  coefficient inclusion, and the Hopf counit sends a_m z^m to a_m, exactly z_i ↦ 1.
  This also verifies agreement of e, not just of the underlying scheme. No new
  Laurent-space or split-torus definition is needed.
- Every invertible O_Y-module N: `(N : ...Modules) [N.IsInvertible]`.
- The required O_Y-linear isomorphism q^* e^* N ≅ N is
  `Nonempty ((tensorPullback ...hom).obj
  ((tensorPullback (η[...]).left).obj N) ≅ N)`.
  `Nonempty` asserts existence of an isomorphism, without choosing or claiming a
  canonical trivialization. The two functors are the recorded tensor inverse
  image, not an arbitrary functor or a module of the wrong ringed space.
- Empty and disconnected X, and r = 0: no binders exclude them. No group action,
  relative action, ampleness, separatedness, finite type, or field hypothesis occurs.
  The group law is used only to read the existing canonical identity section.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its scheme morphisms.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (the every-affine-open condition).
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  together with `IsDomain` applied to the scheme's actual local rings.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`, as used by the existing torus construction.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and its projections, underlying that construction.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, whose signature and local-unit
  docstring were read. Its rank-one Zariski triviality gives the stated notion.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, which publicly imports
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; the conclusion uses
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`. Its data are actual inverse
  image followed by extension of scalars and sheafification. The normalized
  composition/identity comparisons remain available for the proof.
- Added the already landed `def-sfb-relative-split-torus` to `stmt_deps`:
  `Sheaf.AlgebraicGeometry.RelativeSplitTorus`,
  `AlgebraicGeometry.relativeSplitTorus`. Its full definition and node were read.
  It supplies precisely the needed scheme, projection and section. This is the
  permitted reuse of an existing landed definition, not a new node or correction.

All recorded proof-dependency modules are imported, with proof-only modules using
plain `import`, including `RegularNormalDecomposition`, `AffineSpaceOpenInvertibleTrivial`,
and the relevant Mathlib geometry and polynomial-UFD files. The proof-only node
`lem-sfb-normal-noetherian-generic-line-pullback` has no recorded Lean declaration or
Mathlib match in the inspected DAG, so there is no module to import for it; the
accepted proof still explicitly names it. This missing future proof input does not
enter the signature. No import was omitted for a cycle.

Edge cases checked before writing:

- X empty: the local-ring hypothesis is vacuous, the canonical torus is empty,
  and the stated isomorphism agrees with the sheaf axiom for the empty cover.
- X disconnected, including infinitely many components and non-quasi-compact X:
  neither the group-scheme construction nor the signature imposes a finiteness or
  connectedness condition. The proof uses the open component cover componentwise.
- r = 0: the exponent group Fin 0 → ℤ is the trivial group, its group algebra is
  A, and projection and identity section identify with the identity of X. The
  conclusion is the identity/composition law for tensor pullback.
- Characteristic: the construction is integral and works in every residue
  characteristic, with no field or algebraic-closure assumption.
- Size: all schemes and their module categories use the explicit universe u;
  the fixed finite rank introduces no auxiliary test universe or size restriction.

Searches for an existing theorem (via the prescribed msearch.py wrapper):

- LeanFinder, `Every invertible sheaf on a split torus over a normal locally
  Noetherian scheme is pulled back from the identity section`: eight hits,
  principally ring Picard-group facts, `AffineSpace.homOverEquiv`, and
  `Scheme.Modules.pullbackId`; none states this theorem for schemes.
- Loogle, `"Pic", "Laurent"`: zero hits.
- Mathlib grep, `Pic.*Laurent|Laurent.*Pic|normal.*laurent|laurent.*normal`:
  one comment in `Algebra/Polynomial/Laurent.lean`, concerning the simp normal
  form of a Laurent monomial, not line-bundle invariance.
- LeanSearch, `Invertible sheaves on the product of a normal locally Noetherian
  scheme with a split torus come from the base`: eight hits, including
  `Scheme.Modules.inv_app`, algebraic module-invertibility results, and affine
  pullback facts; none states the required assertion.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for Laurent/normal,
  torus/Picard and `relativeSplitTorus`: found the reusable relative split-torus
  definition, but no theorem with the present statement. The field-only torsor
  and invariant-affine-neighbourhood statements have different hypotheses and
  conclusions. Searching the exact item id in `lean/WeilConjectures` found no hit.

The source text of Stacks Tags 0BD7 and 0BDA was read in `divisors.tex`:
0BD7 requires the normal integral base and generic-fibre triviality used in the
proof; 0BDA gives triviality on opens of affine space over any field. The item is
an explicitly formulated consequence of those tags, as its source field says.
No statement fault or STATEMENT-DISPUTED issue was found.

Validation: the server compile through scompile.py passed for the delivered module
in both sandbox and library modes, with no errors or warnings.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
