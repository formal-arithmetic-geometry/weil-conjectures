## Worker report

This stage-2 delivery states `AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal.exists_model`
in `Sheaf.AlgebraicGeometry.AffineCoordinateStrictLocalModel`. Its sole postponed proof is
`exists_model`; all helper definitions have real data. `Model` and `FibreModels` are dependent
conclusion packages. No arbitrary model, comparison map, or extra smoothness hypothesis is
assumed by the theorem. No node statement or accepted stage-1 proof was changed.

The inherited BLOCKED ending concerned Q114's stage-1 split, reviewed on 2026-10-23. The live
node has `status: split`, a stage-1 review and no `lean` or `reviewed_lean`. There is no repair
note for the item. `coord/brief-stage2.md` §0 explicitly distinguishes that situation from
an existing stage-2 delivery; the queue also assigns this item to stage 2. Thus this delivery
preserves Q114's accepted split and supplies its Lean statement.

Every hypothesis and clause is rendered as follows (all names below are in
`AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal`):

- Schemes S,V: `{S V : Scheme.{u}}`; finite rank r, including zero: `(r : ℕ)`;
  E = ULift (Fin r): `Index.{u} r`; the coordinate isomorphism: `e`. The source calls this
  an isomorphism over S with structure map f; `projection r e` is exactly the composite
  `e.hom` with the affine-space projection, so f is determined rather than a second datum.
- The algebraically closed field and geometric point are `{Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)`. Its base point is `v ≫ projection r e`.
  The universe u is arbitrary, and a common enlargement covers every input size.
- A is `Base r e v = strictHenselizationRing (v ≫ projection r e)`; B is
  `strictHenselizationRing v`. The two local-ring instance binders expose precisely the
  local structures of these specified geometric strict local rings, which already exist
  by `strictHenselizationLocalStructure`; they impose no restriction on schemes or points.
  There is no hypothesis on a model ring or on a choice of strict henselization.
- The canonical A-to-B map is `baseMap`: the ring map of the uniquely pointed
  `strictHenselizationMap`. `ringMap` uses `Spec.preimage` and equality transport only.
  It is not an unspecified map satisfying an assumed condition.
- `coordinate r e v i` is exactly `AffineSpace.coord S i`, pulled back along the structural
  morphism followed by e and converted from global sections of Spec B by `ΓSpecIso`.
  K is an arbitrary `Set (Index r)`; `hK` is exactly membership of all selected coordinates
  in the maximal ideal of B. `coordinateIdeal` is their `Ideal.span`.
- The scheme V_K is realized by the actual complementary affine space, with the explicit
  zero-insertion map `inclusion` into V. Thus its canonical S-isomorphism is the identity
  on this chosen representative. `Model.closed` states it is a closed immersion;
  `Model.zeroLocus` identifies its entire scheme structure by the coordinate-zero
  universal property on arbitrary test schemes, including nonreduced ones. This is not
  just a set of points. Zero insertion is over S by `AffineSpace.homOfVector_over` and
  the inverse coordinate isomorphism, so this identification is over the required base.
  `Model.smooth` is smoothness of its projection to S.
- `Model.point` and `point_eq` give the factorization of the original geometric point.
  `quotientIso` is the displayed strict-local-ring isomorphism to B/J_K.
  `quotientIso_map` says its composite with the actual functorial map B-to-Osh(V_K)
  is `Ideal.Quotient.mk J_K`. In particular the A-actions induced by the canonical maps
  agree: precompose this equation with `baseMap`. Functoriality identifies the composite
  A-to-B-to-Osh(V_K) with the canonical A-map over S. Thus this states the A-algebra
  qualification without choosing a second, potentially different algebra structure.
- `fibreIdeal` is `Ideal.map (baseMap ...) (IsLocalRing.maximalIdeal A)` = m_A B;
  `PolynomialRing` is precisely the bundled ring `MvPolynomial E (ResidueField A)`;
  `polynomialIdeal` is L = span of the selected polynomial variables.
- `Model.fibres` instantiates `FibreModels` with exactly A,B,P,K,m_A B,J_K,L, the canonical
  base map, coefficient map C composed with the residue quotient, t_i, X_i and both
  geometric evaluations. Its generic parameters are conclusion-package parameters;
  the theorem never quantifies over arbitrary such input in place of these objects.
- `kappaPoint` and `kappaPoint_eq` describe the embedding of kappa in Ω induced by the
  base geometric point. `polynomialPoint_coeff` and `polynomialPoint_coord` specify the
  lifted closed-fibre geometric point by polynomial evaluation on every coefficient
  and every variable. Surjectivity of A-to-kappa makes this the complete evaluation map.
  Its prime q is exactly `RingHom.ker polynomialPoint`, not a maximal prime assumption.
- `ideal_le` is L ≤ q. `quotientPoint_eq` is factorization through P/L;
  `prime_quotient` identifies its kernel with q/L (the image of q under the quotient).
  `prime0` and `prime1` supply primality as conclusions, not theorem hypotheses.
- `presentation0` and `presentation1` use the dependency's exact
  `Algebra.StrictHenselizationPresentationIn.{u,u}` on `Localization.AtPrime q` and
  `Localization.AtPrime q'`. These are universal pointed-etale colimit presentations,
  with their structural algebra data. Their residue separable closures are literally
  `separableClosure q.ResidueField Ω` and `separableClosure q'.ResidueField Ω`;
  `residue0_eq` and `residue1_eq` pin the residue embeddings to the polynomial points.
- `iso0` and `iso1` give the two displayed isomorphisms from B/m_A B and
  B/(m_A B + J_K). `local0` and `local1` expose the model local structures; a ring
  isomorphism between these local rings is necessarily local.
  `coefficient0`, `coordinate0`, `coefficient1`, `coordinate1` identify coefficients
  and all surviving variables with their localized polynomial classes.
  `evaluation0` and `evaluation1` preserve the chosen geometric evaluations in Ω.
- `comparison`, `comparison_local`, `comparison_polynomial`, `comparison_residue`
  and `comparison_unique` specify the unique local strict-henselization map covering
  P-to-P/L with the fixed residue embedding. `comparison_quotient` is the commuting
  square with the canonical quotient B/m_A B-to-B/(m_A B+J_K), using `Ideal.Quotient.factor`.
  Compatibility with the earlier quotient B-to-B/J_K follows by precomposing with the
  quotient from B: both paths are the same quotient B-to-B/(m_A B+J_K).

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.coord`,
  `AffineSpace.homOfVector`, its projection and coordinate formulas.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (and the recorded relative
  dimension interface); `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` (the geometric
  point is the recorded inline Spec Ω morphism).
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`: `strictHenselizationRing`,
  `strictHenselizationScheme`, `strictHenselization_properties`;
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `strictHenselizationStructuralMap` and its limit-leg characterization.
- The recorded `Sheaf.Paper.StrictHenselizationFunctoriality.strictHenselizationFunctoriality`
  supplies the canonical map through the already published wrapper
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`:
  `Scheme.strictHenselizationMap` and its existence/uniqueness characterization.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn` and `.residueMap`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal property; the relative affine space uses this construction.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with `X`, `C` and evaluation;
  `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and the
  residue-field interface.
- The added landed statement dependency `def-weil-pbc-strict-henselization-point-evaluation`
  is used through `Sheaf.Paper.StrictHenselizationPointEvaluation`:
  `Scheme.strictHenselizationPointEvaluation`. The upstream same-name evaluation uses
  a different colimit vertex, so importing both is incorrect. We import the side required
  by the recorded functoriality interface, not a new evaluation definition.

All already stated proof dependencies are imported: closed-immersion cartesian
comparison, affine strict-local ring comparison, affine-space smoothness and Mathlib
scheme morphism gluing. `lem-trf-smooth-strict-local-closed-fibre-model` has no Lean record
or Mathlib match yet, so there is no module to import for that proof dependency. It is
not needed to type the statement and is not silently assumed. Its role remains in the
unchanged proof plan and the theorem docstring.

Edge cases checked: r=0 and K empty (no variables; identity quotient), K=empty at arbitrary
rank (J=L=0), K=E (complement has dimension zero; P/L=kappa), nonclosed polynomial primes
(q is never assumed maximal), nonreduced/non-Noetherian S, and empty S (no geometric-point
input exists). The t_i-in-m_B assumption is essential for factorization; it is retained.
No degree, characteristic, residue-algebraicity of the whole Ω, or Noetherian condition
has been added. No statement dispute or source correction was found.

Searches made: `msearch.py` LeanFinder query "Affine coordinate zero subspace strict
henselization quotient and closed fibre polynomial localization models" returned eight
henselian/root-criterion hits, no coordinate comparison. Loogle query `"AffineSpace",
"coord"` returned the six coordinate/reindex/base-change formulas used above, no
strict-local quotient theorem. LeanSearch query "Affine coordinate subspace strict
henselization quotient by coordinates" returned affine subspaces of modules and an
elliptic-curve coordinate-ring quotient, no matching scheme statement. Mathlib grep
`coordinate.*strict|strict.*coordinate|zero.*subspace` under AlgebraicGeometry had no hit.
Direct rg searches of both project roots for the exact node id had no hit; the broader
coordinate/strict-local search found the affine-infinity model and generic strict-local
comparisons, which do not state this result. DAG searches found existing general
comparison nodes, so none was redefined. No independent new mathematical notion is
introduced: the helper declarations are concrete pieces and conclusion packaging of
this owning node, listed in `lean.declarations` as authorized by the brief.

Read the actual source passages: Stacks algebra.tex 05WS, 04GU, 00T7 and
etale-cohomology.tex 04HX. The current blueprint sk-i-curve-zero and
lem-trf-local-term-locality describe the newer local-term route; Q114 already documented
this node's historical lower-level coordinate-tool ancestry. No blueprint unit is changed.

Validation: scompile.py checked the sandbox and named module cleanly, respectively
23.4 s and 28.6 s after factoring polynomial packaging over its explicit ring parameters.
The earlier full structure repeatedly unfolded scheme-colimit types and hit the 60-second
limit; the mathematical statement is unchanged by the packaging refactor. Only the named
stage-2 existence theorem has a sorry.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
