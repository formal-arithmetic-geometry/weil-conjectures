## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralDescentFinitePointOrbits` states
`AlgebraicGeometry.integral_descent_finite_point_orbit`, with its sole proof `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes. The complete five-step DAG proof is carried
in the theorem docstring, including the distinction between image finiteness and
finiteness of a scheme-theoretic fibre.

Sources read: the assigned DAG statement and all seven statement-dependency
records; the recorded declarations and their docstrings in the live read clone;
Raynaud, *Un critère d'effectivité de descente*, Theorem 4.1(ii), printed p.16,
and its proof pp.17–21, at
https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf;
and the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3). Raynaud gives the orbit-in-an-affine-open effectivity criterion; the
assigned node is explicitly an agent-formulated finite-orbit prerequisite, rather
than a quotation of that theorem or an application of effectivity. The Lean proof
is postponed, and does not assume the orbit lies in an affine open.

Every hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Schemes T and S, morphism q:T → S | `{T S : Scheme.{u}} (q : T ⟶ S)` |
| q integral | `[IsIntegralHom q]` |
| q surjective | `[Surjective q]` |
| q flat | `[Flat q]` |
| q quasi-compact | `[QuasiCompact q]` |
| Each underlying point fibre of q is finite | `(hq : ∀ s : S, (q ⁻¹' {s}).Finite)` |
| Scheme V → T | `(V : Over T)`, with underlying scheme `V.left` and morphism `V.hom` |
| V → T locally of finite presentation | `[LocallyOfFinitePresentation V.hom]` |
| V locally Noetherian | `[IsLocallyNoetherian V.left]` |
| A descent datum on V over T/S | `(D : Over.DescentDatum q V)` |
| T₂ = T ×_S T | `pullback q q` |
| a₀, a₁ | `pullback.fst q q`, `pullback.snd q q` |
| R = V ×_{T,a₀} T₂ | `pullback V.hom (pullback.fst q q)` |
| r₀:R → V is projection | `pullback.fst V.hom (pullback.fst q q)` |
| r₁ obtained from D then second projection | `(pullbackRightPullbackFstIso q q V.hom).hom ≫ D.toHom` |
| Every point v of V | `(v : V.left)` |
| O_v is r₁(r₀⁻¹(v)) | Image `''` of the inverse image `⁻¹' {v}` under these exact maps |
| O_v finite as subset of V | `.Finite` on that image, not on the inverse image or a scheme fibre |

Why the displayed r₁ is exactly the node's map: the recorded transport form of
`Over.DescentDatum` is the Yoneda form of the pullback isomorphism. Its `toHom`
transports the universal point on `V ×_S T` from the first T-coordinate to the
second. Mathlib's `pullbackRightPullbackFstIso q q V.hom` identifies the node's
literal R with `V ×_S T`. The lemmas
`pullbackRightPullbackFstIso_hom_fst` and
`pullbackRightPullbackFstIso_hom_snd`, read at
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Pasting.lean:470–480`, say that this
identification preserves r₀ and sends the second T-coordinate to a₁ after the R
projection. Naturality of the recorded transport therefore identifies the
composite with the V-projection after D. There is no arbitrary relation map or
extra compatibility hypothesis. The statement keeps R itself as the image's
domain; no replacement of the fibre by another set is made.

Dependency declarations used, with their source modules:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (structure and morphism signatures read).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  The canonical cancellation isomorphism is the already existing
  `CategoryTheory.Limits.pullbackRightPullbackFstIso`, from `.Pullback.Pasting`.
- `def-weil-pbc-fpqc-covering`: `Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`, read with its flat jointly-surjective
  quasi-compact-family docstring. Here the node explicitly specifies a single
  morphism, so its flat, surjective and quasi-compact clauses are expressed
  separately by the existing `Flat`, `Surjective`, `QuasiCompact` classes, not by
  a second covering predicate. Their source signatures were also read in
  `Morphisms.Flat`, `Morphisms.UnderlyingMap`, `Morphisms.QuasiCompact`.
- `def-pd-descent-datum`: `CategoryTheory.Over.DescentDatum` and its existing
  `CategoryTheory.Over.DescentDatum.toHom`,
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`. The full transport,
  naturality, identity and cocycle fields and the universal transport definition
  were read. No dependency-interface repair is needed.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-finite-integral-morphism`: its recorded integral declaration
  `AlgebraicGeometry.IsIntegralHom`, defined in `Mathlib.AlgebraicGeometry.Morphisms.Integral`
  and exposed by the recorded `Mathlib.AlgebraicGeometry.Morphisms.Finite` import.
  `IsFinite` is not imposed: its stronger finite-module condition is absent.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`.

All statement dependency modules are public imports. All currently stated proof
dependency modules are imported, including the residue-field algebraicity instance,
the field transcendence-degree tower theorem, fibre/residue-arrow comparisons,
finite-presentation and Noetherian permanence, affine quasi-compactness, and
`Sheaf.AlgebraicGeometry.FieldSpecializationTrdegDrop`.
`lem-sfb-quasicompact-antichain-image-finite` currently has neither a Lean record
nor a Mathlib match, so there is no recorded module to import for this proof-only
dependency. It does not supply any notion needed to type the statement.

Edge cases checked before writing:

- Empty V is admitted: the conclusion has a point binder and is vacuous.
- Empty S and T are admitted; there is no `Nonempty` restriction on any scheme.
- Identity q and the identity descent datum give singleton orbits, as required.
- Finite field covers are included, but algebraic extensions of infinite degree
  are also admitted. In particular the theorem does not infer `IsFinite q` from
  integrality plus finite underlying fibres, and places no cardinality bound on
  the points in the base-changed scheme-theoretic fibre.
- Nonclosed v is allowed; the singleton inverse image is an arbitrary subset,
  not a closed fibre or a rational/geometric point condition.
- V is not assumed quasi-compact, separated, or globally Noetherian; local finite
  presentation and local Noetherianity occur exactly as stated.
- All characteristics and every universe u are allowed. `set_option autoImplicit false`
  enforces explicit variable binding.

Searches actually run (raw service results are retained in `searches.jsonl`):

- LeanFinder: “For an integral surjective flat quasi-compact scheme morphism with
  finite point fibres, every point orbit of a locally finitely presented locally
  Noetherian scheme descent datum is finite”. Eight hits, headed by the finite
  scheme-fibre instance, `IsFinite` and flat-surjective descent of properties.
  None states orbit-image finiteness for a merely integral cover.
- LeanSearch: “Finite images of point orbits for scheme descent data over integral
  flat surjective morphisms with finite base fibres”. Eight hits about finite
  morphisms and morphism-property descent, with no exact orbit-image theorem.
- Loogle: `AlgebraicGeometry.IsIntegralHom, CategoryTheory.Over.DescentDatum`:
  the service reports that the project's descent datum is an unknown identifier;
  this query cannot search that project declaration. The follow-up
  `AlgebraicGeometry.IsIntegralHom, Finite` returns zero hits.
- Mathlib grep via msearch: `descent.*orbit|orbit.*descent|finite.*orbit` in
  `AlgebraicGeometry`, zero hits.
- Direct rg of the read clone's `WeilConjectures` and `Sheaf` for
  `finite.*orbit|orbit.*finite|integral.*descent`, plus direct grep for the item id
  in `WeilConjectures`: no existing statement of this node. Related files concern
  finite group actions, continuous discrete actions, or other coefficient descent.
  The descent relation was inspected in
  `FpqcInvariantIntersectionNeighbourhoods.lean`; its `descentRelationTarget`
  uses the same universal transport on `V ×_S T`, but states no orbit finiteness.
  The smaller recorded upstream module already supplies `D.toHom`.
- Direct rg for the proposed declaration names in `WeilConjectures`, `Sheaf`
  and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py Q88 lem-sfb-integral-descent-finite-point-orbits` compiled
the delivery file in both its private sandbox and library module contexts, with
exit code 0 and no errors or unexpected warnings. The signature in `lean.statement`
is copied verbatim from `theorem` to before `:=`; every source line is at most
100 characters. No mathematical node fault or disputed statement was found.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
