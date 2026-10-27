## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidSubsetSaturationInvariant` states
`AlgebraicGeometry.IsGroupoidScheme.subset_saturation_invariant`. Its only theorem has
proof `sorry`, as required for stage 2. The node is unchanged except for `lean`.
There are no new nodes, dependency repairs, disputed statements, or statement corrections.

Source read: `literature/stacks-project/groupoids.tex`, lines 3570–3627,
Tag 03BC (`definition-invariant-open`), the immediately following equivalence of subset
invariance with equality of source and target inverse images, and Tag 03LO
(`lemma-constructing-invariant-opens`), part (1) and its proof. Part (1) applies to
arbitrary subsets without the extra hypotheses of parts (2) and (3).

Hypotheses and conclusion, clause by clause:

- The schemes U and R are `{U R : Scheme.{u}}`, with unrestricted explicit universe `u`.
- The source, target, identity, inverse and composition are `(s t : R ⟶ U)`,
  `(e : U ⟶ R)`, `(i : R ⟶ R)` and `(c : pullback s t ⟶ R)`.
- The entire groupoid hypothesis is `_hG : IsGroupoidScheme s t e i c` from the
  recorded dependency. Its composition convention is c(a,b) = a composed with b,
  with source from the second projection and target from the first projection.
- Every subset A of the underlying point set is allowed by `(A : Set U)`.
- The defined expression σ(A) = t(s⁻¹(A)) is rendered directly as
  `t '' (s ⁻¹' A)`, using the standard Set image and preimage and the coercions of
  scheme morphisms to their underlying point functions. No separate saturation
  definition or local abbreviation is introduced.
- Invariance is exactly the equality of subsets of R,
  `s ⁻¹' (t '' (s ⁻¹' A)) = t ⁻¹' (t '' (s ⁻¹' A))`.
- The absence of openness, finiteness, flatness and separation assumptions is
  reflected in the absence of any such binder or instance.

Dependency declarations read and used:

- `def-a1-groupoid-scheme`: `Sheaf.AlgebraicGeometry.GroupoidScheme`,
  `AlgebraicGeometry.IsGroupoidScheme`. Read the full structure and docstring,
  including the source, target, composition and inverse identities. It is imported
  publicly because it occurs in the statement.
- Proof dependency `lem-weil-pbc-base-change-image`: its Mathlib match is
  `AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback` in
  `Mathlib.AlgebraicGeometry.PullbackCarrier` (lines 420–430). Its full signature
  gives the image identity for any `IsPullback` square and any subset, without
  flatness assumptions. This module is imported only for the proof plan.

The theorem docstring contains all three DAG proof steps. The singleton specialization
of the pullback image theorem lifts a compatible pair of scheme points; composition
proves the forward inclusion, and inversion proves the reverse inclusion. In particular,
no identification of the underlying space of a scheme fibre product with a topological
fibre product is assumed.

Edge cases checked mathematically before writing: A empty gives empty images and
preimages; A all of U has saturation all of U by the identity section e, giving all of R
on both sides. For an empty U the arrow scheme is empty since it maps to U, and the
statement still applies. The trivial groupoid s = t = e = i = identity reduces to equal
preimages. Nonclosed points and inseparable residue fields are included: the proof uses
the scheme pullback image identity, not rational-point composition. No nonemptiness,
finite type, characteristic or base-field restriction occurs. The absolute groupoid
notion is the one the node explicitly specifies; the source's groupoid over a base
forgets to these data.

Searches actually run:

- `msearch.py`, LeanFinder: “For every subset A of the points of a scheme groupoid
  its saturation t(s inverse A) is invariant under source and target”. Eight hits
  about manifold structure groupoids and ordinary subgroupoids; no matching theorem.
- `msearch.py`, Loogle: `"Groupoid", "Scheme"`. Zero hits.
- `msearch.py`, grep: `groupoid.*(orbit|invariant)|saturat.*groupoid`.
  Seventeen hits, concerning manifold structure groupoids; no matching theorem.
- `msearch.py`, LeanSearch: “For a groupoid scheme the target image of the source
  preimage of any subset is invariant”. Eight hits, including the already cited
  `Scheme.image_preimage_eq_of_isPullback`, elementary open-image facts and ordinary
  subgroupoid facts; none states this scheme-groupoid saturation invariance.
- `rg` in both project roots for `GroupoidScheme|IsGroupoidScheme|groupoid.*[Ss]atur|saturation.*invariant`
  found the groupoid interface and several specialized applications.
  `WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated` was opened and read:
  `descent_orbit_saturated` concerns singleton orbits of a cartesian groupoid arising
  from a descent datum, with additional descent-specific objects and compatibility
  hypotheses, so it does not state the present arbitrary-groupoid theorem.
  `Sheaf.AlgebraicGeometry.DescentSaturationInvariantOpen` was also read; it constructs
  restricted descent data under affine, flat and finite-presentation assumptions,
  rather than stating the arbitrary subset equality here.
- `rg` for `subset_saturation_invariant` and `groupoid_subset_saturation_invariant`
  in Mathlib, both project roots and `dag/lean_names_upstream.json` found no collision.
- The prescribed node-id search in `lean/WeilConjectures` returned no hits.

Validation: the delivered module was compiled with the prescribed `scompile.py` on
the server, both as a sandbox file and under its library module name; both passed
with no compiler errors or unexpected warnings. The required delivery dry run and
push are performed after this report is written.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
