## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TangentDimensionSmoothness`
states `AlgebraicGeometry.GrpObj.tangent_dimension_smoothness`, with `sorry` as its
only theorem proof. It also constructs the canonical base-field module instance
`AlgebraicGeometry.GrpObj.identitySchemeTangentSpaceModule` on the already recorded
dual-number tangent space, using `Module.compHom`. This is scalar restriction along
the structural map `F → κ(e)`, written as the composite from the base ring to the
base stalk, then the identity stalk, then its residue field. The identity section
identifies this residue field with F; the action is precisely the F-action in the
node. The helper contains real data and no postponed proof, choice, or new notion
of tangent vectors. It is listed in `lean.declarations` with the main theorem.

The node's statement, dependencies, proof, and reviewed stage-1 split are preserved.
The previous ending concerned stage-1 delivery of an already reviewed split.
The stage-2 handoff in `coord/brief-stage2.md` section 0 applies: the current node
has no Lean record and occurs in the stage-2 queue. No repair note exists for it.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| F is a field | `(F : Type u) [Field F]` |
| F is algebraically closed | `[IsAlgClosed F]` |
| G is an F-scheme | `(G : Over (Spec (.of F)))` |
| G has its group-scheme multiplication, identity and inverse | `[GrpObj G]` |
| G is affine | `[IsAffine G.left]` |
| G is of finite type over F | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the exact recorded conjunction |
| e is the group identity | `GrpObj.onePoint G`, the image of the sole point of Spec F under the unit section |
| The tangent space at e | `schemeTangentSpace F G.left G.hom (onePoint G)`, the recorded dual-number construction |
| Its dimension over F is finite and nonnegative | `Module.Finite F (...)`; over a field this is finite dimensionality, and `Module.finrank F (...) : ℕ` is its dimension |
| The topological Krull dimension is a finite nonnegative integer | `∃ d : ℕ, topologicalKrullDim G.left = (d : WithBot ℕ∞)` |
| Dimension inequality | `topologicalKrullDim G.left ≤ (Module.finrank F (...) : WithBot ℕ∞)` |
| Equality holds if and only if G is smooth over F | The final `topologicalKrullDim ... = (...) ↔ Smooth G.hom` |
| The identity component may be smaller than G | No connectedness, irreducibility or identity-component binder |
| Reducedness is not assumed | No reducedness or smoothness hypothesis; `Smooth G.hom` occurs in the conclusion only |

Statement dependencies used, after reading their node records and declarations:

- `def-weil-field`: `Field`, from `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: the recorded match explicitly includes `IsAlgClosed`,
  from `Mathlib.FieldTheory.IsAlgClosed.Basic`. An algebraic closure of a separate
  field is not requested here.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, from
  `Mathlib.CategoryTheory.Monoidal.Grp`, specialized to schemes over Spec F as
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic` supplies `GrpObj.onePoint`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-sc-scheme-tangent-space`: `AlgebraicGeometry.schemeTangentSpace`,
  `schemeTangentSpaceAddCommGroup` and `schemeTangentSpaceModule`, from
  `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`. Their defining dual-number
  maps and canonical residue-field vector-space operations are reused verbatim.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`, from
  `Mathlib.Topology.KrullDimension`, including its negative-infinity and infinity cases.

The theorem uses Mathlib's `Module.Finite`, `Module.finrank` and `IsAffine`.
All universes and variables are explicitly bound. No new definition node or
dependency module is necessary: the scalar-restriction helper is part of the
identity tangent-space interface and its data are fully constructed.

Available proof dependencies are imported privately: identity local dimension
(`Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension`), rational tangent
cotangent duality (`Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality`),
regularity of smooth local rings (`Sheaf.RingTheory.SmoothOverFieldRegularLocal`),
and the Mathlib modules for closed rational points, finite duality, Noetherian
permanence, localization, regular-local dimension and Krull's height theorem.
Translation is supplied by the already public group-scheme Basic module; its
finite-type and smoothness imports also supply the Jacobson, affine smoothness,
restriction and source-local smoothness interfaces. The dependency
`lem-sfb-regular-separable-affine-smooth-neighbourhood` currently has no Lean record
or match locally, so it has no proof import; it is explicitly retained in the
proof docstring and the unchanged DAG. It is not needed to state this theorem.

Source reading: Milne's local PDF, printed pp.13-14 and 17-18, including Proposition
1.28 and Proposition 1.37 and the preceding dimension paragraph. The reviewed proof
uses local dimension at the group identity, so it does not apply the global
dimension inequality to an arbitrary point of an arbitrary non-equidimensional
scheme. The full five-step accepted proof is carried into the theorem docstring.

Edge cases checked before writing:

- The trivial group Spec F has both dimensions zero and is smooth.
- Any finite constant group over F, including a disconnected one and one whose
  order is divisible by the characteristic, has both dimensions zero and is smooth.
- The additive and multiplicative groups have both dimensions one and are smooth.
- In characteristic p, alpha_p and mu_p have dimension zero and tangent dimension
  one: the inequality is strict and the smoothness equivalence is false on both sides.
- Products of these examples with a finite constant group retain all components
  and nonreduced structure. No connectedness or characteristic-zero restriction enters.
- An empty scheme cannot carry this group identity section. Nevertheless the
  dimension expression retains Mathlib's full `WithBot ℕ∞` codomain, and finiteness
  and nonnegativity are asserted as conclusions, never presumed by a dimension cast.
- `Module.finrank` alone would return zero for an infinite-dimensional space; the
  separate `Module.Finite` conjunct explicitly rules that out.

Searches actually run:

- `msearch.py ... leanfinder`, query: "An affine finite type group scheme over an
  algebraically closed field has finite Krull dimension at most its tangent space
  dimension, with equality if and only if smooth". Eight hits: standard-smooth
  relative-dimension predicates and charts, their rank-of-differentials statements,
  and scheme smooth-relative-dimension predicates. No full group criterion.
- `msearch.py ... leansearch`, query: "For a finite type algebraic group dimension
  is at most identity tangent dimension and equality is equivalent to smoothness".
  Eight hits: smooth loci, standard-smooth relative dimensions, manifold Lie groups,
  and finite-presentation of Kaehler differentials. No full group criterion.
- `msearch.py ... loogle`, query: `"tangent", "smooth"`. Ten hits on formal smoothness
  and cotangent complexes, including `Algebra.FormallySmooth.subsingleton_h1Cotangent`
  and the smooth Jacobian criterion. No group dimension criterion.
- `msearch.py ... grep` in Mathlib/AlgebraicGeometry, query:
  `finrank.*[Tt]angent|[Tt]angent.*finrank|[Ss]mooth.*[Tt]angent|[Tt]angent.*[Ss]mooth`.
  Only the import of `StandardSmoothCotangent` in Etale.lean matched.
- `rg` in the live `lean/WeilConjectures` and `lean/Sheaf` trees for the node id:
  no declaration. Concept searches for group/tangent/dimension/smoothness found
  `GrpObj.finrank_lie_eq_localKrullDim_of_smooth` in GroupScheme/LieLocalDimension;
  it assumes smoothness and gives neither the nonsmooth inequality nor the converse.
  It is not an exact existing statement. The group-scheme Lie and tangent modules
  provide related constructions, which were inspected without substituting a second
  tangent-space definition.
- Name searches for `tangent_dimension_smoothness` and
  `identitySchemeTangentSpaceModule` across Mathlib, upstream, Sheaf, and
  `dag/lean_names_upstream.json` gave no collision.

Validation: the prescribed `scompile.py Q67 lem-sfb-group-tangent-dimension-smoothness`
compiled the module on the server both as a sandbox and under its library module
name (1.7 s and 1.6 s), with no errors or warnings. The node JSON changes only
`lean`, with its statement copied verbatim from the theorem signature. The date
uses UTC as requested.

No statement dispute, source correction, new node, or dependency repair.

## Second reading by Q67

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
