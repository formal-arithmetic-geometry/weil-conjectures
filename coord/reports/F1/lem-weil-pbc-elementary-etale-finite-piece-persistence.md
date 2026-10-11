## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePiecePersistence` states
`AlgebraicGeometry.finitePiece_persistence_of_isIso_residueFieldMap`, with its sole proof
`sorry`. No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes and the morphisms f and φ: `{X S U U' : Scheme.{u}}`, `(f : X ⟶ S)`,
  `(φ : U ⟶ S)`. Every universe is explicit. The unnamed s is φ u₀; `(hx : f x = φ u₀)`
  states exactly the node's equality of images.
- The first fibre product is `pullback f φ`; its projections p and q are
  `pullback.fst f φ` and `pullback.snd f φ`. The open subscheme is
  `(V : (pullback f φ).Opens)`, with inclusion `V.ι` and scheme `V.toScheme`.
- (i) is `hfinite : IsFinite (V.ι ≫ pullback.snd f φ)`.
- (ii) is the point `v : V.toScheme`, its image equality `hv`, and `hunique`, which
  quantifies over every point of V over u₀, without further conditions on that point.
- (iii) is `hvx` and `hresidue`, the latter requiring the *induced* residue-field map
  of `V.ι ≫ pullback.fst f φ` to be an isomorphism, rather than an abstract isomorphism.
  Its domain is κ(p(v)); `hvx` identifies this point with x. This is the map on V's
  own residue field, so no ambient-point replacement or extra field identification is needed.
- The further base change is `(ψ : U' ⟶ U)`, `(u₁ : U')`, with `hu : ψ u₁ = u₀`
  and `hbase : IsIso (ψ.residueFieldMap u₁)`. Its domain is κ(ψ u₁), identified with
  κ(u₀) by hu. No étaleness assumption is added.
- The second fibre product is `pullback f (ψ ≫ φ)` with its two standard projections.
  The specified π is a morphism between these pullbacks; `hπp` and `hπq` are precisely
  the two equations defining it in the node. The pullback universal property makes this
  morphism unique, so these equations impose no additional mathematical restriction.
- `let V' := π ⁻¹ᵁ V` is the inverse-image open subscheme specified in the node.
- (i') is the conclusion's `IsFinite (V'.ι ≫ pullback.snd f (ψ ≫ φ))`.
- (ii') is `∃ v' : V'.toScheme` with its image equality and the universal uniqueness
  clause for *every* w above u₁. Uniqueness is not restricted to points satisfying (iii').
- (iii') is the equality of the image of v' with x and `IsIso` of the actual residue-field
  map of `V'.ι ≫ pullback.fst f (ψ ≫ φ)` at v'.
- The moreover clause is `π (V'.ι v') = V.ι v`, comparing both points in the first pullback.

Dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; read their structure signatures and docstrings.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`, and `pullback.map`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; read signatures/docstrings.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies `HasPullbacks Scheme`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; read its affine-local definition.
  Also read `IsIntegralHom` in Morphisms.Integral; integrality is not used in this item.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, `Mathlib.AlgebraicGeometry.ResidueField`; read their
  definitions and docstrings. `IsIso` means an isomorphism in CommRingCat, hence the
  isomorphism of fields induced by the morphism that the node requires.
- The open-subscheme API `Scheme.Opens.toScheme` and `Scheme.Opens.ι` was read in
  `Mathlib.AlgebraicGeometry.Restrict`; these notions are included in def-pc-scheme.
  The two imports supply the APIs used here; no private copies of notions are introduced.

Source: the repository has no local `literature/stacks-project/more-morphisms.tex`, so I
opened https://stacks.math.columbia.edu/tag/02LK. Its final assertion is the persistence
of (i)-(iii) under an elementary étale neighbourhood. The node explicitly generalizes this
to arbitrary ψ preserving the residue field, and its four-step proof justifies that
formulation without étaleness. No fault or disputed statement was found.

Edge cases checked: empty schemes or an empty V cannot satisfy the displayed point binders;
no extra nonemptiness assumption is imposed. U' may have arbitrary other fibres. Identity
ψ and V equal to the whole first pullback are included. There are no characteristic,
Noetherian, separatedness, finite-type, or étaleness restrictions. One arbitrary explicit
universe u covers schemes in any universe (smaller schemes may be lifted).

Searches (msearch.py, group F1, this item):

- LeanFinder query: "finite open subscheme with unique fibre point and residue field
  isomorphism persists under base change with identical residue field". Eight results:
  residueFieldCongr compatibilities, SpecToEquivOfField, Pullback residueFieldCongr
  compatibility, and Ideal.fiberIsoOfBijectiveResidueField. These are tools for the proof,
  not the statement about the finite open subscheme and all conclusion clauses.
- Loogle query: "AlgebraicGeometry.Scheme.Hom.residueFieldMap, IsFinite".
  Zero hits; unknown identifier IsFinite.
- LeanSearch query: "finite open subscheme unique point fibre base change residue field
  isomorphism". Service unavailable: Internal Server Error; no verdict inferred.
- Mathlib grep query: `residueField.*(IsIso|Bijective)|finite.*baseChange`,
  subdirectory AlgebraicGeometry. Seven hits concern stability of finite, quasi-finite,
  finite-type or finite-presentation ring properties under base change, not this statement.
- Direct rg of Mathlib AlgebraicGeometry for
  `residueField.*Bijective|Bijective.*residueField|elementary`: no hits.
- Direct rg of WeilConjectures and lean/Sheaf for
  `finite.*piece|piece.*persist|elementary.*etale|02LK`: hits concern other finite-piece
  constructions and étale API, no matching persistence statement. Direct node-id search
  in WeilConjectures: no hits.
- Direct name search in dag/lean_names_upstream.json, Mathlib, WeilConjectures, and
  lean/Sheaf for `FinitePiecePersistence|finitePiece_persistence_of_isIso_residueFieldMap`:
  no hits; the chosen declaration name is fresh.

Server compile via scompile.py succeeded with exit code 0 in 1.6 seconds and no warnings.
The final step is the delivery dry run; the independent second reader supplies their own
reading and performs the actual delivery.


## Second reading by F1

Independent object/hypothesis/conclusion checklist, read against the node and the actual
Mathlib declarations (H3). All entries pass:

1. Objects X, S, U, U' are arbitrary schemes: `{X S U U' : Scheme.{u}}`;
   maps f and φ are `(f : X ⟶ S) (φ : U ⟶ S)`. Mathlib `Scheme` is a locally
   ringed space locally isomorphic to an affine spectrum, and `Scheme.Hom` is a
   morphism of locally ringed spaces, exactly def-pc-scheme.
2. Points u and x, with s = φ(u) and f(x) = s: `(u₀ : U) (x : X)` and
   `(hx : f x = φ u₀)`. Eliminating the defined name s adds no hypothesis.
3. X_U and its projections p, q: `pullback f φ`, `pullback.fst f φ`,
   `pullback.snd f φ`. Read HasPullback.lean's signatures for `pullback`, its
   projections and lift; they implement def-pc-fibre-product. Pullbacks.lean supplies
   `HasPullbacks Scheme` unconditionally, with no affineness or finiteness assumption.
4. Open subscheme V: `(V : (pullback f φ).Opens)`, scheme `V.toScheme` and
   inclusion `V.ι`. Read Restrict.lean: these are the restriction to the open and
   its open immersion. This uses def-pc-scheme's open subscheme, not a private notion.
5. Hypothesis (i): `hfinite : IsFinite (V.ι ≫ pullback.snd f φ)`.
   Read Finite.lean: IsFinite extends IsAffineHom and requires finite ring maps
   on every affine open. This is def-weil-finite-integral-morphism's finite clause.
6. Hypothesis (ii), existence and unrestricted uniqueness: `(v : V.toScheme)`,
   `hv : (V.ι ≫ pullback.snd f φ) v = u₀`, and
   `hunique : ∀ w : V.toScheme, (V.ι ≫ pullback.snd f φ) w = u₀ → w = v`.
   Giving the unique witness as an input is equivalent to assuming unique existence.
7. Hypothesis (iii): `hvx : (V.ι ≫ pullback.fst f φ) v = x` and
   `hresidue : IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v)`.
   Read ResidueField.lean: κ is the residue field of the stalk and residueFieldMap
   is induced by the local stalk map, with direction κ(image) → κ(source).
   hvx identifies its domain with κ(x); IsIso is of this induced ring map,
   not merely existence of some field isomorphism. The open subscheme has the
   canonical ambient residue field, since its inclusion is an open immersion.
8. Further base change and marked point: `(ψ : U' ⟶ U) (u₁ : U')`,
   `hu : ψ u₁ = u₀`, `hbase : IsIso (ψ.residueFieldMap u₁)`.
   No étaleness, local finite type, or field-base assumption is inserted.
9. X_U' is `pullback f (ψ ≫ φ)` with the standard fst and snd projections.
   π is the displayed morphism between the two pullbacks. `hπp` and `hπq`
   are exactly p ∘ π = p' and q ∘ π = ψ ∘ q'. The universal property
   guarantees existence and uniqueness of such π, so these binders do not restrict
   the node's data beyond specifying its canonical map.
10. V' is exactly the inverse-image open: `let V' := π ⁻¹ᵁ V`.
11. Conclusion (i'): `IsFinite (V'.ι ≫ pullback.snd f (ψ ≫ φ))`.
12. Conclusion (ii'): `∃ v' : V'.toScheme` with its displayed image equality to u₁
    and `∀ w : V'.toScheme, ... w = u₁ → w = v'`. This is unique existence
    in the entire fibre, not only among points satisfying the residue-field clause.
13. Conclusion (iii'): the same v' maps to x under `V'.ι ≫ pullback.fst f (ψ ≫ φ)`;
    `IsIso` applies to that actual morphism's residueFieldMap at v'.
14. Moreover: `π (V'.ι v') = V.ι v`. Both sides are points in X_U;
    the inclusions faithfully render the node's π(v') = v.

Source reading: local Stacks .tex is absent. Independently fetched and read
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
from section-etale-localization through lemma-etale-makes-quasi-finite-finite-at-point,
and checked https://stacks.math.columbia.edu/tag/02LK. The section introduces the
basic diagram with an étale neighbourhood. The lemma's locally finite type and
isolated-fibre-point assumptions are for constructing the original triple; its
final assertion preserves (i)-(iii). The node expressly states an agent generalization
to arbitrary ψ with an isomorphism on the indicated residue fields. Its four-step
proof justifies this: the inverse-image open is V ×_U U', finite by base change;
the fibre has points Spec(κ(v) ⊗_{κ(u)} κ(u')), a singleton because the second
field map is an isomorphism; the canonical first-factor map and hence κ(x) → κ(v')
are isomorphisms. No source hypothesis needed for this persistence argument is missing.

Edge cases: empty X, S, U, U', or V are allowed as schemes; the point binders rule out
exactly the cases ruled out by the node's point hypotheses. No independent nonempty
instance is assumed. V = top and ψ = identity are included. Nilpotents and zero rings
are not excluded; a zero-ring empty spectrum cannot supply a point. No index set,
integer n or characteristic binder occurs, so empty index sets and n = 0 introduce
no extra restriction. There is no characteristic, Noetherian, separatedness or étaleness
restriction. Universe u is arbitrary and explicitly bound, as in the schemes category
of the dependency nodes; every finite diagram can be placed in a common universe.

Independent H4 searches, using different concept terms:

- msearch LeanFinder: "unique fiber point residue extension isomorphism inverse image
  finite open base change". Eight hits, including Scheme.Hom.fiberHomeo,
  fiberToSpecResidueField, Pullback residueFieldCongr compatibility, and
  Ideal.fiberIsoOfBijectiveResidueField; none states all persistence clauses.
- msearch Loogle: "AlgebraicGeometry.Scheme.Hom.residueFieldMap". Twelve hits:
  the map itself, its id/comp/congr equations, and the open-immersion IsIso instance;
  none is this persistence theorem.
- msearch LeanSearch: "finite morphism unique fibre point persists residue field
  preserving base change". Internal Server Error; recorded unavailable, no verdict.
- Direct rg of Mathlib AlgebraicGeometry, source WeilConjectures/Mathlib/AlgebraicGeometry,
  and project lean/Sheaf/AlgebraicGeometry for
  `persist|elementary.*neigh|unique.*point|one.*point`: only unrelated uniqueness,
  quasi-finiteness and finite-piece construction statements; no exact match.
  Broader residueFieldMap searches in all WeilConjectures and lean/Sheaf found
  tangent criteria, invariance and field arithmetic, not this persistence statement.
- Exact declaration/module-name rg across Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no collision. No replacement by an existing declaration.

H5-H9: no definitions are introduced, hence no hollow data. Exactly one theorem has
proof `by sorry`; nothing is proved. Module and theorem docstrings give Stacks 02LK
and the exact blueprint id; the theorem docstring carries all four node proof steps
and their dependencies. Finite and ResidueField imports supply the two main APIs;
namespace and 100-character lines follow the example. No new nodes, dependency
modules, or statement correction are present or needed. Every variable and universe
is explicitly bound. No semantic or convention mismatch found; Lean and node record
are unchanged. This second reading adds only this independent report.

Second-reader server compilation: scompile.py on the absolute sandbox module path
passed with exit code 0 in 1.6 seconds, no errors or warnings.
