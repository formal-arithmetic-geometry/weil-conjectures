## Worker report

The module `Sheaf.AlgebraicGeometry.EventuallyProper` states
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit`, with its sole proof `sorry`.
It states the node unchanged, with no new notions, dependency modules, or node correction.
The declaration docstring carries the node's six-step natural-language proof and its
named inputs. Every universe and variable is explicitly bound.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Directed set I: `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
  A preorder allows the Stacks directed-set convention; no antisymmetry is imposed.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. Its functor laws are precisely
  compatibility of transition morphisms. For `hi : i₀ ≤ i`, the transition Sᵢ → S₀ is
  `D.map (homOfLE hi).op`.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]`.
- S is the limit: `(c : Cone D) (hc : IsLimit c)`; `S = c.pt`, and S → S₀ is
  `c.π.app (op i₀)`. This accepts any specified limit cone, rather than imposing
  an extra choice or extra property of its projections.
- Distinguished index 0: `(i₀ : I)`. It is an arbitrary index, not a minimum.
  This binder already excludes an empty directed set, exactly as the node's `0 ∈ I` does.
- S₀ quasi-compact and quasi-separated: `[CompactSpace (D.obj (op i₀))]`
  and `[QuasiSeparatedSpace (D.obj (op i₀))]`.
- X₀ and Y₀ schemes, both quasi-compact and quasi-separated:
  `{X₀ Y₀ : Scheme.{u}}`, with `CompactSpace` and `QuasiSeparatedSpace` for each.
- Their S₀-structures and the morphism over S₀: `(a : X₀ ⟶ D.obj (op i₀))`,
  `(b : Y₀ ⟶ D.obj (op i₀))`, `(f₀ : X₀ ⟶ Y₀)`, `(h : f₀ ≫ b = a)`.
  The equality h is the meaning of “morphism of schemes over S₀”, not an added condition.
- X and Y are the fibre products with S, and f is the base change:
  `pullback.map a (c.π.app (op i₀)) b (c.π.app (op i₀)) f₀ (𝟙 c.pt)
  (𝟙 (D.obj (op i₀))) ... ...`. Its domain is `pullback a (c.π.app (op i₀))`,
  and its codomain is `pullback b (c.π.app (op i₀))`.
  The two equality arguments are constructed from h and category identity laws.
- f proper: `(hf : IsProper (pullback.map ...))` for that precise induced map.
- f₀ locally finite type: `[LocallyOfFiniteType f₀]`. No finite-presentation hypothesis.
- Conclusion: `∃ (i : I) (hi : i₀ ≤ i), IsProper (pullback.map ... )`.
  The map here uses `D.map (homOfLE hi).op` in both fibre products, f₀ on the first
  factors, and the identity of Sᵢ on the second factors. Thus it is exactly fᵢ,
  and the witness is explicitly required to satisfy i ≥ 0.

Dependency declarations read and used:

- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`. Its class requires affine preimages
  of affine opens; used on every transition.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition`,
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`. The recorded theorem and its full
  docstring were read. This module is imported; the existing limit formalism `Cone D`
  and `IsLimit c` specifies the limit already supplied in the node. Its existence
  theorem need not be applied in a statement whose limit is given.
- `def-weil-pbc-scheme-conventions` is explicitly a convention record, with no own
  declaration. Quasi-compactness and quasi-separatedness of schemes use Mathlib's
  `CompactSpace` and `QuasiSeparatedSpace`, not morphism properties of identity maps.
  The quasi-separated class and its scheme-level equivalence in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` were read.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.map`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. Their full signatures
  and docstrings were read. No private fibre-product or base-change definition.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; also read `IsSeparated` and
  `UniversallyClosed` in their recorded Mathlib source files. Universally closed
  implies quasi-compact, so this class agrees with separated, finite type and
  universally closed as in the node.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its class and docstring were read,
  as were `QuasiCompact` and its docstring in the companion module. Here only the
  locally finite type clause is needed.

Sources were opened at https://stacks.math.columbia.edu/tag/081F and
https://stacks.math.columbia.edu/tag/081D (the local literature checkout is absent).
081D supplies exactly the qcqs assumptions; 081F supplies the properness hypothesis,
local finite type hypothesis, and proper finite-stage conclusion. No node fault found.

Edge cases checked before writing: empty schemes are allowed (no nonempty scheme
binder); an empty I is excluded only by the required distinguished index; a singleton
I permits i = i₀ and hi reflexive; i₀ need not be minimal; nonseparated f₀ is allowed,
since separation is obtained only in the proof; no Noetherian, finite-presentation,
base field, characteristic, or nonzero-ring assumption. Separate universes v for I
and u for schemes do not restrict the index size or quantify over test objects in a
potentially vacuous smaller universe. All schemes in a diagram can share one universe
by enlargement. The affine-transition and qcqs hypotheses are genuine restrictions,
not universally true assertions about identity morphisms.

Searches made before writing:

- `msearch.py ... leansearch "Properness descends to a finite stage of an inverse limit
  of schemes with affine transition maps"`: UNAVAILABLE, Internal Server Error.
  No verdict drawn from this unavailable service.
- `msearch.py ... leanfinder "A morphism of qcqs schemes locally of finite type becomes
  proper at a finite stage if its base change to an inverse limit with affine
  transitions is proper"`: eight hits, concerning finite morphisms being proper,
  the definition of properness, valuative criteria, and properness from composition;
  none is this limit-descent statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, CategoryTheory.Limits.IsLimit"`:
  zero hits.
- `msearch.py ... grep "exists_isProper|eventually.*[Pp]roper|IsProper.*[Ll]imit"
  AlgebraicGeometry`: two hits, the properness instances of pullback projections;
  neither descends properness to a stage.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` for
  `descend_separated|exists_isSeparated|exists_isClosedImmersion|eventually.*[Pp]roper|
  exists_isProper`: nearby descent of separatedness and closed immersions in the
  source's AffineTransitionLimit, but no properness-at-a-stage declaration.
- `rg` for `lem-weil-pbc-eventually-proper|exists_isProper|eventually.*[Pp]roper` in
  the source repository, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no matches.
- Full-name collision search for `exists_isProper_baseChange_of_isLimit|EventuallyProper`
  in Mathlib, WeilConjectures, `lean/Sheaf`, and the upstream name index: no matches.

Validation: `scompile.py M1 lem-weil-pbc-eventually-proper
.../lean/Sheaf/AlgebraicGeometry/EventuallyProper.lean` compiled on the server in 1.6 s,
exit code 0, with no warnings. The final dry run is run after this report and record.

## Second reading by M1

I independently opened the item's node and module, every statement dependency's
node, and the recorded dependency declarations. The local Stacks checkout is absent;
I read the actual `limits.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex at
`situation-descent-property` and `lemma-eventually-proper`, together with the tag pages
https://stacks.math.columbia.edu/tag/081D and
https://stacks.math.columbia.edu/tag/081F. The source assumes exactly the three qcqs
schemes named by the node. No statement correction is present or needed.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

- Directed set I: `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
  Exact: Stacks directed sets need not be antisymmetric.
- Inverse system of schemes Sᵢ and compatible transitions: `D : Iᵒᵖ ⥤ Scheme.{u}`.
  Exact: the preorder category supplies the transition in the correct direction;
  `D.map (homOfLE hi).op` has source Sᵢ and target Sᵢ₀.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]`.
  Exact: Mathlib's recorded `IsAffineHom` requires affine inverse images of affine
  opens. Identity transitions impose nothing extra.
- Limit S and projections: `(c : Cone D) (hc : IsLimit c)`.
  Exact: S is `c.pt`; projection to Sᵢ₀ is `c.π.app (op i₀)`. A specified limit
  uses `IsLimit`, rather than assuming an unrecorded stronger property of S.
- Chosen stage 0 ∈ I: `(i₀ : I)`. Exact: no least-element hypothesis.
- S₀ qcqs: `[CompactSpace (D.obj (op i₀))]` and
  `[QuasiSeparatedSpace (D.obj (op i₀))]`. Exact scheme properties.
- X₀, Y₀ qcqs schemes: `{X₀ Y₀ : Scheme.{u}}` and both corresponding
  `CompactSpace` / `QuasiSeparatedSpace` instances. Exact; neither omitted.
- S₀-structures and the morphism over S₀: `a : X₀ ⟶ D.obj (op i₀)`,
  `b : Y₀ ⟶ D.obj (op i₀)`, `f₀ : X₀ ⟶ Y₀`, `h : f₀ ≫ b = a`.
  Exact: h is the required structure compatibility, not an additional hypothesis.
- X, Y and f: `pullback a (c.π.app (op i₀))`,
  `pullback b (c.π.app (op i₀))`, and their `pullback.map` with components
  `f₀`, `𝟙 c.pt`, and the base identity. Exact. I read `pullback.map` itself:
  its projections are the first projection followed by f₀ and the second projection
  followed by the identity. The equality arguments have the required orientations:
  `a ≫ 𝟙 = f₀ ≫ b` and projection composed with identity equals itself.
- Proper f: `hf : IsProper (pullback.map ...)` for precisely that induced map.
  Exact; it is not properness of a projection or of f₀.
- Locally finite type f₀: `[LocallyOfFiniteType f₀]`. Exact; no finite presentation,
  Noetherian, field, or separatedness hypothesis appears.
- Conclusion: `∃ (i : I) (hi : i₀ ≤ i), IsProper (pullback.map ...)`, using
  `D.map (homOfLE hi).op` and identity on Sᵢ. Exact: the witness is later than i₀
  and the proper morphism is fᵢ, with the same X₀, Y₀, structures, and f₀.

Dependency audit: I read `exists_limit_affine_transition` in
`Sheaf.AlgebraicGeometry.LimitAffineTransition`, including its cone and projection
clauses. The item only needs to specify an already supplied limit, so does not invoke
its existence theorem or inherit its same-universe restriction. I read the convention
node: it deliberately defines no separate notion. I checked Mathlib's
`quasiSeparatedSpace_iff_forall_affineOpens` and the definition of
`QuasiSeparatedSpace`; these are scheme quasi-separatedness, not separatedness or
quasi-separatedness of identity maps. I read `LocallyOfFiniteType`, `QuasiCompact`,
`IsProper`, `IsSeparated`, `UniversallyClosed`, and `pullback.map` in their recorded
Mathlib modules. The instance `UniversallyClosed → QuasiCompact` makes Mathlib's
locally finite type properness definition equivalent to the node's finite type form.
No private definition or unusable statement dependency was found. There are no new
nodes or dependency modules to review.

Edge cases: empty schemes and spectra of the zero ring are allowed. The empty index
set is excluded by i₀ exactly as in the node; a singleton is allowed and the witness
may be i₀. There is no requirement that i₀ be minimal, and equivalent indices in a
preorder are allowed. No integer n occurs in this statement; the docstring's Chow
argument includes n = 0. Arbitrary characteristics and mixed-characteristic bases
are included. Universe u for schemes and independent v for indices are bound, and
there is no quantification over test objects in a smaller universe. Neither qcqs nor
locally finite type is replaced by a universally true identity-map hypothesis.

Independent searches, with vocabulary distinct from the first worker's:

- `msearch.py M1 lem-weil-pbc-eventually-proper leanfinder "proper morphism descends
  from inverse limit to some index without finite presentation"`: eight hits,
  primarily descent of morphisms and closed-subset nonemptiness; no properness descent.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, CategoryTheory.Limits.Cone"`:
  successful query, zero hits.
- `msearch.py ... grep "IsProper.*IsLimit|IsLimit.*IsProper|081F" AlgebraicGeometry`:
  successful query, zero hits.
- Independently ran rg on the source's and Mathlib's AffineTransitionLimit modules
  for properness and 081F, and across source WeilConjectures, project lean/Sheaf,
  and the upstream-name index for properness with limit/stage terminology and the
  full declaration name. No equivalent theorem or name collision found. The nearby
  source results concern closed immersion / separatedness descent, not this theorem.
  The worker's LeanSearch unavailability is recorded above and is not positive evidence.

H5/H6/H8/H9: the module contains no definition, no hollow data, and just one theorem
whose proof is `sorry`. Every variable and universe is bound. The module and theorem
source docstrings identify this node; the theorem docstring follows all six DAG proof
steps, including re-basing, Chow, base changes, closed immersion at the limit, descent,
and properness of the final stage. Lines are at most 100 characters. The recorded
`lean.statement` was checked byte-for-byte against the theorem signature and agrees.

Mismatches found: none. Changes made: appended this independent second-reading report;
left the correct Lean module and node unchanged.

Validation: independently ran `scompile.py M1 lem-weil-pbc-eventually-proper` on the
module; server compilation completed in 1.7 s, exit code 0, with no warnings.

## Reviewer fix (R-evp1139)

The index type was `{I : Type v}` with an independent universe `v`, against the recorded
limit form (M1 d2371fc68 `exists_limit_affine_transition`, F1 a215660fd, J1 13cd55798):
the index type must live in the schemes' universe, `{I : Type u}`, or the limit cone over
`Iᵒᵖ ⥤ Scheme.{u}` need not exist in `Scheme.{u}` for large `I` and the statement departs
from the cited dependency. Changed to `{I : Type u}` and `universe u`; the report's claims
about separate universes v and u above are superseded. Nothing else changed.
