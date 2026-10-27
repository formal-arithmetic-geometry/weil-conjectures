## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceIntegralExtensionQcOpen` states
`AlgebraicGeometry.AlgebraicSpace.exists_integral_extension_qcOpen`, with its sole proof
`sorry`. It is the algebraic-space extension lemma of Stacks Tag 0G2D,
`literature/stacks-project/decent-spaces.tex`, lemma-extend-integral-morphism, read in full
with its proof. No node statement, definition, or dependency record is changed.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `{V B Z : AlgebraicSpace S}` are arbitrary
  algebraic spaces over that same base, and `(j : V ⟶ B) (π : Z ⟶ V)` are their given
  morphisms. `AlgebraicSpace` is the recorded full subcategory of fppf sheaves, with
  representable diagonal and an étale surjective scheme atlas. Morphisms are its natural
  transformations. The explicit `universe u` follows the recorded size convention and
  imposes no additional equality of universes or smallness hypothesis.
- The quasi-compact open immersion is `hj : IsRepresentableWith (fun _ _ p ↦
  IsOpenImmersion p.left ∧ QuasiCompact p.left) j.hom.hom`. This quantifies over every
  scheme over `S` and every map of its Yoneda presheaf to `B`, supplying a representing
  pullback square whose scheme projection is both open and quasi-compact. The two
  properties are tested on the same representing scheme, as required. This is also the
  interface already used by `exists_qcOpen_schematicClosure`.
- Integrality of `Z → V` is `hπ : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left)
  π.hom.hom`. The recorded Mathlib `IsIntegralHom` includes affineness and integral
  maps of sections on every affine target open. No finite-type or surjectivity
  hypothesis is imposed.
- The extension is `∃ (E : AlgebraicSpace S) (ν : E ⟶ B)`, with the same scheme-test
  integral predicate on `ν.hom.hom`.
- `∃ e : Limits.pullback ν.hom j.hom ≅ Z.obj` is the isomorphism of fppf sheaves
  `E ×_B V ≅ Z`. The recorded fibre-product theorem identifies this sheaf pullback
  with an algebraic-space fibre product. Fullness of the algebraic-space category makes
  this exactly an isomorphism of algebraic spaces, without an additional representability
  assumption.
- `e.hom ≫ π.hom = Limits.pullback.snd ν.hom j.hom` says precisely that the isomorphism
  is over `V`.
- `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
  (e.inv ≫ Limits.pullback.fst ν.hom j.hom).hom` states that the induced inclusion
  `Z → E` is an open immersion. Its map is explicitly the inverse isomorphism followed
  by the first pullback projection, so it is the specified pullback open immersion,
  rather than an unrelated existential open map. The pullback identity and the preceding
  equation also give its composite to `B` as `π ≫ j`.
- The introductory atlas topology, geometric-point/fibre, quasi-separatedness, separatedness,
  and étale conventions set the ambient vocabulary; none adds a hypothesis or conclusion
  to this extension lemma. The recorded topology and geometric-point modules are imported;
  the geometric fibre is the sheaf pullback already used here. In particular no
  quasi-separatedness or quasi-compactness of `B`, `V`, or `Z` as a space is assumed.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsAlgebraicSpace`, `IsEtale`;
  scheme tests are genuine representing `IsPullback` squares of presheaves.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`, with the existing `Point` point classes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` (read full signature and proof docstring),
  and its sheaf `Limits.pullback` interface.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`:
  `AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.IsIntegralHom`; the latter is the
  actual predicate needed. Both are the recorded integral/finite dependency modules.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (ambient separatedness convention).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric-point dependency's
  other recorded signature `Scheme.SpecToEquivOfField` was read in Mathlib's
  `AlgebraicGeometry.ResidueField`. No geometric point occurs as theorem data.
- `def-weil-size-convention` is a metatheoretic convention, with no module/declaration;
  all variables and the universe are bound explicitly, with `autoImplicit false`.
- The already stated proof dependency `lem-a1-space-open-chart-tests` is imported privately
  as `Sheaf.AlgebraicGeometry.SpaceOpenChartTests`; its declaration
  `AlgebraicSpace.space_open_chart_tests` and full proof docstring were read.
  The integral scheme predicate is also a proof dependency and is imported publicly
  because it occurs in the statement.
- The other proof-only nodes currently have no `lean` or `mathlib_match`, and are not
  needed to type the statement: `lem-sfb-space-integral-qcqs-permanence`,
  `lem-sfb-space-separated-fp-composition`, `lem-sfb-space-relative-integral-factorization`,
  and `lem-sfb-space-integral-factorization-etale-base-change`. Their imports can be added
  when their statements land. The theorem docstring contains all five proof steps,
  including their precise roles, for stage 3.

Edge cases checked before writing:

- For `V` empty, a morphism `Z → V` forces `Z` empty; the empty integral extension
  satisfies the result. No `Nonempty` binder excludes it, including when `B` or `S`
  is empty.
- For `Z` empty over any `V`, take the empty extension over `B`. Empty morphisms are
  integral, and the induced inclusion is open.
- For `j = id`, take `E = Z`, `ν = π`, and the identity-base-change isomorphism; `π`
  need not be an open immersion, whereas the induced map `Z → E` is the identity.
- For `π = id`, take `E = B`; the displayed inverse-image isomorphism and induced
  open map are the given `j`.
- A non-quasi-compact ambient space is allowed; the hypothesis concerns the morphism
  `j`, not compactness of its source or target. Integrality is not confused with an
  integral source space, finiteness, or surjectivity. No characteristic restrictions occur.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder`, query: “An integral morphism to a quasi compact open
  subspace of an algebraic space extends integrally to the whole algebraic space”.
  Eight hits, consisting of integral-scheme restriction and scheme-normalization
  declarations. None states the algebraic-space extension result.
- `msearch.py ... loogle`, query:
  `AlgebraicGeometry.IsIntegralHom, AlgebraicGeometry.IsOpenImmersion`. Zero hits.
- `msearch.py ... leansearch`, query: “Integral morphism over a quasi-compact open
  immersion of algebraic spaces extends to an integral morphism over the ambient
  algebraic space”. Eight hits on `IsIntegralHom`, its constructors, restriction,
  and scheme properties, with no match for this statement.
- `msearch.py ... grep`, query `extend.*integral|integral.*extend|extension.*qc`,
  restricted to `AlgebraicGeometry`: the sole reported hit was `IsIntegralHom`.
- Direct `rg` searches in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib's
  `AlgebraicGeometry` used the node id, `space_integral_extension_qc_open`,
  `exists_integral_extension`, and integral/extension patterns. No exact declaration
  or duplicate proposed name was found. `dag/lean_names_upstream.json` has no node-id hit.
  `IntegralSurjectiveOpenExtension.lean` was opened: its
  `AlgebraicGeometry.exists_surjective_integral_extension` concerns schemes and imposes
  surjectivity, so it does not cover this statement. The schematic-closure theorem was
  opened to confirm reuse of the identical quasi-compact open scheme-test interface.

No new nodes or dependency modules were required. No statement dispute or correction.
Only the item's `lean` field is changed. `scompile.py Q18 lem-sfb-space-integral-extension-qc-open` compiled the delivered
file successfully against the server build in both sandbox and library module modes
(1.9 seconds and 1.8 seconds respectively), with no errors or unexpected warnings.

## Second reading by Q18

Final clause-by-clause self-check against the node and the complete module: `hj` expresses
both open immersion and quasi-compactness on every scheme test; `hπ` expresses exactly
representable integrality. The output has an algebraic space, an integral map to `B`, a
sheaf isomorphism commuting with `V`, and the induced open immersion. The order of the
pullback is `E ×_B V`, so its second projection is the map to `V` and its first projection
gives the inclusion into `E`. No extra hypothesis or conclusion was introduced. There are
no definitions with missing data, no unbound variables, and exactly one named postponed
theorem, matching the item. No mismatch was found. This is a self-check by the dispatched
worker; the maintainer supplies the independent delivery review required by this brief.
