## Worker report

The module `Sheaf.AlgebraicGeometry.NormalTowerCommonLevelCoverGluing` states
`AlgebraicGeometry.Scheme.finiteEtale_normalTower_commonLevel_cover_gluing`.
Its proof is `sorry`. The other declarations contain actual canonical chart/pullback data;
`NormalTowerCoverGluing.Gluing` packages exactly the witnesses and equations in the
conclusion. It introduces no independent geometric notion. All helper declarations are
listed in `lean.declarations`. No new DAG node, dependency repair or statement correction
is needed. There are no disputed statements.

Hypothesis-by-hypothesis correspondence:

- The positive prime is `p : ℕ` with `hp : p.Prime`; primality includes positivity.
- The quasi-compact base is `V : Scheme.{u}` with `[CompactSpace V]`.
- The open is `U : V.Opens`; its scheme and inclusion are `U.toScheme` and `U.ι`.
- `P` belongs to `(@IsFinite ⊓ @Etale).Over ⊤ U.toScheme`, exactly the recorded
  finite étale category, with every morphism over the base allowed.
- The levels are the subtype `{m : ℕ // 0 < m ∧ Nat.Coprime m p}`. For prime `p`,
  its second condition is exactly being prime to `p`; no allowed positive level is omitted.
- `X` associates to each level an `Over V` object, retaining both its scheme and its
  structural morphism. `hNoeth` and `hCompact` say that every level is locally
  Noetherian and quasi-compact. These are the two required Noetherian hypotheses.
- `hNormal` says that every stalk at every level is an integrally closed domain.
  This is the node's local-ring definition, using `IsDomain` and `IsIntegrallyClosed`.
- `q a b hab : X b ⟶ X a` is an actual morphism in `Over V`. Its structure equation
  enforces compatibility with the maps to `V`, rather than assuming arbitrary maps.
  `q_id` and `q_comp` impose exactly the identity and divisibility-tower composition laws.
- `hGeneric` quantifies over every irreducible component and every point generic for
  that component and requires its structural image to lie in `U`. Thus the open inverse
  image contains the generic point of every component. Schemes are sober, so this does
  not exploit a possibly nonexistent generic point.
- `W : V → V.Opens` and `hW : ∀ v, v ∈ W v` give the prescribed neighbourhoods.
  `m : V → ...` gives their prescribed positive prime-to-`p` levels.
- `chart A W` is the actual chosen fibre product `pullback A.hom W.ι`.
  `Y v` is a finite étale cover of `chart (X (m v)) (W v)`.
- `θlocal v` is an isomorphism in the finite étale category over the actual chart
  at `W v ⊓ U`. Its source is the restriction of `Y v`; its target is the pullback
  of `P` along the canonical map to `U`. This is precisely the displayed specified
  isomorphism after the canonical identification of iterated fibre products.
  These data are supplied as a family of witnesses for the node's pointwise existence;
  since the conclusion must preserve the specified identifications, none is forgotten.

Conclusion, clause-by-clause:

- `s : ℕ` and `v : Fin s → V` are the selected finite list of points, without a
  nonemptiness or distinctness condition. `(⨆ j, W (v j)) = ⊤` is their covering equation.
- `n` is a positive prime-to-`p` level and `n.val = ∏ j, (m (v j)).val` is exactly
  the specified product, including the empty product `1`. `hd` supplies the divisibility
  proofs needed as arguments to the existing transition maps; it imposes no new choice
  of transition maps or mathematical hypothesis.
- `Gluing.Z` is a finite étale object over `(X n).left`.
- `Gluing.θ` identifies its restriction along `pullback.fst (X n).hom U.ι`
  with `P` pulled back along `pullback.snd (X n).hom U.ι`. This is the first required
  global displayed isomorphism over `U_n`.
- In `Gluing`, `B j = X (m (v j))`, `W j = W (v j)`, and
  `q j = q (m (v j)) n (hd j)`. Pulling `Y j` back along `chartMap (q j) le_rfl`
  is exactly the prescribed `Z_j` over `H_j = X_n ×_V W_j`.
- `localIdentification` constructs the induced `θ_j` from the *given* `θlocal j`.
  It uses the canonical pullback-composition and equality isomorphisms. No arbitrary
  natural isomorphism, stronger compatibility input, or normalization comparison is used.
- `Gluing.α i j` is an actual isomorphism of the restrictions of `Z_i` and `Z_j`
  over `chart (X n) (W i ⊓ W j)`, namely the actual overlap.
- `overlap_identification` states that pulling `α i j` back to the prescribed open,
  then composing with `θ_j`, gives `θ_i`. Since `θ_j` is invertible, this is exactly
  the restriction formula `θ_j⁻¹ θ_i`.
- `overlap_unique` says every isomorphism with that restriction equals `α i j`.
  Together with the `α` witness, this is the required unique existence.
- `identity` states `α i i = Iso.refl _`. `cocycle` states the composite of `α i j`
  and `α j k` equals `α i k` after the canonical restrictions to
  `(W i ⊓ W j) ⊓ W k`. `restrictLocalIso` uses the actual base-change functors and
  their canonical composition comparisons, so both sides have the same objects.
- `e j` identifies the global cover on `H_j` with `Z_j`. `induces` says these
  isomorphisms induce exactly `α i j`, after restricting both to the pairwise overlap.
- `identification` says the global `θ`, restricted to the dense open of each chart,
  agrees with that chart's specified, induced `θ_j` under `e j`.
- No field asserts that integral closure commutes with a tower map.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` has a conventions-only record and no declaration;
  the actual notions here are `Scheme`, `IsFinite`, and `Etale`.
- `def-weil-pbc-finite-etale-category`: `CategoryTheory.MorphismProperty.Over`
  (`Mathlib.CategoryTheory.MorphismProperty.Comma`) and
  `CategoryTheory.MorphismProperty.Over.pullback`
  (`Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`), with the exact
  specialization `(@IsFinite ⊓ @Etale).Over ⊤` specified by its `mathlib_match`.
- `def-weil-pbc-normal-ring`: `IsDomain`, `IsIntegrallyClosed`
  (`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`), applied to the scheme stalks.
  The extra localization quantifier for an arbitrary normal ring is unnecessary here:
  the node itself explicitly requires the stalks to be normal domains.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.map` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`),
  with existence for schemes from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-irreducible-components`: `irreducibleComponents`
  (`Mathlib.Topology.Irreducible`), and `IsGenericPoint` (`Mathlib.Topology.Sober`).
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`
  (`Mathlib.AlgebraicGeometry.Noetherian`).
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`
  (`Mathlib.Topology.Defs.Filter`).
- Stated proof dependencies are imported: `regular_normal_and_normal_decomposition`
  (`Sheaf.AlgebraicGeometry.RegularNormalDecomposition`) and
  `Scheme.finiteEtale_normalIntegral_generic_hom_full`
  (`WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`).
  The Mathlib proof leaves are supplied by Morphisms.Finite, Morphisms.Etale,
  AlgebraicGeometry.Gluing, and the target-locality API in Morphisms.Basic.

Edge cases checked before writing and again against the final signature:

- Empty `V`: `Fin 0 → V` exists, the open supremum is bottom = top, and the product
  is `1`; every scheme over `V` is empty. No `Nonempty V`, `0 < s`, or surjectivity of
  a finite étale cover is assumed.
- Nonempty `V` with empty tower levels: all fibre products and finite étale covers
  still make sense, and the conclusion permits an empty global cover.
- Empty `U`: generic containment forces every nonempty irreducible component away;
  sobriety and component coverage force the levels empty. No contradiction is hidden
  by adding an integral or nonempty hypothesis.
- Empty charts, overlaps, triple overlaps, and empty finite étale covers: all are
  permitted objects of the same categories; there is no field excluding them.
- Repeated selected points are permitted, as in a finite list. The product keeps
  multiplicities; `n` is not silently replaced by a least common multiple.
- Level `1`, any positive prime (including `2`), and arbitrary scheme universe `u`
  are retained. All objects in each fibre product have the same scheme universe;
  there is no independent smaller test-object universe.

Searches made on 2026-10-24 with the prescribed `msearch.py N7 <item>` wrapper:

- LeanFinder: "Finite etale covers locally extending a fixed cover on a dense open
  of a normal noetherian tower glue at the product of finitely many levels".
  Eight hits, including `Scheme.Cover.gluedCover_J`, affine-transition-limit cover
  constructions, and `Scheme.Cover.RelativeGluingData.cover`; none states the result.
- Loogle: `"FiniteEtale", "glue"`. Zero hits.
- Mathlib grep: `(FiniteEtale|finiteEtale).*(glue|dense|normal)|` followed by
  `(glue|dense|normal).*(FiniteEtale|finiteEtale)`. Zero hits.
- LeanSearch: "Finite etale covers of a normal noetherian scheme with specified
  identifications on a dense open glue at a common level of a tower".
  Eight hits: étale-site definitions, glued-cover charts and relative gluing data,
  but no extension theorem with generic uniqueness and the product-level conclusion.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for normal/common-level tower gluing, the item id, `normalTower`,
  `NormalTowerCoverGluing`, `finiteEtale_normalTower`, and `pullbackIdentification`:
  no existing statement or collision. Broader tower/normal searches returned
  unrelated normalized blowup and coefficient towers. The upstream generic-fullness
  theorem was read and used as a proof dependency, not duplicated.
- Read the recorded category/pullback signatures and docstrings in Mathlib, and the
  upstream finite étale category sources. The latter has another established model;
  this delivery uses the exact model named by this node's dependency instead of
  defining a third finite étale category.

Source reading: ILO PDF pages 139--140 (printed 133--134), IX Proposition 2.1 proof;
Stacks `pione.tex`, labels `proposition-normal` and
`lemma-finite-etale-covering-normal-unramified`; the current
`literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`.
The arbitrary-tower result is explicitly an agent-written deduction in the DAG,
not falsely attributed to a literal ILO theorem statement.

Validation: the prescribed `scompile.py` compiled this delivered module in sandbox
and library mode cleanly. Every variable and universe is explicitly bound; there
are no diagnostic commands, local notation, private helpers, local instances, or
postponed data definitions. The only postponed theorem is the named main statement.

## Second reading by N7

Author's second pass, with the node and final file open; the dispatcher brief forbids
starting another agent, so independent review is left to the maintainer as prescribed.

Compared the input binders against every hypothesis, and every `Gluing` field against
the corresponding conclusion. The final formulation keeps the isomorphisms as actual
finite étale categorical isomorphisms over the intended bases. In particular, the
selected product is present verbatim, `α` lives on pairwise overlaps, its uniqueness
is an explicit quantified field, and the triple-overlap cocycle is explicit rather
than inferred in the report. `e` and `identification` retain the prescribed local
identifications, which a bare existence of a global cover would have lost.

The compile exposed two syntactic/elaboration issues: the tower-map binder needed a
separate divisibility-proof binder, and the triple-overlap inclusions needed `le_inf`
rather than `inf_le_inf`. Both were repaired without changing the mathematics. The
initial helper-only compile also reported an unnecessary `simpa`; it was replaced
by `simp`. The final full-module compile is clean. No mathematical mismatch,
statement change, added hypothesis, dropped clause, or additional independent
notion was found on this pass.
