## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceNoetherianAmpleNeighbourhood` states
`AlgebraicGeometry.AlgebraicSpace.exists_relativelyAmple_neighbourhood_of_noetherian`,
with its sole proof `sorry`. It states Stacks Divisors on Spaces 0D3A, read in
`spaces-divisors.tex` at `lemma-ample-in-neighbourhood`, together with the definition
0D31 and scheme-base equivalence 0D32. The natural-language statement is unchanged.
No new nodes or dependency repairs are needed. Two existing, landed definition nodes
are added to stmt_deps to use their canonical notions rather than private copies:
`def-sfb-space-morphism-properties` and `def-trf-space-line-module-proj-input`.

Hypotheses and clauses:

- The Noetherian scheme T is `(T : Scheme.{u}) [IsNoetherian T]`. Mathlib
  `isNoetherian_iff_of_finite_affine_openCover` identifies this with precisely the
  finite affine cover by Noetherian rings in the node. Noetherian means both locally
  Noetherian and quasi-compact, not just a topological Noetherian-space hypothesis.
- The space X and its map to T are `(X : AlgebraicSpace T)` and
  `f : X ⟶ schemeSpace (Over.mk (𝟙 T))`. This follows the source's algebraic space
  over T convention; the representable terminal space is T itself.
- `hf : MapIsProper f` is exactly separatedness, finite type and universal
  closedness. Its existing definition uses the closed-immersion diagonal,
  quasi-compactness and all compatible etale scheme charts for local finite type,
  and closedness on point spaces after every algebraic-space base change.
- `(L : X.Modules) (hL : X.IsLineModule L)` renders the given small-etale line module,
  including local triviality on covering sieves.
- `(t : T)` is the arbitrary base point. The map `T.fromSpecResidueField t` is the
  canonical Spec(kappa(t)) to T, with the same universe u as T.
- `hfibre` asserts the existence of a scheme `Z : Over T`, its map `p` to this
  residue-field spectrum, and a Yoneda map `q` to X. The `IsPullback` clause says
  exactly that Z represents X_t, with both projections fixed. It is not an
  additional representability assumption on f away from t.
- `Scheme.Modules.IsAmple Z.left ((lineTestFamily X L hL).module
  (CostructuredArrow.mk q))` is ampleness of L_t on that scheme. `lineTestFamily`
  is the existing canonical cartesian family of scheme tensor pullbacks of L,
  obtained from the descent universal property and normalized by its small-etale
  identification. Its `invertible` instance supplies ordinary invertibility.
  In particular no independently chosen module or arbitrary map replaces L_t.
- The conclusion `∃ V : T.Opens, t ∈ V ∧ ...` imposes exactly an open neighbourhood,
  with no affineness, nonemptiness or connectedness added.
- The existential scheme `Z`, map to `Over.mk V.ι` and `q`, followed by the second
  `IsPullback`, asserts that X_V is a scheme with its actual map to V and to X.
- `∀ W : V.toScheme.Opens, IsAffineOpen W → ...` tests every affine open of V.
  The module in `IsAmple` is the ordinary `Scheme.Modules.tensorPullback` along
  `(p.left ⁻¹ᵁ W).ι` of the canonical restriction of L to Z. This is exactly
  L on the inverse image of W. The explicit invertibility witness is
  `invertible_pullback_tensor`; it adds no hypothesis. This is the node's entire
  relative-ampleness clause, justified as its scheme-base interpretation by 0D32.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; Mathlib's
  `Mathlib.AlgebraicGeometry.Noetherian` supplies `IsNoetherian` and its finite
  affine-cover characterization using exactly those Noetherian rings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its scheme-test
  `IsRepresentableWith`, `Modules`, and `IsLineModule` (the full local-unit signature).
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `schemeSpace` and the public
  enlarged ringed-site constructions (in particular `cotangentRingMap` and its
  chart normalization), supplying the canonical interpretation of tensor pullback.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`; its line-module
  clauses and normalized pullback comparisons give the scheme interpretation.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, local rank-one triviality on Zariski opens.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`, including
  quasi-compactness and positive tensor-power affine nonvanishing neighbourhoods.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper` and its
  three component predicates, matching every properness clause in the item.
- `Sheaf.TraceFormula.SpaceLineModuleProjInput`: `lineTestFamily`,
  `linePresentation`, and `exists_linePresentation`; its publicly imported
  `SpaceLinePresentationDefs` gives `TestLineFamily.module` and `.invertible`.
  Read the complete cartesian coherence and etale identification signatures:
  the existing universal property determines these pullbacks up to the unique
  compatible isomorphism, so this use is not an arbitrary Nonempty choice.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.fromSpecResidueField`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `Scheme.Modules.invertible_pullback_tensor`, the explicit witness in the conclusion.

Proof-only imports are the available recorded project/source modules for projective
quotient geometry, standard projective-space charts, etale open-chart morphism descent,
projective-space properness, projective chart preimages, affine ample pullback, the
free-projective-bundle/base-change comparison, and the morphism given by generating
sections. Mathlib affine schemes, proper morphisms, closed immersions, finite morphisms,
and affine morphisms are imported for the recorded Mathlib proof matches. Unstated
proof prerequisites (space section lifting, space proper base change/composition,
closed subspace properness, quasi-finite locus, finite-fibre criterion and the proper
locally quasi-finite scheme theorem, and eventual-power immersion) have no recorded
module to import yet. The docstring retains all nine proof steps and their node uses.

Edge cases checked before writing:

- Empty X_t: no Nonempty assumption is made on Z or X. The fibre condition includes
  the empty representing scheme; its ampleness condition is vacuous apart from
  compactness, which the empty scheme has. Properness permits shrinking away from
  the image, as the node's first proof step explains.
- Empty base: the binder t makes that case vacuous, exactly as the source.
- Nonclosed t and arbitrary residue characteristic: the actual residue-field map is
  used; no closed-point, algebraically closed-field or characteristic restriction.
- No finite family or nonempty index is postulated in the signature. Relative
  ampleness quantifies all affine opens, including any empty affine open.
- Schemes and their representing tests use the common size convention u. There is
  no independent smaller test universe, no site/coefficient universe equality, and
  all variables and universes are explicit (`autoImplicit false`).

Searches actually run:

- msearch leanfinder: "Proper algebraic space over a Noetherian scheme with ample
  schematic fibre has a schematic relatively ample open neighbourhood". Eight hits,
  including IsLocallyNoetherian, quasi-affine schemes and affine-neighbourhood
  reductions; no algebraic-space ample-neighbourhood theorem.
- msearch loogle: "AlgebraicGeometry.Scheme.Modules.IsAmple,
  AlgebraicGeometry.IsProper". Zero hits; the service reports unknown identifier
  for the project's IsAmple, which is not a Mathlib declaration.
- msearch grep: "ample.*neigh|[Aa]lgebraic[Ss]pace|ample.*fiber" in AlgebraicGeometry:
  zero Mathlib hits.
- rg of upstream WeilConjectures for ampleness/neighbourhood and the exact item id:
  existing scheme ampleness lemmas, no statement about an algebraic space and no
  exact item-id match. The upstream IsAmple and IsInvertible definitions are reused.
- rg of Sheaf for noetherian ampleness, schematic fibres and neighbourhoods: scheme
  versions `NoetherianFibreAmpleNeighbourhood` and `TraceFormula.AmpleNeighbourhood`
  do not imply schematicity of a general algebraic space. `AlgebraicSpaceAmpleLocal`
  assumes etale-local schematic ampleness, rather than a single schematic fibre.
- Searches for canonical pullbacks and scheme restriction found the existing
  `lineTestFamily`, `MapIsProper` and their owning DAG nodes, which are reused.
- rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for the
  proposed new theorem name found no collision.

Validation: the single delivered module compiles through scompile.py against the
published server library, in module mode, with no errors or warnings. No statement
correction or STATEMENT-DISPUTED issue was found. The withdrawal-only CompactObject
example now contains no declarations, so the module follows the header, public-import,
exposed-section and docstring conventions in the current neighbouring statement modules.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
