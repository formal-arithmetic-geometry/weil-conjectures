## Worker report

The module `Sheaf.AlgebraicGeometry.CoproductModelRepresentsSheaf` states
`AlgebraicGeometry.coproductModel_represents_sheaf`, with its proof entirely `sorry`.
It also supplies `coproductModelProjection`, a transparent abbreviation for the existing
`Sigma.desc (fun _ : S ↦ 𝟙 V)`, with actual morphism data. No new mathematical notion,
new node, dependency repair, or statement correction is required. The original node is
copied with only `lean` changed.

Source checked: the CURRENT blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice-scheme.proof.md`,
(2)--(3), and `literature/stacks-project/descent.tex`, the lemmas with labels
`lemma-descending-property-separated`, `lemma-descending-property-etale`, and
`lemma-fpqc-universal-effective-epimorphisms` (Tags 02KU, 02VN, 023Q).
The new module's docstring records all eight proof steps of the DAG node.

Hypotheses and objects, clause by clause:

- Schemes `X`, `V`, `Y` are explicit `Scheme.{u}` binders; `p : V ⟶ X` has
  `[WeaklyEtale p] [Flat p] [Surjective p] [QuasiCompact p]`, retaining every
  stipulated property, including the flatness already implied by weak étaleness.
- The specified singleton fpqc covering is the explicit `hp : Presieve.singleton p ∈
  Scheme.fpqcPrecoverage X`. This is the one-arrow version of `Presieve.ofArrows`.
- The set is `S : Type v` with `[Small.{u} S]`, so indices may have any presentation
  universe while their size lies in the chosen scheme bound. This is exactly the
  universe convention needed for Mathlib's scheme coproduct, not a finiteness or
  nonemptiness restriction. The independent scheme bound `u` can be enlarged freely.
- `T` is literally the chosen scheme coproduct `∐ fun _ : S ↦ V`; its structure map
  is `coproductModelProjection V S`. No arbitrary scheme or arbitrary structure map
  replaces the coproduct.
- The sheaf of sets is `F : Sheaf (Scheme.ProEt.topology X) (Type w)`, with an
  independent explicit section universe `w`. Its sheaf axiom is part of this type.
- A weakly étale `W → V` is `W : V.ProEt`. Postcomposition to the original site is
  `(MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale p)).obj W`.
  The binder `a` gives precisely an `Equiv` from its section set to
  `Over.mk W.hom ⟶ Over.mk (coproductModelProjection V S)`, i.e. `Hom_V(W,T)`.
- `ha` states naturality for EVERY morphism `g : W' ⟶ W` in this full small site;
  neither `g` nor its underlying map has an extra property imposed.
- `δ : Over.DescentDatum p (Over.mk (coproductModelProjection V S))` is the recorded
  upstream datum, including naturality, identity, and cocycle. Its source docstring
  establishes its Yoneda-equivalent formulation as transport of points, avoiding
  a second definition of the isomorphism over `R = V ×_X V`.
- `hδ` says transport along `f₁,f₂ : W ⟶ V` with equal composites to `X` takes the
  image under `a` of a section to its image under `a` on the second restriction.
  The section is transported by `F` along the identity map on the underlying scheme.
  Both `f₁` and `f₂` have explicit weak-étaleness proofs because these evaluations of
  `a` are on the small site. This is the canonical comparison of the two restrictions
  of `F|_V`. Evaluating on weakly étale objects over `R`, and using naturality, recovers
  exactly the isomorphism formulation in the node. In particular, the overlap objects
  used by the proof have both maps weakly étale by base change and composition.
- `q : Y ⟶ X` is arbitrary. `η : (Over.pullback p).obj (Over.mk q) ≅
  Over.mk (coproductModelProjection V S)` is precisely `Y ×_X V ≅ T` over `V`.
- `hη` quantifies over all test schemes and all pairs of points, exactly as the
  recorded `DescentDatum.IsEffective` invariance interface does: transport leaves
  the map to `Y` given by `η.inv.left ≫ pullback.fst q p` unchanged. Together with the
  specified cartesian isomorphism, this says that this particular `η` induces `δ`;
  it does not merely assume some effective model exists.

Conclusions, clause by clause:

- `IsSeparated q ∧ Etale q` is separatedness and étaleness of the given descended map.
- `Nonempty S → Surjective q` asserts surjectivity only under the stated condition.
- `∃ hY : WeaklyEtale q` supplies the site-object witness for `Y`; the auxiliary
  proof `hT : WeaklyEtale (coproductModelProjection V S)` similarly permits evaluation
  of `a_T`. These are conclusions, not additional hypotheses. Proof irrelevance
  makes the resulting site objects independent of these witnesses.
- `∃! b : ∀ U : X.ProEt, F.obj.obj (op U) ≃
  ((Scheme.ProEt.forget X).obj U ⟶ Over.mk q), ...` states existence and uniqueness of
  the family of bijections to `Hom_X(U,Y)`.
- The first conjunct in the unique-existence predicate is naturality for every
  `g : U' ⟶ U`. The second is normalization on `U_V`: its left side restricts `s`
  along `pullback.fst U.hom p` and applies `a` on the pulled-back object over `V`;
  its right side is the map `(b_U(s)|_{U_V}, pr_V)` composed with `η.hom.left`.
  The `pullback.lift` compatibility is derived from `Over.w (b U s)` and the
  pullback condition, not supplied as an extra hypothesis.
- The equivalent descent description in the node is encoded by that normalization
  plus the `Equiv`: the local map descends to `b U s`. Conversely, specialize the
  same equation to `s = (b U).symm f`; `Equiv.apply_symm_apply` says its image is `f`,
  so its restriction is exactly `a^{-1}` of the pulled-back map composed with `η`.
  This is the asserted inverse, without adding a redundant equation.
- The universal section is written explicitly as
  `(b (@Scheme.ProEt.mk _ _ q hY)).symm (𝟙 (Over.mk q))`.
  The third conjunct says `b_U(F(f)(u)) = f` for EVERY site morphism to `Y`,
  whose forgetful image is every scheme map over `X` from a site object.
- The final conjunct is the promised local formula on `T`. It pulls `u` back along
  `r = η.inv.left ≫ pullback.fst q p`, applies `a_T`, and obtains precisely
  `𝟙 (Over.mk (coproductModelProjection V S))`. The map to `Y` is proven over `X`
  from `Over.w η.inv` and the pullback condition.

Dependencies used, after reading each recorded declaration and its docstring:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.mk`,
  `Scheme.ProEt.forget`, `Scheme.ProEt.topology`; `WeaklyEtale` and its composition,
  base-change, and étale-to-weakly-étale instances are the imported Mathlib ones.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage`, and
  `Scheme.instSubcanonicalFpqcTopology` for fpqc morphism descent (proof dependency).
- `Mathlib.AlgebraicGeometry.Limits`: the recorded scheme coproduct instance,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι`; the statement uses the corresponding
  `Sigma.desc` and chosen coproduct, with the stipulated smallness.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the record explicitly retains
  Mathlib `Sheaf` for the sheaf component, and that is what this statement uses.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum`, particularly `transport`, and the invariance
  description in `Over.DescentDatum.IsEffective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`
  (defined in its imported `Morphisms.Separated`), not properness itself.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- The scheme-conventions and size-convention nodes explicitly declare no new notion:
  their properties are the Mathlib classes listed above, and their size convention
  is rendered by explicit `u v w` and `Small.{u} S`.
- Plain proof-only imports are
  `WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`
  (`isSeparated_of_flat_surjective_baseChange`),
  `WeilConjectures.AlgebraicGeometry.FpqcDescentEtale` (`etale_of_fpqc_cover`), and
  `Sheaf.AlgebraicGeometry.EtaleComparison`
  (`etale_indEtale_weaklyEtale_comparison`). All other recorded proof dependencies
  are Mathlib declarations available through the statement imports (source locality,
  open-immersion base change, closed immersions, base-change stability of coverings,
  and subcanonical fpqc topology).

Edge cases checked before and after writing:

- Empty `S` is allowed: there is no nonemptiness instance on it. The chosen coproduct
  and codiagonal still exist; the surjectivity clause remains an implication.
- Empty `X` (hence empty `V`, `Y`, and local models) is allowed: no nonempty scheme
  hypothesis or nonempty-point choice occurs. The sheaf's empty-cover axiom yields
  the required singleton sections, even for the empty index type.
- Infinite `S` is allowed, with no quasi-compactness requirement on `T → V` or `Y → X`.
  Only the stipulated covering morphism `p` is quasi-compact.
- `F` is not assumed nonempty-valued; `Equiv` covers empty section sets as well.
- All `X`-maps between site objects are included; no additional weak-étaleness
  assumption is placed on test morphisms for naturality or the universal formula.
- `η` need not be a preferred isomorphism: normalization and transport compatibility
  refer to the particular supplied isomorphism, so twisting it changes the normalized
  family as required.

Searches (2026-10-23), all via the prescribed tools/read-only source paths:

- `msearch.py ... leanfinder "A sheaf on the small pro etale site locally represented
  by a coproduct is represented by its descended separated etale scheme"`: 8 hits,
  including `Scheme.LocalRepresentability.representableBy`, `.isRepresentable`,
  `.yonedaIsoSheaf` and basic étale site definitions. The representability results
  require a big Zariski sheaf and relatively representable open charts, unlike this
  small pro-étale sheaf, and do not state the normalized or universal-section clauses.
- `msearch.py ... loogle 'AlgebraicGeometry.Scheme, "representable"'`: 2 hits,
  the same `.isRepresentable` and `.representableBy`, not an exact match.
- `msearch.py ... grep 'representab.*descen|descen.*representab|[Ee]tale.*[Cc]oproduct'
  AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "A sheaf locally represented by a coproduct on a weakly
  etale fpqc cover is represented by its descended scheme"`: 8 hits, big-Zariski
  local representability, coproducts of locally ringed spaces/sheaves, gluing, and
  quasi-coherent presentations; no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for representability/descent and
  coproduct-model patterns found `Functor.RepresentableBy.exists_representableBy_of_descent`
  and `nonempty_representableBy_of_effective_fpqc_descent`. Their full signatures
  require presheaves on all `Over X`/big fpqc sheaves, not the small pro-étale site,
  and they do not give the coproduct property descent or normalized universal section.
  `EtaleRepresentableDescentGlue` is an étale-cover gluing result, also different.
- Exact blueprint-id `grep -rn` in `lean/WeilConjectures`: no match.
- Name checks in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and
  `lean/Sheaf` found neither new declaration name. The existing
  `constantGroupSchemeProjection` additionally requires an `AddCommGroup` index,
  so cannot express this arbitrary set (including the empty set). The supplied
  abbreviation only names the existing `Sigma.desc` morphism for this statement.

Validation: `scompile.py O2 lem-sfb-coproduct-model-represents-sheaf <module>` passed
both the sandbox check and the library-name check, with no errors or warnings.
The only postponed theorem is `AlgebraicGeometry.coproductModel_represents_sheaf`.
No `STATEMENT-DISPUTED` issue was found.

## Second reading by O2

The dispatcher explicitly forbids starting another agent; this section records the
worker's second reading, not an independent agent's review. The maintainer supplies
the independent delivery review. I reread the node, current source proof, and final
Lean side by side. I checked the orientation of `η` (pullback to model), of `a`
(sections to maps), and of `hδ` (first lift to second lift); the morphism inserted
in `F.map` is the identity from the second restriction to the first, so its
contravariance gives the required direction. I checked `hη` matches the recorded
effectivity invariance condition with the particular projection to `Y`. I checked
that the unique-existence predicate includes naturality, normalization, and both
universal-section formulas and that it permits arbitrary and empty index types.
The three compile repairs only made the existing compatibility proofs explicit:
identity composition, the `Over.w` equation for `b_U(s)`, and the `Over.w` equation
for `η.inv`; they changed no mathematical hypothesis or conclusion. No unmatched
node clause or new source-based correction was identified.
