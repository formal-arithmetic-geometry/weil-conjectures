## Worker report

This is the stage-2 statement of lem-sbc-sets-underived-exchange-sectionwise, not a
repeat of its already merged stage-1 split. The base node has `status: split` and a
stage-1 review by NA but no Lean record. The previous unchanged-node rejection
therefore did not establish that a Lean statement existed. This delivery adds the
Lean record and its module, leaving the mathematical statement and proof unchanged.

The module is `Sheaf.AlgebraicGeometry.SetUnderivedExchangeSectionwise`; its theorem
is `AlgebraicGeometry.setUnderivedExchangeSectionwise`. The only postponed proof is
this theorem, and its docstring carries all five steps of the node's proof with
sources and dependency names. All five helpers have real data and source/blueprint
docstrings. There are no new DAG nodes, no dependency repairs, and no statement
correction. No statement dispute was found.

Hypotheses and objects, individually:

- The four schemes are explicitly bound as `{X' X Y' Y : Scheme.{u}}`.
- All four arrows are separately bound with precisely the original endpoints:
  `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`, `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`.
- The Cartesian square is `sq : ChosenCartesianSquare g' f' f g`, the recorded
  dependency's actual structure. Its `w` supplies commutativity and its
  `isoPullback` and projection equations supply Cartesianity. Neither smoothness,
  properness, étaleness of any square edge, nor any finiteness is assumed.
- A sheaf of sets on X is `F : Sheaf X.smallEtaleTopology (Type (u + 1))`.
  This is the project's existing set-sheaf convention, with no abelian structure.
- The test object is `V : Y'.Etale`, the representing object is `W : Y.Etale`,
  and `a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj W` is exactly a
  morphism over Y' into the base change of W.
- The representative section is
  `s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))`.
  The base-change object is W ×_Y X, canonically the X ×_Y W of the node; this
  follows Mathlib's established ordering, not a different mathematical object.

Clauses and constructions, individually:

1. `sq.exchangeTranspose` is the chosen Cartesian square with horizontal and
   vertical arrows exchanged. Its fibre-product identification is
   `sq.isoPullback ≪≫ pullbackSymmetry f g`; its fields use the original equations
   and existing Mathlib projection identities as terms. It introduces no theorem
   or proof placeholder.
2. The exchange itself is the already landed
   `Etale.setBaseChangeArrow sq.exchangeTranspose F`. Its type is exactly
   `g⁻¹ f_* F ⟶ f'_* g'⁻¹ F`, since the transposed square substitutes g and g'
   for the existing construction's inverse-image edges. No duplicate exchange
   morphism is constructed.
3. `sq.setExchangeComparison G` is precisely c_{g,f'} followed by transport
   from f' ≫ g to g' ≫ f using `sq.w.symm`, followed by the inverse of c_{f,g'}.
   The isomorphisms are taken from
   `Classical.choose etaleSetInverseImageCompositionUnits.2.2`. That theorem
   explicitly characterizes each component uniquely by its unit equation, so
   this choice is determined and is the existing canonical comparison.
4. The theorem's first conjunct identifies the existing arrow with
   `(Etale.setUpperLowerAdjunction f').homEquiv _ _` applied to that comparison
   at f_*F followed by `Scheme.etaleSetPullback g'` of the f counit. This renders
   the node's defining transpose, including its specified normalization.
5. `sq.setExchangeRestrictionMap V W a` is ℓ_a. It applies base change along f'
   to a, passes from (W ×_Y Y') ×_{Y'} X' to W ×_Y X' using the inverse of
   `Over.pullbackComp f' g`, and then passes to (W ×_Y X) ×_X X' using
   `Over.pullbackComp g' f (f' ≫ g) sq.w.symm`. This is the universal
   fibre-product map induced by the square and a. Its domain is V ×_{Y'} X',
   the node's A with factors canonically swapped; its target is the node's
   X' ×_X (X ×_Y W), with those same canonical symmetries. It is a morphism
   of X'-étale objects, so restriction of the inverse-image sheaf is typed.
6. `setExchangeRepresentative f g F V W a s` is the actual sheafified class.
   It applies `Over.pullback g |>.op.lanUnit` at W to s, then the Kan-extension
   presheaf restriction along a, then `toSheafify` at V. Thus the theorem
   quantifies over actual presheaf representatives, rather than treating all
   sheaf sections as single global representatives.
7. `sq.setExchangeRepresentativeImage F V W a s` applies the g' adjunction
   unit to s over the base change of W along f, then restricts via ℓ_a.
   Its type is `(g'⁻¹F)(A)`, definitionally `(f'_*g'⁻¹F)(V)`.
   The second conjunct states the required image formula on every W,a,s.
8. The third conjunct quantifies over two arbitrary representing triples at
   the same V. Equality of their actual sheafified classes implies equality
   of the unit-and-restriction outputs. This includes identifications arising
   only after sheafification, not merely a single transition in the colimit.
9. The last conjunct quantifies over all F,F₁ and ψ : F ⟶ F₁, and asserts
   the naturality square using the existing inverse/direct-image functors
   on morphisms. Naturality of the representative rule follows from this and
   the displayed formula. Restriction in V is inherent in the sheaf morphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`; `Scheme.smallGrothendieckTopology` is its
  underlying topology spelling used by the existing functors.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf` and its
  underlying presheaf `obj`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including all four structure fields.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`:
  `AlgebraicGeometry.etaleSetInverseImageCompositionUnits`, including both unit
  naturality clauses, unit normalization, fixed-sheaf uniqueness, and associativity.
  This is the recorded upstream module; the retired Sheaf module is not imported.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, `pullbackSymmetry`, and both hom projection identities.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, and `sheafificationAdjunction`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`:
  `AlgebraicGeometry.Etale.setUpperLowerAdjunction`,
  `AlgebraicGeometry.Etale.setBaseChangeArrow`. The already landed node
  sbc-def-base-change-map is added to stmt_deps to cite these shared helpers.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`:
  `Scheme.etaleSetPullback`, the actual Kan-extension/sheafification definition.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`,
  whose direct-image definition has no abelian constraint after unused section
  instances are eliminated, and is evaluation on base change.
- The mathlib-status proof dependencies' `mathlib_match` records were read:
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` in
  `Mathlib.CategoryTheory.Sites.Pullback`; `Functor.lan`, `Functor.lanUnit`,
  `Functor.lanAdjunction` in `Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`;
  `lan_preservesFiniteLimits_of_preservesFiniteLimits` in
  `Mathlib.CategoryTheory.Functor.Flat`. Their modules are imported publicly
  through the existing constructions, with Flat also a proof-only import.

The source was opened at etale-cohomology.tex, lemma-base-change-local, including
its preceding definition of the set-valued base-change map and proof of (1).
Tag 0EZR was verified in the Stacks tags table. The five-step node proof makes
explicit the representative calculation used for restriction in that source.

Edge cases checked mathematically before writing:

- Identity square: the chosen comparisons normalize by the composition units;
  the formula becomes the ordinary unit/restriction rule, with identity ℓ_a
  on an identity representative.
- f = identity: f_* evaluates on a canonically trivial base change, and the
  formula is the g' inverse-image unit followed by restriction.
- V empty or any scheme empty: the formula still uses the site's actual
  pullbacks and sheafification; there is no nonempty or nonzero assumption.
  A sheaf has its required singleton value on the empty test object.
- Terminal sheaf: both sides are the unique section; there is no additive
  zero being substituted for a set section.
- Arbitrary characteristic and arbitrary scheme universe u: no field,
  characteristic, dimension, separatedness or boundedness restriction occurs.
- Two representatives equal only locally after sheafification: the third
  conjunct uses equality in g⁻¹f_*F(V), so covers this case explicitly.

Searches for an existing statement (all made for ND and this item):

- msearch.py leanfinder: “sectionwise representative formula for exchange of
  sheaves of sets on small etale sites”; eight hits on typesGlue, compatible
  families, evalEquiv and glued sheaves, none is the exchange formula.
- msearch.py loogle: `CategoryTheory.Sheaf, CategoryTheory.Adjunction.homEquiv`;
  ten hits on module sheafification, cocontinuous adjunctions, skyscraper and
  condensed sheaves; none is the sectionwise set exchange theorem.
- msearch.py leansearch: “For a Cartesian square of schemes the underived
  exchange of sheaves of sets maps sheafified representatives to restriction
  along the induced fibre product map”; eight hits on Mayer–Vietoris sheaf
  squares, module adjunctions, Cartesian monoidal sheaves and relative gluing;
  none is this statement.
- msearch.py grep: `underived|exchange|sectionwise|representative` in
  `CategoryTheory/Sites`; hits are whisker exchange, external URL strings,
  and representatives in concrete sheafification, with no exchange formula.
- rg over project and upstream sources found the existing setBaseChangeArrow,
  setUpperLowerAdjunction and unique composition-unit theorem; these are reused.
  The abelian square comparison requires an abelian coefficient category and
  is not a set-valued match. Existing section-comparison maps concern commuting
  triangles, not this exchange arrow.
- rg of the five proposed helper names and theorem name in lean/Sheaf and
  the upstream source, and grep of this blueprint id upstream: no matches.

Validation: every delivered Lean file is compiled through scompile.py under the
normal 60-second per-file limit; dry-run preflight is run through deliver2.py.
The compilation and dry-run outcomes are recorded below when available.

Validation result: scompile.py compiled both sandbox and library forms cleanly,
with no errors or warnings. deliver2.py --no-push reported that commit dea1e129de
passes preflight and compiles. The unchanged-node failure is resolved by the new
stage-2 Lean record. All checks used the authorized wrappers; no global build or
live-source edits were made.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
