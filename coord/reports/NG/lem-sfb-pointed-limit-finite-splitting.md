## Worker report

This is the stage-2 statement of `lem-sfb-pointed-limit-finite-splitting`, not another
stage-1 split. The live node has a reviewed stage-1 proof under Q86 but no `lean`
record and no released repair note. The previous worker's stage-1 live-wins objection
does not prevent this dispatched stage-2 work. No live file was edited.

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitFiniteSplitting`
states all clauses of the node. Its four theorems have `sorry` proofs; their docstrings
carry the corresponding complete natural-language proof steps of this DAG node.
The five auxiliary declarations only package the given inputs and asserted outputs,
or abbreviate a composite of existing forgetful functors. They are owned by this node,
listed in `lean.declarations`, and do not construct new fundamental groups, fibres,
quotients, pullbacks, coproducts, or limits. No data definition uses `sorry` or a choice
from a postponed existence theorem. No new definition node or dependency repair is needed.

Hypotheses and input objects, clause by clause:

- Schemes and scheme morphisms: `X : Scheme.{u}` and `⟶`, Mathlib's actual schemes.
- Nonempty connected base: `[ConnectedSpace X]`; its `toNonempty` field includes
  nonemptiness, so the empty scheme is excluded precisely as in the node.
- Quasi-compact and quasi-separated base: `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]`. The latter is equivalent to `QuasiSeparated` of the
  terminal structure map, by `quasiSeparated_iff_quasiSeparatedSpace`.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `x : Spec (.of Ω) ⟶ X`, the recorded inline geometric-point convention.
- Fundamental group with profinite topology and its left actions on finite fibres:
  `G : ProfiniteGrp.{u}`, `[∀ Y, MulAction G ((FiniteEtale.fiber x).obj Y)]`, and
  `[IsFundamentalGroup (FiniteEtale.fiber x) G]`. This is the required small model
  of the fibre-functor automorphism group with evaluation topology; the existing
  `toAutContinuousMulEquiv` identifies it with that group. This follows the standing
  FUNDAMENTAL GROUP size convention, rather than forcing the large literal automorphism
  group into the scheme universe. The FLC fibre functor and finite-etale realization
  are the existing dependency interfaces, not new copies.
- Finite étale covers and all base morphisms between them: `X.FiniteEtale` and its
  existing full subcategory morphisms. `finiteEtaleOver` is just
  `ObjectProperty.ι _ ⋙ MorphismProperty.Over.forget _ _ X`.
- Every open normal subgroup: `OpenNormalSubgroup G`, including the whole group.
  `PointedCosetSystem.covers` is a functor from that poset to `X.FiniteEtale`.
- Connected stages: `PointedCosetSystem.connected N`.
- The fibre identification with `(G/N,N)`: `label N : (G ⧸ N.toSubgroup) ≃ ...`.
  `label_smul N a b` renders equivariance for every representative `b`, and the
  marked point is `label N 1`. Quotient surjectivity means no coset is omitted.
- Pointed transitions for each `M ≤ N`: `transition h a` says their fibre maps send
  the label of `aM` to that of `aN`. The functor supplies identities and composition;
  these are the same pointed transitions of the node.
- Compatible universes and small indexing systems: the explicit universe `u` puts
  schemes, the geometric field, the profinite model, cosets, finite fibres and the
  open-normal index poset in compatible sizes. The covers category is allowed its
  correct larger object universe. This is the recorded size convention, not an
  independent index universe or an assumption equating distinct site universes.
- A given limit over `X`: `PointedCosetLimit.cone` is a cone in `Over X` on the
  given cover diagram followed by `finiteEtaleOver X`, and `isLimit : IsLimit cone`.
  No canonical or specially constructed limit is substituted for the given one.
- Compatible marked point `t`: `point`, `point_base`, and `point_leg N` say
  `t ≫ (T → X) = x` and `t ≫ p_N = y_N`.
- Connected total limit: `PointedCosetLimit.connected : ConnectedSpace cone.pt.left`.

Conclusions in `exists_pointedLimitSplitting`, clause by clause:

- The simultaneous maps `f_s` for every finite cover `Y` and every geometric-fibre
  element `s` are `PointedLimitSplitting.sectionMap Y s`. They are morphisms in
  `Over X`, so being over `X` is part of their type.
- The value `f_s(t)=s` is `section_point`; uniqueness among ALL `X`-maps with that
  value is `section_unique`, not uniqueness merely among chosen section families.
- The splitting map has summands `pullback.lift (𝟙 T) (sectionMap Y s).left ...`.
  `splitting` asserts `Nonempty (IsColimit (Cofan.mk (pullback (T → X) (Y → X)) ...))`.
  This says exactly that these graph maps make the fibre product the coproduct of
  copies of `T`, equivalently that the canonical arrow from the coproduct is an
  isomorphism. It is the coproduct universal property recorded by the dependency,
  and uses the actual scheme pullback and the actual graph maps. In particular,
  it includes the empty fibre and the empty coproduct.
- An `N` acting trivially on `E` is rendered as
  `∀ (n : N.toSubgroup) (s : (FiniteEtale.fiber x).obj Y), (n : G) • s = s`.
  This quantifies every such subgroup; none is selected and assumed special.
- The finite-stage map is `finiteStage Y N k s`, an actual finite-etale-category
  morphism. Its fibre formula `aN ↦ a s` is `finiteStage_formula`, for every `a : G`.
  `finiteStage_unique` says this formula uniquely specifies the finite-stage map.
- Factorization `f_s = f_(s,N) p_N` is `factor` (Lean compositions read left to right).
- Compatibility with every refinement is `refinement` for all `M ≤ N` and the two
  proofs of trivial action. Independence of `N` follows directly from `factor`:
  every such composite equals the SAME `sectionMap Y s`; no index-dependent choice
  of the final maps is made. Proof irrelevance also removes dependence on `k`.
- Naturality for every finite-etale `X`-map is `natural`, using the existing
  `FiniteEtale.fiber.map b` on labels.
- The automorphisms `d_g` are `deck : G → Aut L.cone.pt`, hence over `X`.
  Their projection normalization is `deck_leg`, with label `S.label N (mk g)`.
  `deck_unique` says the equations uniquely specify each automorphism.
- `f_s d_g = f_(g s)` is `section_deck`.
- `d_1 = 1` is `deck_one`. The noncommutative right-action convention is `deck_mul`:
  `(deck g).hom ≫ (deck h).hom = (deck (g * h)).hom`, i.e. `d_h ∘ d_g = d_(g h)`.
  Thus evaluation on scheme points gives the stated right action, with the required
  normalization by the left finite-fibre monodromy, not its inverse convention.

Pointed naturality and functoriality:

- `exists_unique_pointedLimitComparison` quantifies another base `X'`, with the same
  three base hypotheses, a geometric point `x'`, its profinite fundamental-group model,
  another arbitrary system `S'` and connected pointed limit `L'`. The target geometric
  point is written literally `x' ≫ f`, following the recorded Stacks 0BND (3) interface
  for a pointed morphism; arbitrary equality presentations can be rewritten to it.
- `PointedLimitComparison` stores `F`, its equation over `f`, and `t' ≫ F = t`.
  The theorem asserts existence and equality with EVERY other pointed comparison;
  uniqueness is not limited to maps satisfying the later equivariance clauses.
- The fibre bijection is the recorded `FiniteEtale.pullbackFiberIso f x'`.
  The displayed comparison formula uses its inverse component on `s`, the primed
  `sectionMap` into `(FiniteEtale.pullback f).obj Y`, and the actual projection
  `Limits.pullback.fst Y.obj.hom f`. This is the node's `q_Y f'_(tau^-1(s))`.
- Equivariance uses precisely
  `FiniteEtale.fundamentalGroupMap (FiniteEtale.pullbackFiberIso f x') G' G`.
  Its continuity is the existing `continuous_fundamentalGroupMap`. The equation is
  `(C'.deck h).hom.left ≫ F.hom = F.hom ≫ (C₀.deck (f_* h)).hom.left`, i.e.
  `F ∘ d'_h = d_(f_* h) ∘ F`. No surjectivity assumption is imposed.
- `pointedLimitComparison_id` says every pointed endomorphism of this given limit
  over the identity is the identity, so it applies to the unique comparison.
- `pointedLimitComparison_comp` uses three independent given systems and limits,
  pointed base morphisms `f,g`, and pointed comparisons `F,H,K` over `f,g,f≫g`.
  It states `F ≫ H = K`, the required composition identity, without assuming
  equality of the three choices of systems or chosen limits.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`: `Scheme.flcFiber`; its
  reexported finite-etale realization is `Scheme.FiniteEtale.fiber` in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `Limits.pullback`, its projections, and `pullback.lift` (available for schemes).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (includes nonemptiness).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline
  as prescribed, not a second point type. The recorded `Scheme.SpecToEquivOfField`
  was also read; no conversion from geometric morphisms to residue-field pairs is needed.
- `Mathlib.CategoryTheory.MorphismProperty.Comma`: `MorphismProperty.Over`,
  `MorphismProperty.Over.forget`; the existing `Scheme.FiniteEtale` specialization
  and its pullback are used rather than copied.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and
  `quasiSeparated_iff_quasiSeparatedSpace` (scheme condition written on the space).
- `def-weil-size-convention` has its existing metatheoretic convention record;
  explicit universe binders render it, with no replacement mathematical definition.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `Cofan.mk`, and
  `CategoryTheory.Limits.IsColimit`, the recorded finite-coproduct universal property.
- Proof dependency `thm-galois-fundamental`: plain import of its recorded
  `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`, with
  `FiniteEtale.exists_fiber_flc_equivalence` and the existing `equivalenceContAction`.
- Proof dependency `lem-galois-pi1-functoriality`: existing
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction`, read through
  `pullbackFiberIso`, its explicit projection formula, `fundamentalGroupMap`,
  `fundamentalGroupMap_smul`, and `continuous_fundamentalGroupMap`. It is a public
  import because the new comparison statement itself uses these constructions.

Sources and searches:

- Read `literature/stacks-project/pione.tex`, Theorem fundamental-group, Tag 0BND
  (1), (3), including its proof; read all seven live node proof steps and the Q86
  review. The node is a generic lemma below the unit, not the unit statement.
- `msearch.py ... leanfinder`: query “A connected pointed inverse limit of finite
  etale Galois covers splits every finite etale cover and has a functorial right
  deck action”. Eight hits: abstract `PointedGaloisObject`, connected Galois
  objects, pretransitivity and `IsFundamentalGroup (Aut F)`; no full scheme statement.
- `msearch.py ... loogle`: query `"FiniteEtale", "fiber"`. Seven hits, all
  `CommAlgCat.FiniteEtale` fibre constructions and equivalences for separably closed
  fields; none states arbitrary scheme-limit splitting or pointed naturality.
- `msearch.py ... grep`: query
  `finiteSplit|bijective_fiber|PointedGalois|UniversalCover`. Nineteen Mathlib hits:
  abstract pointed Galois/prorepresentability, group classifying-space universal
  covers, and totally split algebras. None states the node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the same concepts found
  `UniversalCoverConstruction.lean` and `PointedLimitCech.lean`; both were read.
  `bijective_fiber`, `transport`, `map`, `finiteSplitMap`, `rightDeck`, and
  `PointedLimitCechCoordinates` concern the particular `UniversalCover.cover x`,
  and do not state this lemma for a given arbitrary coset system and connected limit.
  Replacing the input limit with that construction would drop a hypothesis case.
- Exact item-id grep in `lean/WeilConjectures` and `lean/Sheaf`: no hit.
- Exact new declaration-name search in Mathlib, upstream-name inventory,
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declarations with these names.
  No duplicate construction of the canonical universal cover is introduced.

Edge cases checked before stating:

- Empty fibre: section and finite-stage families have empty domain, trivial-action
  condition is vacuous for every subgroup, and the graph cofan is the empty
  coproduct. The conclusion correctly makes the pullback initial.
- Trivial fundamental group: the sole quotient is the singleton and deck equations
  give the identity; no nontriviality or positive-cardinality binder is present.
- Nontrivial noncommutative group: explicitly read the composition convention on
  the fibre formula; `deck_mul` is the right action, not the reversed multiplication.
- The whole subgroup and identity refinement are included; quotient representative
  formulas cover all cosets. Two killing subgroups are compared by their intersection
  in the docstring proof, while `factor` states independence for every one.
- A non-surjective induced fundamental-group map, including a geometric base point,
  is admitted in the comparison statement. Pullback covers need not be connected.
- The limit itself need not be finite étale, noetherian, or the chosen canonical
  universal cover. Only its specified connectedness and limit property are required.
- Three different choices of systems/limits are admitted in the composition clause.

No statement correction, disputed statement, abandoned dependency, or new DAG node.
The only initial elaboration issue was an omitted explicit target-fibre action binder
in the comparison interface; it was added, retaining both independent group actions.
The resulting file compiled cleanly through `scompile.py`, both as a sandbox module
and with its intended library module name (5.9 s and 9.1 s in that run).

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
