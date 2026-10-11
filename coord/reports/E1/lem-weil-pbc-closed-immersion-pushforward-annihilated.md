## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated` states
`AlgebraicGeometry.Scheme.Modules.closedImmersion_pushforward_annihilated` with one
`sorry` and no definitions or proved lemmas. The original node is unchanged except for
its `lean` record. No missing notion, unusable dependency, or statement fault was found.

Clause-by-clause correspondence:

- Schemes `X` and `Z`: `{X Z : Scheme.{u}}`, with explicit universe `u`.
- The morphism `i : Z → X`: `(i : Z ⟶ X)`; its closed-immersion hypothesis:
  `[IsClosedImmersion i]`.
- The defining ideal sheaf is `i.ker`. Its sections on every open `V` are rendered by
  `i.ker.idealOfOpens V`, reusing the existing upstream extension of ideal-sheaf data.
  `Scheme.Hom.ker_apply` identifies its ideals on affine opens with the kernel of `i.app`.
  The closed subscheme associated to `i.ker` is isomorphic over `X` to `Z` for a closed
  immersion (Mathlib's closed-immersion/ideal-sheaf equivalence), so the upstream
  `idealOfOpens` kernel of the associated subscheme map is the kernel of `i.app V`
  on arbitrary opens too. No privately defined ideal or annihilation predicate is used.
- Pushforward is `Scheme.Modules.pushforward i`, and pullback is the recorded
  `Scheme.Modules.tensorPullback i`, not Mathlib's abstract `Modules.pullback`.
- The canonical unit is
  `(Classical.choose (exists_tensorPullbackAdjunction i)).unit.app F`.
  The imported adjunction existence theorem specifies the unit on sections as the
  canonical tensor unit, rather than merely asserting an arbitrary adjunction exists.
- Clause (1) quantifies over every `G : Z.Modules` with `[G.IsQuasicoherent]`.
  Its first conclusion is `((pushforward i).obj G).IsQuasicoherent`.
- Its annihilation conclusion quantifies over every `V : X.Opens` and every
  `a : Γ(X, V)`, assumes `a ∈ i.ker.idealOfOpens V`, and concludes `a • s = 0`
  for every `s : Γ((pushforward i).obj G, V)`. All opens, including non-affine ones,
  occur literally in this formula.
- Clause (2) quantifies over every `F : X.Modules` with `[F.IsQuasicoherent]`.
  Its annihilation hypothesis is the same all-open formula, with `s : Γ(F, V)`.
- Its quasi-coherence conclusion is `((tensorPullback i).obj F).IsQuasicoherent`;
  its unit-isomorphism conclusion is `IsIso` of the canonical unit above in `X.Modules`.
- The final conditional clause is
  `F.IsFiniteType → ((tensorPullback i).obj F).IsFiniteType`. It does not impose
  finite type on all the modules in either preceding clause.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom`; source signature and docstrings read.
- `def-weil-closed-immersion`: its Mathlib match
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-sbc-closed-immersion-ideal-sheaf`: its Mathlib match
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, `AlgebraicGeometry.Scheme.Hom.ker`,
  and `Hom.ker_apply`; the full definitions and docstrings were read.
  For sections on arbitrary opens, reuse
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
  `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` (and its affine compatibility).
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullback`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; full functor construction read.
  Pushforward is the Mathlib `Scheme.Modules.pushforward` used there.
  The canonical unit uses `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
  `Scheme.Modules.exists_tensorPullbackAdjunction`, the named theorem of the
  recorded definition's proof dependency `lem-pc-module-pullback-adjunction`.
- `pqf-def-coherent`: read `Sheaf.AlgebraicGeometry.Coherent` and its docstring.
  It explicitly records quasi-coherence and finite type as the Mathlib predicates
  `SheafOfModules.IsQuasicoherent` (local free presentations) and
  `SheafOfModules.IsFiniteType` (local finite generators), whose source signatures
  and docstrings were read in `Quasicoherent.lean` and `Generators.lean`.
  The coherent predicate itself is not needed for this node, so its module is not imported.

Edge cases checked before writing: empty `X` or `Z` are allowed without nonemptiness
hypotheses; for empty `Z`, its ideal is the unit ideal and annihilation forces `F = 0`.
Zero modules satisfy both clauses. The identity closed immersion has zero ideal and
an invertible pullback unit. A nonreduced closed subscheme retains the actual kernel
ideal rather than its radical. No Noetherian, finite-presentation, reducedness, field,
characteristic, or finite-type hypothesis on the schemes is added. Universe `u` is
explicit and there are no index-universe restrictions or automatically bound variables.

Sources checked: the local `literature/stacks-project` checkout is absent on this machine,
so the source tags were read at the official Stacks pages:
[01QY](https://stacks.math.columbia.edu/tag/01QY),
[08KS](https://stacks.math.columbia.edu/tag/08KS),
[01BG](https://stacks.math.columbia.edu/tag/01BG), and
[01B6](https://stacks.math.columbia.edu/tag/01B6).
They supply respectively the essential image and unit, its stalk argument, and the
pullback preservation assertions. The declaration docstring carries all seven proof
steps from the node, naming the nodes to be used in stage 3.

Searches for an exact existing statement:

- `msearch.py leansearch`: "closed immersion pushforward quasi-coherent sheaf
  annihilated by ideal unit pullback isomorphism"; service unavailable (Internal Server
  Error), recorded as unavailable rather than a mathematical negative result.
- `msearch.py leanfinder`: "closed immersion pushforward quasi-coherent modules
  annihilated by ideal pullback unit isomorphism"; eight hits, including
  `restrictFunctorAdjCounitIso`, `restrictAdjunction`, and `restrictFunctor` for
  open immersions, the closed-immersion/ideal-sheaf equivalence, and pushforward
  functoriality facts; none states this node.
- `msearch.py loogle`: "AlgebraicGeometry.Scheme.Modules.pushforward,
  AlgebraicGeometry.IsClosedImmersion"; zero hits.
- `msearch.py grep`: "IsClosedImmersion|annihilat" in `AlgebraicGeometry/Modules`;
  zero hits.
- `rg` in the source `WeilConjectures` tree for the item id and for
  `closedImmersion_pushforward_annihilated|closedImmersion.*annihilat`; no matches.
- `rg` in Mathlib and `lean/Sheaf` for those proposed declaration names; no matches.
  Concept searches in `lean/Sheaf` for `annihil`, `i.ker`, `tensorPullback i`, and
  `unit.app` found the existing fully-faithful and unit-quotient sibling statements.
  They concern respectively the counit/full faithfulness and an arbitrary-module
  quotient presentation, and do not state this node's two quasi-coherence clauses
  and finite-type conditional together. Their signatures and docstrings were read.
- `rg` of `dag/lean_names_upstream.json` for the item id and proposed declaration name:
  no match. No duplicate exact statement was found.

Validation: the final module compiled cleanly on the server with `scompile.py`, in
3.3 seconds, without errors or unexpected warnings. The statement is taken directly
from `tools/stage2_delivery.py signature`, whitespace-normalized. Independent second
reading is left to the designated next worker.

## Second reading by E1

I independently read the unit statement and its Lean declaration against the DAG node and
Stacks sources. The correspondence is exact:

- The node's objects (X,Z,i), with (i) a closed immersion, render as
  `{X Z : Scheme.{u}}`, `(i : Z ⟶ X)`, and `[IsClosedImmersion i]`.
- The ideal sheaf \(\mathcal I\) renders as `i.ker.idealOfOpens V`; this is the
  recorded ideal-sheaf construction, including arbitrary opens.
- The module operations (i_*) and (i^*) render as `(pushforward i).obj` and
  `(tensorPullback i).obj`, respectively, using the recorded pullback notion.
- Clause (1)'s universal quasi-coherent `G`, quasi-coherence of its pushforward, and
  sectionwise annihilation render in the first parenthesized universal quantifier.
- Clause (2)'s quasi-coherent `F`, sectionwise ideal-annihilation hypothesis,
  quasi-coherence of pullback, invertibility of the canonical unit, and finite-type
  implication render in the second universal quantifier. The unit is exactly
  `((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app F)`.

The Lean precedence is checked explicitly: the outer expression is
`(forall G, ...) ∧ (forall F, annihilation -> conclusions)`, matching the node's two
numbered clauses. No hypotheses or conclusion clauses are added, dropped, weakened, or
strengthened. The explicit universe `u` covers the node's unrestricted schemes.

Edge cases checked: empty schemes and empty opens are admitted; the empty closed scheme
has the unit ideal and forces annihilated modules to be zero; zero modules satisfy both
parts; the identity immersion has zero ideal and the usual pullback unit; no Noetherian,
finite-presentation, characteristic, field, reducedness, or finiteness assumptions are
introduced. There is no index type or `n` parameter.

I repeated the existing-definition searches in Mathlib, `WeilConjectures`, and
`lean/Sheaf` (including `rg` searches for the item and declaration names, LeanFinder,
Loogle, and the recorded LeanSearch query). They found no exact statement; only ideal
sheaf correspondence and open-immersion restriction results. The dependency declarations
and their signatures were opened; each supplies precisely the notion cited by the node.
No mismatch was found, so no source, node, or Lean repair was needed. The module compiles
with `scompile.py` without errors or warnings other than the permitted `sorry` declaration.
