## Worker report

`Sheaf.CategoryTheory.GrothendieckEdgeCocycle` states
`CategoryTheory.grothendieck_left_edge_cocycle`. Its sole proof is `sorry`; it adds
no definition and changes only the item's `lean` record.

Hypothesis and clause correspondence:

- The three categories have `Category`, `Abelian` and `IsGrothendieckAbelian`
  instances, each with explicitly bound object and morphism universes.
- The functors are `F : A ⥤ B`, `G : B ⥤ C`, with `F.Additive`, `G.Additive`
  and `PreservesFiniteLimits F/G`, exactly the additive left exact hypotheses.
- `hFG` uses `GrothendieckComposablePair.SendsInjectivesToAcyclics`, the
  recorded definition of F sending injectives to G-acyclic objects.
- `X : A` and `I : InjectiveResolution X` are the object and its given resolution.
  `HasDerivedCategory A/B/C` supplies the existing edge-map implementation's
  derived-category infrastructure; it is not a mathematical restriction.
- The two natural derived-functor identifications are explicitly the canonical
  `I.isoRightDerivedObj (F ⋙ G) n` and `I.isoRightDerivedObj F n`.
- The first conjunct quantifies every `n : ℕ`. The morphism `c` has source
  `G.obj` of the cycles of `F(I)` and target the cycles of `GF(I)`.
  Its inclusion equation fixes the canonical comparison. Left exactness makes
  this comparison an isomorphism, so this is the node's identification of
  cocycles with G of the kernel, written in the opposite direction.
- The second equation first passes from those cycles to `H^n(GF(I))`, then
  through the canonical resolution identification to the derived composite,
  applies the recorded left edge, and finally identifies its target with
  `G(H^n(F(I)))`. The result equals G applied to `homologyπ n`, the quotient
  from the kernel to cohomology. Since `c` is an isomorphism and `homologyπ`
  is epimorphic, this specifies exactly the induced cohomology morphism.
- The second conjunct gives `HF`, a decreasing filtration on each abutment.
  Its steps are fixed as the canonical spectral-object image filtration,
  transported through `grothendieckSpectralObjectHBotTopIso`; they are not an
  arbitrary finite filtration. `IsFinite`, `IsExhaustive`, `IsSeparated` render
  precisely all three stated properties. The construction is the filtration
  identified with the double-complex filtration by the model dependency.
- The last conjunct assumes vanishing for all `p q : ℕ` with `0 < p` and
  concludes `IsIso` of the recorded left edge in every `n : ℕ`.
  The invocation of exact-couple collapse is proof content, recorded step by
  step in the docstring rather than imposed as an additional hypothesis.

Dependencies read and used:

- `Sheaf.CategoryTheory.GrothendieckComposablePair`:
  `GrothendieckComposablePair`, `.SendsInjectivesToAcyclics`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic/Resolution`:
  `Injective`, `InjectiveResolution` (resolution complex and augmentation).
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `Functor.rightDerived`, `InjectiveResolution.isoRightDerivedObj`,
  `Functor.rightDerivedZeroIsoSelf`; the well-definedness node's mathlib_match
  directly provides the canonical identifications.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` and
  `Mathlib.CategoryTheory.Limits.Preserves.Finite`:
  `Functor.Additive`, `PreservesFiniteLimits`.
- `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`:
  `Functor.grothendieckLeftEdgeMap`, `grothendieckSpectralObject`,
  `grothendieckSpectralObjectHBotTopIso`, and its image filtration.
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`:
  `exists_grothendieck_spectralSequence_cartanEilenberg`.
- `Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel`:
  `grothendieckSSDoubleComplexModel`, fixing the filtration and edge comparison.
- `Sheaf.CategoryTheory.EdgeCollapse`, `ExactCouple`, `ExactCoupleConvergence`:
  `BigradedExactCouple.edge_collapse`, `BigradedExactCouple`, `ConvergesTo`.
  These are the proof route; their signatures and docstrings were read, and
  they are named in the theorem's proof docstring. They need no unused imports.
- `Sheaf.CategoryTheory.Filtration`: `DecreasingFiltration` and its three
  predicates, already supplied through the model's imports.

Edge cases: n = 0 is included, with Mathlib's degree-zero cycles and quotient
rather than an n-1 expression. Zero objects and zero functors are permitted.
No boundedness stronger than an injective resolution is assumed. The vanishing
hypothesis allows q = 0, and restricts only p to positive degrees. Universes
are independent for the categories, with no restriction to concrete categories.

Searches (actual tool outputs logged in searches.jsonl):

- msearch leanfinder, `Grothendieck spectral sequence left edge map cocycle quotient kernel cohomology`:
  eight unrelated HomComplex and group-cohomology cocycle declarations; no match.
- msearch loogle, `ShortComplex.homologyπ, Functor`: zero hits; remote Loogle
  did not recognize `ShortComplex.homologyπ`. No inference of absence from this
  name lookup alone.
- msearch grep, `grothendieck.*[Ee]dge|cycles.*[Cc]omparison`: zero hits in Mathlib.
- Local rg in Mathlib for `homologyπ`, `iCycles`, `homologyMap` and
  `isoRightDerivedObj` found the exact reusable cycles/quotient/resolution APIs.
- Local rg for `grothendieck.*[Ee]dge|lem-pc-grothendieck-edge-cocycle` in
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found the
  general edge map and the model/construction statements, not this cocycle
  identification. A source grep for the item id found no occurrence.

Source checked: the local Stacks source is absent on this machine, so opened
https://stacks.math.columbia.edu/tag/015N directly. Its short proof invokes
Cartan--Eilenberg and the second spectral sequence of Tag 015K; it does not
itself print the cocycle formula attributed to it by the node's source note.
The formula follows the stated construction, as expanded in the node's proof.
This attribution imprecision does not require changing the mathematical statement.
No statement correction or STATEMENT-DISPUTED flag is needed.

Validation: server scompile accepted the final module with no errors or warnings.

## Second reading by G1

I independently read the node statement, its source place (Stacks Project,
`derived.tex`, Lemma 015N / tag 015N), and
`lean/Sheaf/CategoryTheory/GrothendieckEdgeCocycle.lean`. The source introduces
left exact additive functors `F : A ⥤ B` and `G : B ⥤ C` between Grothendieck
abelian categories, assumes that `F` sends injectives to `G`-acyclics, chooses
`X` and an injective resolution `I`, and has three conclusion parts.

* The category objects and instances in Lean are `{A : Type uA}`, `{B : Type
  uB}`, `{C : Type uC}` with independent category and object universes,
  `[Category]`, `[Abelian]`, and `[IsGrothendieckAbelian]`; the three
  `[HasDerivedCategory]` instances are the derived-functor infrastructure.
  `F`, `G`, their `[Additive]` and `[PreservesFiniteLimits]` instances, and
  `hFG : (⟨F,G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics`
  render exactly the hypotheses, with no extra finiteness or boundedness
  assumption. `X : A` and `I : InjectiveResolution X` render the chosen object
  and resolution.
* For each `n : ℕ`, Lean's existential `c` has source
  `G.obj ((F.mapHomologicalComplex ... I.cocomplex).cycles n)` and target the
  cycles of `(F ⋙ G).mapHomologicalComplex ... I.cocomplex`. Its first equation
  `c ≫ iCycles = G.map iCycles` is precisely the left-exact cocycle
  identification. Its second equation composes `c` with `homologyπ`, the
  inverse of `I.isoRightDerivedObj (F ⋙ G)`, the recorded
  `grothendieckLeftEdgeMap`, and `G.map (I.isoRightDerivedObj F n).hom`, and
  equates that composite with `G.map homologyπ`; this is exactly the node's
  cocycle-to-cohomology quotient description under the stated derived
  identifications. Quantifier order and every clause agree.
* The existential `HF : ∀ n, DecreasingFiltration
  (((F ⋙ G).rightDerived n).obj X)` is the node's filtration on each
  abutment. The step equation transports the canonical spectral-object image
  filtration through `grothendieckSpectralObjectHBotTopIso`, and the final
  conjunction states `IsFinite`, `IsExhaustive`, and `IsSeparated`, exactly the
  three filtration properties in the node; it is not an arbitrary filtration.
* The final implication quantifies `p q : ℕ`, assumes `0 < p` and vanishing
  `IsZero ((G.rightDerived p).obj ((F.rightDerived q).obj X))`, and concludes
  `IsIso` of the recorded left edge for every `n : ℕ`. This matches the
  positive-column collapse clause without adding hypotheses.

Edge cases were checked: `n = 0` is included by `ℕ` and uses the degree-zero
cycles and quotient; zero objects and zero functors satisfy the same typed
form; the empty-index issue does not arise because all index types are the
natural numbers already present in the source construction; no characteristic,
Noetherian, concrete-category, or universe restriction was introduced. The
independent universes preserve the generality of the node.

For the one-definition rule I searched the source checkout and Mathlib with
`rg` for `grothendieck_left_edge_cocycle`, edge/cocycle variants,
`homologyπ`, and `isoRightDerivedObj`, and used the recorded LeanFinder/Loogle
searches in `searches.jsonl`. Only the abstract edge-map and reusable
homological-complex APIs exist; no declaration states this cocycle theorem.
The dependency declarations were opened: the composable-pair structure,
Mathlib's `InjectiveResolution`, the right-derived resolution isomorphisms,
the Grothendieck spectral-sequence edge map, its double-complex model, and the
exact-couple collapse/convergence declarations all supply the notions used.
No dependency module was missing or unusable, and no second definition was
written.

The module already matched the node exactly and compiled cleanly with
`scompile.py`; I found no mismatch to repair. The theorem remains a statement
only (`sorry` proof), and all declaration/module docstrings name the Stacks
source and `(blueprint: lem-pc-grothendieck-edge-cocycle)`.
