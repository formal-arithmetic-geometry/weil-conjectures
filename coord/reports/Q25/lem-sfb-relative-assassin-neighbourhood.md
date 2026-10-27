## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeAssassinNeighbourhood` states
`AlgebraicGeometry.Scheme.Modules.relativeAssassin_neighbourhood`, with its sole
postponed proof `by sorry`. It states the existing node without a statement correction,
new definitions, new nodes, or dependency repairs. Its docstring carries all eight
steps of the node's proof and their dependencies. The source is Stacks Project,
more-morphisms.tex, Tag 05F1, `lemma-relative-assassin-in-neighbourhood`, read in full
at lines 6841–6905. The source's relative-assassin conclusion is equivalently the
node's associated-point conclusion on the specified fibre.

Hypothesis and clause correspondence:

- The schemes and morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite type is `[LocallyOfFiniteType f]`; there is no quasi-compactness,
  flatness, finite-presentation, or Noetherian hypothesis.
- The quasi-coherent module of finite type is `(F : X.Modules)` and
  `(hF : F.IsQuasiCoherentFiniteType)`. The recorded dependency defines this as
  `SheafOfModules.IsQuasicoherent F ∧ SheafOfModules.IsFiniteType F`, not coherence.
- The relative associated point is `(ξ : X) (hξ : ξ ∈ relativeAssassin f F)`.
  This uses exact element-annihilator association, not Mathlib's general radical
  associated-prime notion.
- The closed subset is `⟨closure ({ξ} : Set X), isClosed_closure⟩`.
  Its reduced induced closed scheme is the actual
  `(Scheme.IdealSheafData.vanishingIdeal ...).subscheme`; the existing
  `reduced_induced_closed_subscheme` identifies this construction as reduced, with
  precisely that image and the required uniqueness. No arbitrary closed scheme
  or additional reducedness assumption replaces it.
- The existential `W : (...).subscheme.Opens` is an arbitrary open of that scheme;
  `W.carrier.Nonempty` supplies exactly nonemptiness. `W.ι` is its open immersion.
- The composite `W.ι ≫ (...).subschemeι ≫ f` is its map to S.
  `∀ s : S, s ∈ Set.range (...) → ...` restricts the conclusion to exactly s in f(W).
- `(...).fiber s` is W_s, without taking its reduction. The set C ranges over all
  subsets of this fibre; `C ∈ irreducibleComponents (...)` selects all components.
  `∀ y : (...).fiber s, IsGenericPoint y C → ...` selects every generic point of
  every such component, with no choice of a preferred component or generic point.
- `pullback.map _ _ f (S.fromSpecResidueField s)` with arrows
  `W.ι ≫ (...).subschemeι`, `𝟙 _`, `𝟙 S` is exactly W_s → X_s induced by W → Z → X.
  Its two commutativity proofs simplify only category identities and associativity;
  they add no mathematical assumption. This map is constructed, not existential data.
- `associatedPoints ((tensorPullback (f.fiberι s)).obj F)` is precisely
  Ass_{X_s}(F_s), with F_s the tensor pullback specified by the node.

Statement dependencies read and used (module, declaration):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (only its local notion is required).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `AlgebraicGeometry.Scheme.Modules.relativeAssassin` and `associatedPoints`.
  Their stalk definition uses `RingTheory.annihilatorAssociatedPrimes`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, the recorded Mathlib
  match of def-weil-irreducible-components, which needs no Lean record repair.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `fiberι`;
  the definition is the pullback along `S.fromSpecResidueField s`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, exposing the existing
  `vanishingIdeal`, `subscheme`, and `subschemeι` construction.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  opens use the canonical `W.ι` instance rather than an additional hypothesis.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  `Scheme.Modules.tensorPullbackSectionAdjunction` and public upstream
  `Scheme.Modules.tensorPullback`; the statement uses this actual tensor functor.

All recorded statement dependency signatures and docstrings were opened. Existing
proof dependency modules are imported privately: QuasicoherentFiniteTypeAffine,
AffineChartBaseChangeIso, TensorPullbackTilde, AffineAssociatedPointsPrimes,
FibreAssociatedPrimesModuleRing, and AnnihilatorAssociatedPrimes; Mathlib imports
supply the recorded finite-type/Noetherian, flat torsion-free, tensor injectivity,
and minimal-associated-prime leaves. The proof prerequisite
`lem-trf-algebra-module-simultaneous-generic-flatness` has no recorded module at
this checkout, so no import is invented for it; it remains named in the proof
plan and is not needed to type the statement. There is no import cycle.

Edge cases checked before writing:

- Empty X or zero F admits no relative associated ξ, so the implication has no
  spurious forced nonempty open in these cases.
- The closure of ξ is nonempty and irreducible even when X or S is nonreduced;
  the chosen Z is reduced by the canonical construction, while W_s need not be.
- No generic-point uniqueness or irreducibility assumption is placed on W_s:
  the conclusion handles all its components. Empty fibres outside f(W) impose
  nothing; no component is selected by a nonempty choice.
- A field base and a closed or vertical relative associated point are allowed.
  ξ need not dominate S. Neither S nor X need be Noetherian or flat over anything.
- The universe u is explicit and arbitrary, with the project's same-universe
  scheme convention. `autoImplicit` and `relaxedAutoImplicit` are both false.
- W is not required to be affine, dense by an extra condition, or to contain ξ;
  the proof's affine principal-open choice is stronger than what is stated.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`: “A relative associated point of a finite type quasi
  coherent sheaf has a nonempty open in its closure whose fibre generic points
  are associated”. Eight hits: scheme sobriety, stalk localization/spreading, and
  `IsAffineOpen.primeIdealOf_genericPoint`; none states this theorem.
- `msearch.py ... loogle '"associatedPrimes"'`: twelve associated-prime definitions,
  nonemptiness and algebraic transport results, no scheme neighbourhood theorem.
- `msearch.py ... grep 'relativeAssassin|associatedPoints' AlgebraicGeometry/`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: “relative associated point closure open fibre
  generic points finite type module”. Eight generic-point topology hits, no match.
- `rg` on `lean/WeilConjectures` for relative-assassin/associated-point
  neighbourhood names and the exact node id: no exact statement or node-id hit.
- `rg` on `lean/Sheaf` found the canonical RelativeAssassin definition, affine
  association dictionary, generic-fibre containment spreading (different result),
  and FlatRelativeAssociatedSpecialization/FlatAssociatedEquidimensional (require
  flatness and have different conclusions). None duplicates the node's theorem.
- `rg` on `dag/lean_names_upstream.json` for the proposed name and assassin
  neighbourhood names: no name collision. The existing source construction was
  used directly; no new notion search or new definition node is needed.

Validation: the first server compile identified an unresolved carrier coercion
in `(W : Set _).Nonempty`; using the explicit existing `W.carrier.Nonempty` fixed
it. `scompile.py Q25 lem-sfb-relative-assassin-neighbourhood <module>` then compiled
both sandbox and destination-module forms cleanly (1.6 s and 1.5 s), without errors
or unexpected warnings. No STATEMENT-DISPUTED flag or node fault was found.


## Second reading by Q25

Independent clause-by-clause reading (maintainer reviewer, 2026-10-24), against the node and
Stacks more-morphisms.tex Tag 05F1, lines 6841–6850.

| Node clause | Lean | Verdict |
|---|---|---|
| f : X → S morphism of schemes | `{X S : Scheme.{u}} (f : X ⟶ S)` | exact; one arbitrary universe |
| f locally of finite type | `[LocallyOfFiniteType f]` | exact; no qc, flatness or Noetherian hypothesis |
| F quasi-coherent of finite type | `(F : X.Modules) (hF : F.IsQuasiCoherentFiniteType)` (= IsQuasicoherent ∧ IsFiniteType) | exact |
| ξ ∈ Ass_{X/S}(F) | `hξ : ξ ∈ relativeAssassin f F` (def-trf-relative-assassin record) | exact |
| Z = closure of {ξ} with its reduced induced structure | `(vanishingIdeal ⟨closure {ξ}, isClosed_closure⟩).subscheme`, the construction that the stmt_dep reduced_induced_closed_subscheme characterizes | exact |
| ∃ nonempty open W ⊆ Z | `∃ W : (…).subscheme.Opens, W.carrier.Nonempty` | exact |
| s ∈ f(W) | `s ∈ Set.range (W.ι ≫ subschemeι ≫ f)` | exact |
| every generic point of every irreducible component of W_s | `∀ C ∈ irreducibleComponents ((…).fiber s), ∀ y, IsGenericPoint y C` | exact; nothing is chosen |
| image in X_s via W → Z → X | `pullback.map _ _ f (S.fromSpecResidueField s) (W.ι ≫ subschemeι) (𝟙 _) (𝟙 S)` into `f.fiber s = pullback f (S.fromSpecResidueField s)` | canonical map |
| ∈ Ass_{X_s}(F_s), F_s the tensor pullback | `∈ associatedPoints ((tensorPullback (f.fiberι s)).obj F)` | exact; the same `associatedPoints`/`tensorPullback` that define `relativeAssassin` |

Source comparison: 05F1 concludes that the generic points of V_s lie in Ass_{X/S}(F). By
def-trf-relative-assassin, x ∈ Ass_{X/S}(F) exactly when its canonical point of X_{f(x)} lies in
Ass_{X_{f(x)}}(F_{f(x)}). The image of y in X has f-image s, so the node's fibre formulation says
the same thing.

Edge cases: empty X or F = 0 leaves no ξ, so the statement is vacuous; a field base; a closed or
vertical ξ; a nonreduced fibre W_s, which is not reduced in the Lean; s outside f(W), which is
excluded by the range hypothesis. All are covered as in the node.

Records: lean.statement equals the file signature verbatim; there is no statement_change, there
are no new nodes or dependency records, and the stmt_deps are unchanged from the stage-1 node. The
theorem stmt_dep lem-weil-pbc-reduced-induced-closed-subscheme was already in the base node and
gives the Mathlib vanishingIdeal/subscheme construction used here (advisory only). The module has
exactly one `sorry`, plus source and blueprint docstrings and the 8-step proof plan. It contains no
hollow definition.

Searches: the node's logged leanfinder, leansearch, loogle and grep searches, and `rg` on side-live
lean/Sheaf and lean/WeilConjectures for relativeAssassin_neighbourhood and relative-assassin
neighbourhood names, found no existing statement. No findings in substance.
