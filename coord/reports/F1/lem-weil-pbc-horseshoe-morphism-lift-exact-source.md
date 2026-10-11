## Worker report

Item: `lem-weil-pbc-horseshoe-morphism-lift-exact-source`.
Module: `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource`.
Declaration: `CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift_exact_source`.
The module states the exact-source horseshoe comparison lemma with a single `sorry` proof;
it defines no new notion and proves nothing. Only the item's `lean` field was changed.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| An abelian category B | `{C : Type u} [Category.{v} C] [Abelian C]`, with both universes explicitly declared |
| Two short exact sequences, with six objects and four arrows | `S T : ShortComplex C`, `hS : S.ShortExact`, `hT : T.ShortExact`; `X₁`, `X₂`, `X₃`, `f`, `g` are their objects and arrows |
| Three source cochain complexes | `XA XB XC : CochainComplex C ℕ` |
| Augmentations A → XA⁰, B → XB⁰, C → XC⁰ | `sA`, `sB`, `sC` are chain maps from `(CochainComplex.single₀ C).obj S.Xᵢ`; their degree-zero components are exactly these augmentations |
| Exact augmented sequences starting with 0 → A, B, C | `[QuasiIso sA] [QuasiIso sB] [QuasiIso sC]` |
| Source short exact sequence of complexes | `i : XA ⟶ XB`, `p : XB ⟶ XC`, `hip : i ≫ p = 0`, and `hexact` requiring the evaluated short complex to be `ShortExact` for every `n : ℕ` |
| Source compatibility with the augmentations | `hi : sA ≫ i = (single₀ C).map S.f ≫ sB`; `hp : sB ≫ p = (single₀ C).map S.g ≫ sC` |
| Target injective resolutions of the primed objects | `JA : InjectiveResolution T.X₁`, `JB : InjectiveResolution T.X₂`, `JC : InjectiveResolution T.X₃` |
| Target horseshoe complex maps | `α' : JA.cocomplex ⟶ JB.cocomplex`, `β' : JB.cocomplex ⟶ JC.cocomplex`, with `hαβ'` witnessing their zero composite |
| Target horseshoe augmentation squares | `hα'`, `hβ'`, the same `single₀` equations as the dependency theorem |
| Target degreewise short exact rows | `hexact'`, for every `n : ℕ`, using `HomologicalComplex.eval` |
| Given morphism (a,b,c) of short exact sequences | `F : S ⟶ T`; its `τ₁`, `τ₂`, `τ₃` are a, b, c, and `ShortComplex.Hom` contains both commutative squares |
| Given endpoint complex maps | `φA : XA ⟶ JA.cocomplex`, `φC : XC ⟶ JC.cocomplex` |
| Endpoint augmentation compatibility | `hφA`, `hφC`, using `(single₀ C).map F.τ₁` and `(single₀ C).map F.τ₃` respectively |
| Existence of a middle complex map | `∃ φB : XB ⟶ JB.cocomplex` |
| Middle augmentation compatibility | `sB ≫ φB = (single₀ C).map F.τ₂ ≫ JB.ι` |
| Compatibility with the left row arrow | `i ≫ φB = φA ≫ α'` |
| Compatibility with the right row arrow | `φB ≫ β' = p ≫ φC` |
| Source complexes need not be injective | No `Injective` or `InjectiveResolution` binder on `XA`, `XB`, or `XC`; only their augmentations are quasi-isomorphisms |

Why the exactness rendering is equivalent: a chain map from `single₀ A` includes
`sA.f 0 ≫ XA.d 0 1 = 0`. For an ℕ-cochain complex there is no incoming differential
in degree zero, so H⁰(XA) is its degree-zero cycle object. An isomorphism
A → H⁰(XA) therefore says that sA.f 0 is monic and identifies A with ker(d⁰).
At every positive degree the source single complex has zero homology; a
quasi-isomorphism says XA has zero homology there, i.e. exactness at XAⁿ.
Conversely the displayed exact augmented sequence gives these homology isomorphisms.
The same applies to XB and XC. Mathlib's `HomologicalComplex.quasiIso_iff`,
`CochainComplex.quasiIsoAt₀_iff`, and `quasiIsoAt_iff_exactAt` express these facts.
`QuasiIso` is existing Mathlib infrastructure for augmented exactness, as also used
by the landed `HorizontalComparisonLift` module, not a new private notion.
Augmentation equations between chain maps from `single₀` are equivalent to their
specified degree-zero equations since all their other components have zero source.

Dependencies read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (read its class and docstring).
- `def-sp-injective-resolutions`: `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution` (read the whole structure,
  including cocomplex, injective, hasHomology, ι and quasiIso); the injective-object
  clause is `CategoryTheory.Injective` in `Preadditive.Injective.Basic`.
- `lem-weil-pbc-horseshoe-morphism-lift`:
  `CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift`,
  `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift` (read the full theorem and
  docstring). Its target data and chain-map augmentation equations are reused verbatim.
  This module is imported and supplies the Mathlib infrastructure transitively.
  The new theorem generalizes its source hypotheses rather than redefining horseshoes.

Edge cases checked mathematically: n = 0 is included in both degreewise exactness
hypotheses, and the source QuasiIso hypotheses force monic augmentations, so the
initial zeros are not lost. The zero objects and zero complexes are allowed.
Exact noninjective source terms remain allowed (e.g. the split constant complexes
from a short exact sequence of abelian groups with noninjective terms). No enough-
injectives assumption is introduced: the target resolutions are already given.
ℕ indexing records precisely the displayed degrees 0,1,...; target negative-degree
vanishing is encoded by the same convention as the dependency. Object and morphism
universes remain independent and unrestricted. The endpoint maps are arbitrary
compatible maps; no canonical choice, homotopy-only equality, or uniqueness is imposed.

Searches (run through msearch.py, with the actual queries in searches.jsonl):

- leanfinder: “A morphism of short exact sequences of exact augmented cochain complexes
  into injective horseshoe resolutions admits a compatible middle lift for prescribed
  endpoint maps”. Eight hits: InjectiveResolution.descFSucc, descFOne, desc,
  descHomotopyZeroZero, descHomotopyZeroOne, descFZero, CochainComplex.cm5b.fac and
  isKInjective_of_injective_aux. These treat individual comparison maps, factorizations
  or homotopies; none provides the constrained middle lift with prescribed endpoints.
- loogle: `CategoryTheory.InjectiveResolution, CategoryTheory.ShortComplex.ShortExact`.
  Zero hits.
- grep (Mathlib CategoryTheory): `horseshoe|exact.*augmented|augmented.*exact`.
  Zero hits.
- leansearch: “Lift prescribed endpoint maps from exact augmented source complexes to a
  compatible morphism of short exact sequences of injective resolutions”. Service
  unavailable (Internal Server Error); no mathematical verdict inferred.
- rg of the project's CategoryTheory sources and upstream WeilConjectures CategoryTheory
  for `horseshoe|exact.source|augmented`: the landed injective-source theorem and CE
  applications were found, but no exact-source middle-lift declaration.
- grep -rn of the upstream WeilConjectures tree for the item's id: no hits.
- rg of dag/lean_names_upstream.json for horseshoe and the proposed declaration: no hits.
- Final declaration/file-name search across Mathlib, WeilConjectures and lean/Sheaf:
  `exists_horseshoe_morphism_lift_exact_source|HorseshoeMorphismLiftExactSource`:
  no preexisting declaration found.

Source check and node fault: this machine has no literature/stacks-project checkout.
Opened https://stacks.math.columbia.edu/tag/015I and
https://stacks.math.columbia.edu/tag/013R directly. Tag 015I is CE resolution
existence and its proof constructs resolutions; it does not contain the comparison
morphism construction asserted by the item's source-place text. Tag 013R is the
acyclic-source/bounded-below-injective-target null-homotopy lemma used in proof step 3.
The statement itself is well-typed and its explicit four-step defect-correction proof
is valid, so no statement correction is needed. The module accurately attributes this
as the classical comparison argument motivated by the CE setting, with Tags 0136 and
013R as ingredients. The node's maintainer-owned source field is preserved.
No STATEMENT-DISPUTED issue found.

Validation: scompile.py on the server completed in 1.2 s, exit code 0, with no warnings.
The only postponed proof is the theorem named above. Every variable and universe is
explicitly bound, and every Lean line has at most 100 characters.

## Second reading by F1

I independently matched the node's objects, hypotheses, and conclusion against
`Sheaf/CategoryTheory/Abelian/HorseshoeMorphismLiftExactSource.lean`.

- The abelian category is rendered by `{C : Type u} [Category.{v} C] [Abelian C]`; both
  universes are explicit and unrestricted.
- The two short exact sequences and their morphism are `S T : ShortComplex C`,
  `hS`, `hT`, and `F : S ⟶ T`; this introduces exactly the six endpoint objects and
  the four sequence arrows required by the node.
- The source complexes and augmentations are `XA XB XC : CochainComplex C ℕ` and
  `sA`, `sB`, `sC` from `single₀`; `[QuasiIso sA]`, `[QuasiIso sB]`, and
  `[QuasiIso sC]` encode exactness of the displayed augmented sequences, including
  degree-zero monicity.
- The source short exact sequence is `i`, `p`, `hip`, `hexact`, with degreewise
  `ShortExact` after `HomologicalComplex.eval`; `hi` and `hp` are precisely the two
  augmentation compatibility equations. No injectivity assumptions are imposed on
  source complexes.
- The target resolutions are `JA`, `JB`, `JC : InjectiveResolution ...`; `α'`, `β'`,
  `hαβ'`, `hα'`, `hβ'`, and `hexact'` give the target horseshoe data exactly as in
  the dependency theorem.
- Endpoint maps `φA`, `φC` and equations `hφA`, `hφC` have the node's prescribed
  compatibility with `F.τ₁` and `F.τ₃`. The conclusion quantifies one `φB` and gives,
  in the same order, augmentation compatibility, the left square, and the right
  square.

No mismatch was found. The Lean statement is verbatim aligned with the node's
statement and uses the recorded dependency declarations; no repair was needed.
The source place was checked against the current Stacks pages: Tag 015I is the
Cartan--Eilenberg existence lemma and Tag 013R is the acyclic-to-bounded-below-
injective null-homotopy lemma. The node's explicit comparison statement is the
intended blueprint lemma, with the proof steps documenting the comparison argument.

Edge cases checked: `n = 0` is included by `∀ n : ℕ`; zero objects, zero maps, and
zero complexes remain admissible; empty index sets do not occur because the complexes
are indexed by all of `ℕ`; no characteristic, Noetherian, finiteness, or enough-
injectives hypothesis is added; and the independent object/morphism universes do
not restrict the abelian category. The three `QuasiIso` assumptions retain the
initial zero and degree-zero augmentation conditions.

Searches were repeated for the declaration and notion using grep/rg over Mathlib,
the upstream `WeilConjectures` tree, and project `lean/Sheaf`, plus LeanFinder,
Loogle, and the recorded LeanSearch query. No existing declaration states this
constrained middle-lift theorem; the only related declarations are the individual
comparison and horseshoe infrastructure already cited by the node. Compilation with
`scompile.py` succeeds with only the intentional theorem `sorry`.
