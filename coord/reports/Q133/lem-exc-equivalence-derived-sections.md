## Worker report

The module `Sheaf.CategoryTheory.EquivalenceDerivedSections` states
`CategoryTheory.exists_equivalence_derivedSections`, with `sorry` as its only postponed proof.
It also constructs `CategoryTheory.InjectiveResolution.equivalenceImage` with real data:
its cocomplex is exactly `E.mapHomologicalComplex` applied to the specified cocomplex,
and its augmentation is the image of the specified augmentation, preceded by the inverse
of Mathlib's `HomologicalComplex.singleMapHomologicalComplex` identification. Injectivity
is supplied by `E.injective_obj_of_injective (I.injective n)`; the remaining structural
fields are Mathlib instances. There is no choice of an unspecified resolution or map.
This is an owning-module helper for the termwise computation, authorized by the brief's
missing-helper rule, rather than a new independent mathematical notion.

Hypotheses and clauses, checked against the unchanged node:

- The three categories are arbitrary `C : Type u₁`, `B : Type u₂`, `D : Type u₃`, with
  independent morphism universes `Category.{v₁}`, `Category.{v₂}`, `Category.{v₃}`.
  `[Abelian C] [Abelian B] [Abelian D]` renders all three abelian hypotheses.
- `[EnoughInjectives C] [EnoughInjectives B]` renders exactly the two enough-injectives
  hypotheses. Enough injectives is not imposed on D. Mathlib derives
  `HasInjectiveResolutions` from these hypotheses; it is not an additional assumption.
- `(E : C ⥤ B) [E.Additive] [E.IsEquivalence]` means the specified additive functor
  admits a quasi-inverse and natural unit and counit isomorphisms. It does not choose
  a different functor, and its exactness and preservation of injectives are inferred.
- `(S : C ⥤ D) (T : B ⥤ D) [S.Additive] [T.Additive]` renders the two additive functors.
  `[PreservesFiniteLimits S] [PreservesFiniteLimits T]` is their left exactness; for
  additive functors between abelian categories this is equivalent to kernel preservation,
  as recorded in def-sp-left-exact-additive.
- `(α : S ≅ E ⋙ T)` is the supplied arbitrary natural isomorphism, with the node's
  direction: Lean writes composition in diagrammatic order.
- `∃ c : ∀ q : ℕ, S.rightDerived q ≅ E ⋙ T.rightDerived q` gives natural isomorphisms
  in every nonnegative degree. Natural numbers encode exactly integers q ≥ 0.
- The first conjunct quantifies over every q, every X and every `I : InjectiveResolution X`.
  `I.isoRightDerivedObj S q` identifies the source with H^q(S(I)).
  `(I.equivalenceImage E).isoRightDerivedObj T q` identifies the target with H^q(T(E(I))).
  The equation `c_q,X ≫ j_I.hom = i_I.hom ≫ H^q(α_I)` is exactly the prescribed
  component formula (equivalently `c_q,X = i_I.hom ≫ H^q(α_I) ≫ j_I.inv`).
  The complex map is the actual `NatTrans.mapHomologicalComplex α.hom`, whose components
  are α on the terms of I; its target is definitionally T(E(I)).
- The second conjunct is the equality of natural transformations
  `c₀.hom ≫ Functor.whiskerLeft E T.rightDerivedZeroIsoSelf.hom =
  S.rightDerivedZeroIsoSelf.hom ≫ α.hom`.
  It says the degree-zero comparison is α under the canonical R⁰S ≅ S and R⁰T ≅ T,
  not merely that some degree-zero isomorphism exists.

The module docstring cites Stacks Tag 015M, read at
`literature/stacks-project/derived.tex`, lemma-compose-derived-functors, with its proof
on F(I). Tag 05TD, lemma-left-exact-higher-derived, gives the canonical degree-zero map.
The theorem docstring contains all seven proof steps from the node, including preservation
of resolutions, the cohomology construction, morphism lifts, independence and normalization.

Dependency declarations used:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (through RightDerived).
- def-sp-enough-injectives: `CategoryTheory.EnoughInjectives`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`.
- def-sp-left-exact-additive: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`, `CategoryTheory.Limits.PreservesFiniteLimits`
  in `Mathlib.CategoryTheory.Limits.Preserves.Finite`, and `Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`.
- def-sp-injective-resolutions: `CategoryTheory.Injective` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `CategoryTheory.InjectiveResolution`
  in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
- The proof leaves use `InjectiveResolution.isoRightDerivedObj`,
  `isoRightDerivedObj_hom_naturality`, `Functor.rightDerived_map_eq`,
  `InjectiveResolution.toRightDerivedZero'` and `Functor.rightDerivedZeroIsoSelf` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`; `InjectiveResolution.desc`,
  `desc_commutes` and `of` in `Mathlib.CategoryTheory.Abelian.Injective.Resolution`;
  `Functor.preservesInjectiveObjects_of_isEquivalence` and
  `injective_obj_of_injective` in `Mathlib.CategoryTheory.Preadditive.Injective.Preserves`;
  and the preservation-of-limits/colimits instances in `Mathlib.CategoryTheory.Adjunction.Limits`.
  The three public imports supply the statement and helper and all these proof-leaf modules.
  No project dependency has an unusable recorded interface; no dependency module is required.

Edge cases: q = 0 is explicitly constrained; an arbitrary nonidentity α is retained in
that equality. With E the identity and α the identity the resolution formula gives the
identity comparison. Zero S, T or zero abelian categories give the unique zero-object
comparisons. An injective X has zero higher derived objects for q > 0, consistent with
the formula on its trivial injective resolution. The degree parameter never excludes zero,
and the six universe parameters are independent. The resolution representation is exactly
the Mathlib `InjectiveResolution` recorded by the dependency node, with ℕ-indexed complexes
encoding the zero negative degrees in the resolution proof. No statement correction or
STATEMENT-DISPUTED issue was found.

Searches were performed through the required `msearch.py Q133
lem-exc-equivalence-derived-sections` wrapper (its log is `searches.jsonl`):

- leanfinder: “Precomposition by an additive equivalence commutes with right derived functors
  computed on injective resolutions” returned the rightDerived resolution formulas and
  natural-transformation composition lemmas, not the source-equivalence comparison.
- loogle: `CategoryTheory.InjectiveResolution.isoRightDerivedObj` returned that definition,
  `rightDerived_app_eq`, `rightDerived_map_eq`, the naturality equations, and degree-zero
  computation. These are ingredients, not the full comparison.
- grep in CategoryTheory: `rightDerived.*[Ee]quiv|[Ee]quiv.*rightDerived|mapInjectiveResolution`
  returned zero hits in the wrapper's search index.
- leansearch: “An additive equivalence of abelian categories commuting with two left exact
  functors induces natural isomorphisms on right derived functors” returned
  `Functor.rightDerivedNatIso`, `leftDerivedNatIso`, `isRightDerivedFunctor_iff_of_iso`,
  resolution naturality, `mapDerivedCategorySingleFunctor`, and `rightDerived_map_eq`.
  `rightDerivedNatIso` concerns the same source and a localization-derived functor; it
  does not give this degreewise source-equivalence theorem with the two normalization clauses.
- leanfinder: “Map an injective resolution along an additive equivalence of abelian categories”
  returned `Abelian.LeftResolution.transport` (a different general functor-resolution notion),
  the chosen injective resolutions and their cohomology APIs. No transported specified
  InjectiveResolution constructor was found.
- Direct rg searches of Mathlib CategoryTheory and Algebra/Homology, upstream
  `WeilConjectures`, and side-project `lean/Sheaf` for the node id, rightDerived/equivalence,
  mapInjectiveResolution, mapEquivalence and equivalence/resolution combinations found
  no duplicate theorem or helper. Existing site-cohomology equivalence modules concern
  sheaves on specified sites, not arbitrary abelian categories. The upstream-name index
  has neither proposed declaration name. All candidates used above were read in source.

Validation: `scompile.py Q133 lem-exc-equivalence-derived-sections
.../EquivalenceDerivedSections.lean` compiled both its sandbox form and its intended library
module with no errors or warnings. The first compile exposed a typeclass search on the
whole family of injective objects; providing each term via Mathlib's explicit preservation
lemma repaired it, without adding hypotheses or increasing limits. It also exposed an
unqualified whiskering name, repaired to `Functor.whiskerLeft`.

## Second reading by Q133

A separate reading pass by the same dispatched worker checked the node and final module;
the brief assigns independent review to the maintainer and forbids starting other agents.
No independent reviewer is claimed here. The six universe parameters and the exact
C/B enough-injective hypotheses remain intact. E is the specified additive equivalence;
S and T have precisely additivity and left exactness. α has the correct direction.
The witness is a family of natural isomorphisms, the resolution formula quantifies over
every resolution and uses its literal termwise image, and the last conjunct fixes that
same family's degree-zero member to α. The helper contains actual data and existing
instance proofs. The theorem's only proof is `sorry`. No mismatch was found in this pass;
no node text, dependency or proof-plan field was changed.

Process note for the maintainer: during initial recovery inspection I mistakenly ran
read-only `git show`, `git ls-tree`, and `git log` in the shared repository despite the
brief's no-Git-command rule. They did not mutate Git or project files. I stopped direct
Git inspection and used filesystem readers and the authorized wrappers thereafter.

Dry run: the prescribed `deliver2.py Q133 lem-exc-equivalence-derived-sections --no-push`
reported `OK (dry run): commit e823ddb8db passes the preflight and compiles; nothing pushed`.
