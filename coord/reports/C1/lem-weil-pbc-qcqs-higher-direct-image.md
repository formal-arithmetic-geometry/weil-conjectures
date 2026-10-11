## Worker report

The module `Sheaf.AlgebraicGeometry.QcqsHigherDirectImage` states
`AlgebraicGeometry.Etale.qcqs_higherDirectImage`, with proof `sorry`. It states the whole
node, combining its abelian-sheaf clause and its bounded-below derived clause. It defines
no new notion. The node copy changes only `lean`.

Hypotheses and clauses, with their Lean renderings:

- Schemes and the morphism `u : U → V`: `{U V : Scheme.{u}} (f : U ⟶ V)`.
- Quasi-compactness and quasi-separatedness: `[QuasiCompact f] [QuasiSeparated f]`.
  These are exactly the morphism properties collected by the conventions node.
- An arbitrary étale abelian sheaf on U:
  `∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}` in the first conjunct.
  In particular this is genuinely the abelian-sheaf category, without replacing it by
  modules over an arbitrary coefficient ring.
- Every nonnegative degree: `∀ q : ℕ`, coerced to `(q : ℤ)` for derived homology.
- The small étale site of V: `V.smallEtaleTopology`, with category `V.Etale`.
- The presheaf `W ↦ H^q(W ×_V U,F|)`: the composite
  `(MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
   ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q).obj F`.
  The derived inclusion applies the ordinary inclusion to an injective resolution and
  takes presheaf cohomology. Kernels, cokernels and hence cohomology in this presheaf
  category are objectwise. Thus its value at an étale U-object Z is `H^q(I(Z))`.
  Étale restriction preserves injectives and K-injectives, so at
  `Z = W ×_V U` this is exactly cohomology of the restricted coefficients. Its maps
  are the maps of the same section complex, not arbitrary independently chosen maps.
  The chosen pullback functor uses `U ×_V W`, canonically symmetric to the displayed
  `W ×_V U`, with projection to U.
- Sheafification: `(presheafToSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj`.
- The sheaf `R^q u_*F`: homology in degree `(q : ℤ)` of
  `(rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
   ((DerivedCategory.Plus.singleFunctor _ 0).obj F)`.
  `Nonempty (... ≅ ...)` expresses that it is the sheaf associated to the specified
  cohomology presheaf, as in the landed abelian-sheaf theorem described below.
- The additional assertion on D⁺: the second conjunct quantifies over
  `K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Applying the description to a K-injective resolution: quantify over a cochain complex
  I of the same abelian sheaves, with `I.IsKInjective` and
  `Nonempty (DerivedCategory.Q.obj I ≅ K.obj)`. These identify a K-injective
  representative of K in the localization. They do not restrict which K are allowed:
  every K has such a representative by the recorded resolution-existence node.
  For a resolution map from any representative of K, localization gives precisely this
  isomorphism. Conversely an isomorphism to a K-injective representative lifts to a
  homotopy-class map and is a quasi-isomorphism. There is no extra hypothesis that
  I is strictly bounded below or termwise injective.
- The computation `Ru_*K = u_*I`: the first conclusion of the second conjunct is
  `Nonempty (DerivedCategory.Q.obj ((lowerStar ... f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I ≅ ((rightDerivedLowerStarPlus ... f).obj K).obj)`.
  Both sides lie in the same unbounded derived category; `.obj` forgets the full
  subcategory membership of the bounded-below result, not any underlying data.
- In each degree, the same description: `∀ q : ℤ` and an isomorphism from
  sheafification of base-change precomposition of
  `(((sheafToPresheaf ...).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology q`
  to `H^q(Ru_*K)`. The presheaf homology is sectionwise, so at W it is
  `H^q(I(W ×_V U))`, exactly the resolution description in the node, and equals
  `H^q(W ×_V U,K|)` since étale restriction of I is K-injective.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a convention record, without a
  declaration of its own. Its relevant constituents are Mathlib
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.QuasiCompact`
  (`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`), and
  `AlgebraicGeometry.QuasiSeparated`
  (`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`). The latter is quasi-compactness
  of the diagonal, not quasi-separatedness of an unrelated absolute scheme.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the direct image is literally
  precomposition by base change on sections. Its recorded derived declaration
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` is defined in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (not in the underived
  Defs module named by the old mixed record). This actual defining module is imported.
  This is only a module-location discrepancy, not an unusable notion; no replacement
  dependency module is necessary.
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology` in
  `Mathlib.AlgebraicGeometry.Sites.Etale` and `AlgebraicGeometry.Scheme.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Its objects and covers have the node's meaning.
- `def-weil-pbc-sheafification` is a Mathlib dependency, needing no new lean record:
  `CategoryTheory.presheafToSheaf` in `Mathlib.CategoryTheory.Sites.Sheafification`,
  left adjoint by `CategoryTheory.sheafificationAdjunction`.
- `def-weil-pbc-kinjective-resolutions`: read
  `Sheaf.AlgebraicGeometry.KInjectiveResolutions` and its
  `CochainComplex.IsKInjectiveResolution`, which names `QuasiIso f ∧ I.IsKInjective`
  for module-valued complexes. The generic `CochainComplex.IsKInjective` recorded beside
  that abbreviation is used directly for abelian sheaves; it is defined in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` and requires every map from an
  acyclic complex to be null-homotopic. Shifting gives the equivalent Hom-complex
  definition in the node. No private copy or coefficient specialization is defined.
- `def-weil-pbc-derived-categories`: read
  `Sheaf.AlgebraicGeometry.DerivedCategories`; its mixed record explicitly includes
  Mathlib `DerivedCategory`, `DerivedCategory.Plus` and
  `DerivedCategory.homologyFunctor`, including the abelian-sheaf interpretation.
  `DerivedCategory.Plus.homologyFunctor` is its restriction to D⁺, in
  `Mathlib.Algebra.Homology.DerivedCategory.Plus`. `DerivedCategory.Q` is the existing
  localization in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.

The imports also supply the existing abelian/Grothendieck structures and resolution
instances; `Mathlib.Algebra.Category.Grp.AB` is needed for the Grothendieck property of
AddCommGrpCat. All universes and variables are bound explicitly; there are no let binders.

Edge cases checked before writing: q=0 gives the ordinary pushforward (the presheaf is
already a sheaf); identity morphisms give local vanishing in positive degree, even though
cohomology over an individual étale object need not vanish. Zero sheaves/complexes give
zero presheaves and cohomology. Empty schemes are permitted. Negative degrees of an
arbitrary bounded-below K are covered by `q : ℤ` in the second clause. Representatives
with acyclic unbounded tails remain allowed. The site/coefficient universes follow the
source's `Scheme.{u}`, `AddCommGrpCat.{u+1}` convention.

Searches (also saved by msearch in searches.jsonl):

- LeanFinder: “Higher direct image is the sheafification of the cohomology presheaf of
  an abelian sheaf on the small etale site”: eight hits, including
  `Sheaf.cohomologyPresheafFunctor`, `Sheaf.cohomologyPresheaf`, `Sheaf.H` and
  sheafification constructions, no full statement of this node.
- Loogle: `Sheaf.H, presheafToSheaf`: zero hits, unknown identifier `Sheaf.H`.
- LeanSearch: “Higher direct images are sheafifications of cohomology presheaves and
  are computed by K-injective resolutions”: unavailable, Internal Server Error.
  No mathematical no-match verdict is inferred from this service failure.
- msearch Mathlib grep: `higherDirectImagePresheaf|cohomologyPresheaf|homologyPresheaf`:
  ten hits in SheafCohomology, with Ext-based cohomology presheaves; no direct-image theorem.
- Source rg for `higherDirectImagePresheafToSheaf` and the item id:
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage` contains
  `AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf` and its singleFunctor
  version. Read the full definitions, signatures and docstrings: these take sheaves of
  arbitrary Λ-modules and therefore do not literally have this node's abelian-sheaf
  objects. They do not replace the statement by a coefficient specialization here.
- Project rg for `higherDirectImagePresheaf|higher_direct_image` and
  `cohomologyPresheaf|higherDirectImage|KInjective.*lowerStar` found
  `AlgebraicGeometry.higherDirectImageSheafifiedPresheaf` in
  `Sheaf.Paper.HigherDirectImageSheafifiedPresheaf`. Read it in full: it gives exactly
  the first clause, for every morphism, using objectwise derived evaluation. It does
  not include the node's additional clause for arbitrary K in D⁺. The new theorem
  states the combined node, and uses the same existing inclusion/rightDerived
  constructions, without defining a second cohomology notion. Deriving the inclusion
  into the presheaf category takes cohomology objectwise and is equivalent to the
  evaluation-by-evaluation formula of that existing theorem.
- Checked `qcqs_higherDirectImage` in the source, project and upstream name index:
  no existing declaration with this name.

Source verification: local literature contains only citation/index files, not the cited
blueprint text. The DAG supplies the blueprint statement and five proof steps. Opened
[Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8), which gives both the sheaf and
complex clauses, [072W](https://stacks.math.columbia.edu/tag/072W), its sheaf proof,
[08BJ](https://stacks.math.columbia.edu/tag/08BJ), preservation of K-injectives by right
adjoints to exact functors, and [00WJ](https://stacks.math.columbia.edu/tag/00WJ), exact
sheafification. The qcqs assumptions are retained as in the node, although the Stacks
formula holds for arbitrary morphisms. No statement correction or disputed statement.

Validation: scompile on the server completed with exit code 0, no errors and no warnings
(2.4 seconds). Only the expected stage-2 theorem `sorry` remains. The module has maximum
line length 100. The second reading is left to the independent reader as instructed.


## Second reading by C1

Independent second reader: I read the sandbox node and module, all six statement
dependency nodes and the actual declarations listed below. Verdict: the Lean says
exactly the node's two clauses; no mathematical mismatch was found and no Lean or node
change was needed. This reading adds the independent audit to the report only.

Object/hypothesis/conclusion checklist (in the node's order):

1. Schemes U and V and their morphism u: `{U V : Scheme.{u}} (f : U ⟶ V)`.
   Verdict: the same schemes and morphism, without a base field or ring assumption.
2. The morphism is quasi-compact and quasi-separated:
   `[QuasiCompact f] [QuasiSeparated f]`. Verdict: exactly the node's hypotheses,
   applied to f, not to identities or absolute schemes. The conventions node collects
   these Mathlib properties and introduces no additional notion.
3. An arbitrary étale abelian sheaf F on U:
   `∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   Verdict: genuine abelian sheaves, not module sheaves for a chosen coefficient ring.
4. Every q >= 0: `(q : ℕ)`, and `(q : ℤ)` in derived homology.
   Verdict: covers precisely the nonnegative degrees, including zero.
5. R^q u_* F: `DerivedCategory.Plus.homologyFunctor` in degree q applied to
   `rightDerivedLowerStarPlus ... f` of `Plus.singleFunctor ... 0` applied to F.
   Verdict: exactly the cohomology sheaf of the derived direct image of F[0].
6. The presheaf on the small étale site of V:
   `(MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
   ((sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q).obj F`.
   Verdict: evaluates at W to the cohomology of the section complex over the
   base-changed étale object, with restriction along base-changed arrows.
   I read Mathlib `Functor.rightDerivedToHomotopyCategory` and `Functor.rightDerived`:
   they apply the functor to an injective resolution and take homology. Evaluation
   of presheaves is exact and homology is objectwise, so this is the same presheaf
   as the derived-evaluation formulation in the landed
   `AlgebraicGeometry.higherDirectImageSheafifiedPresheaf`. Étale localization has
   exact extension by zero as left adjoint, so the restricted injective resolution
   computes H^q(W ×_V U,F|). The source functor chooses U ×_V W with its projection
   to U; fibre-product symmetry gives the displayed W ×_V U, also on arrows.
7. The associated sheaf: `(presheafToSheaf V.smallEtaleTopology
   AddCommGrpCat.{u + 1}).obj` of that presheaf, isomorphic to item 5 via `Nonempty`.
   Verdict: exactly being the sheafification, with no pointwise-only substitute.
8. The bounded-below derived clause: `∀ K : DerivedCategory.Plus
   (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})`.
   Verdict: all of D⁺, including complexes bounded below in negative degrees.
9. Apply the description to a K-injective resolution: quantify over
   `I : CochainComplex (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ`,
   with `I.IsKInjective` and `Nonempty (DerivedCategory.Q.obj I ≅ K.obj)`.
   Verdict: precisely K-injective representatives of K. Given a representative L
   of K, full faithfulness of localization into a K-injective target lifts this
   derived isomorphism to a map L → I which is a quasi-isomorphism. Conversely a
   resolution yields this derived isomorphism. Thus no stronger hypothesis such as
   strict boundedness or termwise injectivity is imposed, and the condition is
   nonvacuous for every K by the resolution-existence node.
10. Ru_*K is computed by u_*I: the first `Nonempty` of the second conjunct compares
    `DerivedCategory.Q.obj (((lowerStar ... f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I)` with the underlying object of Ru_*K.
    Verdict: the asserted derived computation in the same ambient derived category.
11. Every degree has the same sheafification description: `∀ q : ℤ`, with
    `.homology q` of the presheaf complex obtained from I, precomposition by
    base change, sheafification, and an isomorphism to H^q(Ru_*K).
    Verdict: all integer degrees, sectionwise H^q(I(W ×_V U)), hence the restricted
    hypercohomology of K. Quantifier order matches the resolution computation:
    for every K and every valid I, both the complex formula and all degrees hold.

Dependency inspection: I opened `Etale.lowerStar` and its sections/maps formulas
in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; it is the continuous
sheaf pushforward by the base-change functor. I opened `rightDerivedLowerStarPlus`
in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; it is literally
`lowerStar.rightDerivedFunctorPlus`. The recorded dependency module omits this latter
location but its recorded declaration is usable and the delivery imports its actual
module. I opened Mathlib `Scheme.smallEtaleTopology` and its jointly-surjective-cover
characterization, and `presheafToSheaf` with `sheafificationAdjunction`; these match the
site and associated-sheaf dependencies. I read `Sheaf.AlgebraicGeometry.DerivedCategories`
and `Sheaf.AlgebraicGeometry.KInjectiveResolutions`: the former explicitly records the
abelian-sheaf category and Mathlib D⁺/homology; the latter uses the existing generic
`CochainComplex.IsKInjective` and `QuasiIso`. I read the Mathlib K-injective class:
null-homotopy of every map from an acyclic complex, equivalent to acyclicity of the
Hom complex by shifting. Using that recorded generic declaration directly on abelian
sheaves needs no private module-valued resolution definition. No dependency module or
new definition node is in this delivery, and none is missing.

Source reading: the cited blueprint text is absent from this machine's literature
checkout. I used the node's full statement and five-step proof and independently read
Stacks .tex from the project's upstream raw sources: `etale-cohomology.tex`,
`lemma-higher-direct-images` (03Q8), and the opening of its Colimits section;
`derived.tex`, `lemma-adjoint-preserve-K-injectives` (08BJ); `sites.tex`,
`lemma-sheafification-exact` (00WJ). The section does not impose a standing Noetherian,
characteristic, separatedness, or coefficient-finiteness assumption on 03Q8. That lemma
allows arbitrary morphisms and even unbounded K; the node explicitly asks its qcqs,
D⁺ case and the Lean keeps exactly that case. 08BJ assumes an exact additive left
adjoint, as used for étale restriction in proof step 2; 00WJ supplies the exact
sheafification used in step 4. All five node proof steps are present in the statement
docstring. No statement correction exists, so no corrected-statement citer checks apply.

Edge cases: q=0 is ordinary pushforward since the inclusion is left exact; positive
cohomology for an identity morphism sheafifies to zero, even when sections over a
particular étale object have nonzero cohomology. The zero sheaf and zero complex are
allowed. Empty U or V are not excluded. Empty covering/index families are handled by
the existing small étale topology, with no nonempty-index hypothesis added. Negative
q for K is included; I can have unbounded acyclic tails. There is no characteristic
restriction, field, Noetherian hypothesis, or finiteness of coefficients. The universe
u is arbitrary; the site and abelian values use the existing six-functor convention
`Scheme.{u}` and `AddCommGrpCat.{u+1}`, without an independent smaller test universe.
All variables and universes in the signature are explicitly bound.

Independent searches (different queries from the writer):

- msearch LeanFinder: "Derived pushforward of an etale abelian sheaf computed by
  sections of a K injective complex and sheafification": eight hits, including
  `Sheaf.cohomologyPresheafFunctor`, `Sheaf.H`, and `Sheaf.cohomologyPresheaf`.
  These are cohomology constructions, not this two-clause pushforward statement.
- msearch Loogle: `CochainComplex.IsKInjective`: twelve hits, including the generic
  class and its shift and bounded-below-injective results; confirms the existing
  generic notion rather than requiring a new definition.
- msearch grep: `sheafification.*cohomology|cohomology.*sheafification|IsKInjective.*lowerStar`:
  no hits. Direct rg across Mathlib, WeilConjectures and lean/Sheaf with
  `pushforward.*homology|homology.*pushforward|rightDerived.*sheafToPresheaf` and the
  delivered and landed theorem names found the landed first-clause theorem and
  unrelated pushforward cohomology statements, not a full abelian-sheaf theorem.
- Independently opened the source `Etale.higherDirectImagePresheaf`,
  `isIso_higherDirectImagePresheafToSheaf`, and its singleFunctor version: they use
  `ModuleCat Λ` inputs, not the node's abelian sheaves. Opened the landed
  `AlgebraicGeometry.higherDirectImageSheafifiedPresheaf`: it only has F[0] inputs.
  Neither replaces the full item. The module defines no new cohomology notion.

H5/H6/H8/H9: no definitions, axioms, or proved statements are introduced; the one
theorem has exactly `by sorry`. Header, source docstrings, namespace, imports and
100-character line width satisfy the conventions. I checked that `lean.statement`
is character-for-character the theorem signature up to `:=`, not just normalized.
Independent scompile completed in 2.5 seconds with exit code 0 and no warnings/errors.
No mismatch or mathematical repair was necessary; only this second-reading report
was appended.

## Reviewer fix (R-qhd1430, stage 2)

Two changes to the statement, both from reading the node clause by clause:

1. The second conjunct asserted `Nonempty (Q.obj (u_* I) ≅ Ru_* K)` in addition to the
   degreewise description. The node does not say this; it is the formula of the definition
   node def-weil-pbc-direct-image (and step 1 of the proof). Removed: the second conjunct now
   says only that every degree H^q(Ru_*K) is the sheafified sectionwise cohomology of a
   K-injective representative.
2. The first conjunct wrote the presheaf W ↦ H^q(W ×_V U, F|) as the right derived functor of
   the inclusion `sheafToPresheaf`, a second encoding of the cohomology presheaf of the landed
   `AlgebraicGeometry.higherDirectImageSheafifiedPresheaf` (lem-weil-pbc-higher-direct-image-
   sheafified-presheaf, F1), which states this same clause for every morphism with right derived
   evaluation and `NatTrans.rightDerived` restriction maps. The first conjunct now uses that
   landed presheaf verbatim, so one form serves both nodes.

Recompiled with `SHEAF_GROUP=L tools/lean_file.sh` on a sandbox copy: clean.
