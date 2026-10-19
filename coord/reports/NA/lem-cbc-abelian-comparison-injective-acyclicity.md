## Worker report

Existing statement attachment; no new module, definition, proof, or dependency node.
The declaration is
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`
in `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`, lines 107–110.
Its complete signature and docstring were read in both the source checkout and the
published framework source. Its proof is already `sorry`; recording it does not
claim that stage 3 is finished. The lean.statement is its source signature verbatim.

Apply the declaration with `A := AddCommGrpCat.{u + 1}`. This specialization is exactly
the node's statement. The generalized coefficient parameter supplies the existing
statement, rather than requiring a duplicate theorem about abelian groups.
`scompile.py` successfully checked this specialization with all coefficient instances
inferred, against both the local overlay and the server library (2.3 seconds each).
The scratch probe is outside lean/ and is not a delivered module.

Hypothesis and clause correspondence:

- Any scheme X is `(X : Scheme.{u})`; no affineness or other scheme property occurs.
- The small etale site is `X.smallEtaleTopology`; the small pro-etale site is
  `Scheme.ProEt.topology X`, on `X.ProEt`.
- The comparison morphism is represented by `ProEtale.comparisonUpperStar A X`
  and `ProEtale.comparisonLowerStar A X`. Reading their definitions in
  `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` shows the former is
  `Functor.sheafPullbackConstruction.sheafPullback (toProEt X) A ...` (left Kan
  extension followed by sheafification), and the latter is
  `(toProEt X).sheafPushforwardContinuous A ...` (restriction). Thus these are
  the node's canonical inverse and direct images, with no arbitrarily chosen map.
- An abelian etale sheaf I is `(I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
  Its injectivity hypothesis is `[Injective I]`, in this very sheaf category.
- Its comparison inverse image is `(ProEtale.comparisonUpperStar A X).obj I`.
- The conclusion is `(ProEtale.comparisonLowerStar A X).rightAcyclic` of that object.
  `CategoryTheory.Functor.rightAcyclic`, read in
  `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`, is definitionally
  `∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj M)`.
  Every positive degree is uniquely a successor, so this is precisely the displayed
  vanishing for q > 0, without an unintended degree-zero conclusion.
- `CategoryTheory.Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived` uses injective resolutions and homology;
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` identifies it with the
  degree-q homology of F applied to any injective resolution. The resolution is in
  the input category, here abelian pro-etale sheaves, exactly as required.
- There is no torsion, constructibility, finite ring, quasi-compactness, or finite
  cover hypothesis. A is the category of all abelian groups, not finite modules.
  Its Grothendieck abelian instance is available, not an extra condition on I or X.

Dependencies read and used through the existing statement's definitions:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- def-weil-pbc-etale-site: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and `Scheme.Etale`.
- def-weil-pbc-proetale-site: read
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `Scheme.proEtaleDerivedCategory`;
  its underlying site is the existing `Scheme.ProEt.topology`. The module category
  and derived category parts are not needed for this abelian-sheaf statement.
- def-weil-pbc-site-comparison-morphism: read
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `Scheme.proEtaleSiteComparison`.
  The generic coefficient definitions in Comparison.Defs use exactly the same
  `toProEt` inclusion, constructed pullback, and continuous pushforward.
- def-weil-pbc-sites-and-cohomology: read
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Precoverage.IsSiteForCoverings`;
  its other clauses retain existing Mathlib `Sheaf` and derived evaluation.
  Here `Sheaf` and right-derived functors render the abelian-sheaf clauses directly.
- def-sp-injective-resolutions: `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective`; and the recorded `InjectiveResolution` declaration
  in `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
- def-sp-left-exact-additive: its mathlib_match is `Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`; the adjacent resolution formula
  `InjectiveResolution.isoRightDerivedObj` was read as well.

Source check: read Stacks proetale.tex, lemma-relative-comparison (099V), its first
proof paragraph, and the affine-vanishing reference (099U). The source proves exactly
the positive-degree vanishing for inverse images of arbitrary injective abelian sheaves.
The node's five-step proof explains sheafified higher direct images, restriction of
injectives to affine etale objects, compatibility of comparison with localization,
affine vanishing, and the affine covering/sheafification argument. No source-based
correction is needed. The pre-existing theorem's docstring states this acyclicity
clause explicitly; its proof remains open upstream.

Edge cases: X may be empty or nonaffine; I may be zero or have unrestricted torsion.
No binder excludes these. Degree 1 is included (q = 0 in rightAcyclic); degree 0 is
excluded as required. The u+1 abelian-group universe is the common larger universe
of the small sites and adds no equality between site object and morphism universes.

Searches (2026-10-15):

- msearch.py leanfinder: "The inverse image of an injective abelian etale sheaf is
  acyclic for the proetale comparison direct image" returned eight unrelated
  locally-injective-morphism or K-injective-complex hits; no Mathlib match.
- msearch.py loogle: `"rightAcyclic", "Sheaf"` returned zero hits.
- msearch.py leansearch: "Higher comparison direct images of inverse images of
  injective etale abelian sheaves vanish" was unavailable, Internal Server Error.
- msearch.py grep: `comparison.*[Aa]cyclic|[Aa]cyclic.*comparison` returned zero hits.
- rg over source WeilConjectures for the node id and
  `rightAcyclic_comparisonUpperStar_obj_of_injective` found the exact candidate in
  Comparison/LowerStarAcyclic.lean:107 and its consumers in Derived/Comparison.lean
  and the same module. The node's lean_candidates already identified it.
- rg over lean/Sheaf for those patterns found no duplicate. Read the framework's
  Comparison/LowerStarAcyclic.lean and Comparison/Defs.lean to confirm the candidate.

No statement dispute, missing object, or node fault found. Only the item's lean
record changes. The required dry run is performed after preparing this report;
the independent second reader supplies their own reading and delivers.

## Second reading by NA

Independent second reading, 2026-10-15. I opened the complete node, its seven
statement-dependency records, the actual recorded dependency modules, Stacks
proetale.tex at lemma-relative-comparison (099V) and lemma-affine-vanishing
(099U), and the existing declaration and its ambient variables. The source's
099V first paragraph assumes only a scheme and an injective abelian etale sheaf;
affineness occurs only for the local test objects in its proof.

Object/hypothesis/conclusion inventory and itemwise verdicts:

1. Any scheme X: `(X : Scheme.{u})`, using Mathlib's `Scheme`, the declaration
   recorded by def-pc-scheme. Exact; no geometric property instance is present.
2. Its small etale and pro-etale sites: `X.smallEtaleTopology` on `X.Etale` and
   `Scheme.ProEt.topology X` on `X.ProEt`. Exact. I read the small-etale definition
   in Mathlib and `proEtaleDerivedCategory` in the recorded dependency module;
   the latter uses this same pro-etale topology. Its constant module sheaf and
   derived category are additional components of that dependency, not coefficient
   restrictions on the present node.
3. The canonical comparison geometric morphism and its abelian functors:
   `ProEtale.comparisonUpperStar A X` and `comparisonLowerStar A X`. Exact with
   `A := AddCommGrpCat.{u + 1}`. In Comparison.Defs the first is the constructed
   sheaf pullback (left Kan extension followed by sheafification) along `toProEt X`,
   and the second is continuous restriction along that very inclusion. I opened
   `Scheme.proEtaleSiteComparison`: its sets functors use the identical inclusion
   and constructions. The finite-ring module adjunction in that dependency does
   not impose a finite-ring hypothesis on this existing generic abelian theorem.
4. Every abelian etale sheaf I: `(I : Sheaf X.smallEtaleTopology A)` specialized
   to `AddCommGrpCat.{u + 1}`. Exact; not a finite-module or constructible category.
   The generic ambient binders `[Category.{u+1} A] [Abelian A]
   [IsGrothendieckAbelian.{u+1} A]` all synthesize for this specialization, as the
   independent wrapper check confirmed. They add no hypothesis on X or I.
5. I injective in that category: `[Injective I]`. Exact. I read the recorded
   Mathlib class: it extends maps into I across every monomorphism. It does not
   assert injectivity of an underlying morphism or of a pro-etale input object.
6. The object whose acyclicity is asserted is precisely
   `(comparisonUpperStar A X).obj I`. Exact; no independently chosen lift.
7. Every higher direct image vanishes: the conclusion is
   `(comparisonLowerStar A X).rightAcyclic ((comparisonUpperStar A X).obj I)`.
   Exact. I read `Functor.rightAcyclic` in its defining module: it is
   `forall q : Nat, IsZero ((F.rightDerived (q + 1)).obj M)`. Thus it quantifies
   over exactly the positive degrees, after X and I, and has no degree-zero clause.
8. The stipulated injective-resolution meaning of R^q: Mathlib's
   `Functor.rightDerived` is homology of the right-derived homotopy functor;
   `InjectiveResolution.isoRightDerivedObj` explicitly identifies its value with
   homology of F applied to an arbitrary injective resolution. I read these
   signatures and the `InjectiveResolution` fields. Here the resolution category
   is `Sheaf (ProEt.topology X) AddCommGrpCat`, as the node requires. Exact.
9. No affine, torsion, constructibility or finite-ring hypothesis: none occurs
   in the specialized signature. Exact. The sites-and-cohomology dependency's
   current module supplies its covering-axiom component; its retained Mathlib
   `Sheaf` and derived functors supply the abelian-sheaf and cohomology components
   used here. No replacement site or private notion is introduced.

Edge cases: the empty scheme and zero sheaf are included by the binders; there
is no nonemptiness or affineness assumption. Arbitrary torsion and nontorsion
abelian groups are included. Positive degree 1 is the q=0 instance of rightAcyclic;
degree 0 is deliberately excluded. Characteristic and index sets impose no
conditions here. The scheme universe u is arbitrary; abelian groups live in the
larger common site universe u+1, in accordance with the dependency's size
convention. No equality of site object and morphism universes is imposed.

Independent searches used different wording from the worker: msearch leanfinder
"An injective etale sheaf pulled back to the pro etale topology has zero higher
direct images" returned eight nonmatching hits (locally injective morphisms,
etale morphisms and the generic vanishing on injective input objects).
msearch loogle `"rightAcyclic"` returned zero hits. msearch leansearch
"The pullback of an injective abelian sheaf from the etale site is acyclic for
proetale comparison pushforward" was unavailable (Internal Server Error), with
no negative verdict inferred. rg over Mathlib CategoryTheory, upstream
WeilConjectures and the project's lean/Sheaf for comparison/acyclic variants,
then for the exact declaration name, found this upstream theorem and its users;
no distinct project or Mathlib statement supplants it. I opened its actual
source at LowerStarAcyclic.lean:107-110, including the generic ambient binders.

No mathematical mismatch was found and no Lean or node field was changed.
The existing theorem's signature is verbatim the node's lean.statement. Its
upstream docstring explicitly states this acyclicity, but uses the older blueprint
identifier and does not reproduce this node's five-step proof. As an existing
attachment it is read-only and no new module/docstring is delivered; this is not
a reason to duplicate the theorem. The node and worker report retain the full
source and proof plan. No new definitions, dependency modules, hollow data,
proofs or statement corrections are introduced by this delivery.

I independently ran scompile.py on scratch/ExistingCheck.lean: both the private
local overlay and server check passed (2.3 seconds each), with no warnings or
errors. The output exposes all ambient binders and checks the AddCommGrpCat
specialization with its instances inferred. All variables and universes are bound.
