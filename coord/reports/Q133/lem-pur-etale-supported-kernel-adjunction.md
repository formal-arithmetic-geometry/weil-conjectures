## Worker report

Item: `lem-pur-etale-supported-kernel-adjunction`, group Q133, stage 2.
The delivery adds `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction` with two
concrete definitions and one theorem whose proof is `sorry`. The item's statement,
statement dependencies and proof plan are unchanged. No dependency repair or new
DAG node is needed: the two helper definitions are precisely the constructions
introduced in this item's own statement, recorded in `lean.declarations`.

Source read: `literature/stacks-project/etale-cohomology.tex`, the supported-sheaf
paragraph immediately before `lemma-sections-with-support-acyclic` (Tag 09XQ), the
lemma's proof and its Hom identity, and
`proposition-closed-immersion-pushforward` (Tag 04CA), especially part (2) and its
proof using the canonical unit on supported sheaves. These have no quasi-compactness,
finite-coefficient, torsion or constructibility assumption in the abelian etale case.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Arbitrary schemes Z, O, X are `{Z O X : Scheme.{u}}`, with u explicitly declared.
  A closed immersion i and open immersion j are `(i : Z ⟶ X) (j : O ⟶ X)` with
  `[IsClosedImmersion i] [IsOpenImmersion j]`. The complementary-image condition is
  `hcompl : IsCompl (Set.range i.base) (Set.range j.base)`. For these immersions this
  says exactly that O is the complementary open subscheme, up to its given open
  immersion, and does not choose a different closed scheme structure.
- Abelian sheaves on the small etale site are
  `Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and the same expression for Z/O.
  This is exactly the recorded coefficient-universe convention. The existing site,
  sheaf and abelian instances supply the categories and kernels; there is no extra
  instance hypothesis in the statement.
- The direct images are the dependency's `Etale.lowerStar AddCommGrpCat.{u + 1}`;
  the inverse images are `Etale.upperStar AddCommGrpCat.{u + 1}`. Both are the actual
  small-etale constructions in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `supportedKernel j` is
  `kernel (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit` in the functor
  category. Kernels are equalizers against zero, and functor-category limits are
  computed pointwise. Thus evaluation at F gives precisely a kernel of the specified
  unit `F ⟶ j_*j⁻¹F`, with its inclusion and kernel-induced action on morphisms.
  `Limits.evaluation_preservesLimit` and `Limits.limitObjIsoLimitCompEvaluation`
  in Mathlib's `Limits.FunctorCategory.Basic` express this evaluation explicitly.
  This uses the existing general kernel definition, not a new sheaf-kernel model.
- `supportedClosedInverseImage i j` is the concrete composite
  `supportedKernel j ⋙ upperStar AddCommGrpCat.{u + 1} i`, so its value is exactly
  `i⁻¹P_Z(F)` and its morphism action is inverse image of the induced kernel map.
- The canonical comparison, including its naturality, is the single natural
  transformation `Functor.whiskerLeft (supportedKernel j)
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit`. Its component at F
  is the closed adjunction unit at P_Z(F), with target `i_*i⁻¹P_Z(F)`.
  `IsIso` of this natural transformation asserts precisely that this particular
  comparison is a natural isomorphism. No arbitrary objectwise isomorphism replaces it.
- Exactness of the specified i_* is rendered as both
  `PreservesFiniteLimits (lowerStar AddCommGrpCat.{u + 1} i)` and
  `PreservesFiniteColimits (lowerStar AddCommGrpCat.{u + 1} i)`.
  In the abelian categories, with the existing additive direct-image functor,
  this is the usual exactness assertion.
- The final clause is
  `Nonempty (lowerStar AddCommGrpCat.{u + 1} i ⊣ supportedClosedInverseImage i j)`.
  An `Adjunction` contains Hom equivalences for every G and F, natural in both
  variables. This says exactly that i_* is left adjoint to the constructed i^!₀;
  it is stronger than separate bare cardinality or bijectivity assertions only
  in requiring the naturality that the node already explicitly requires.

Dependency declarations used, with full source signatures/docstrings inspected:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjectivity on stalks).
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (locally ringed-space open immersion).
- `Mathlib.CategoryTheory.Sites.Sheaf` and
  `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `CategoryTheory.Sheaf`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`. The latter is the actual chosen adjunction,
  including both units used here. The former is evaluated by base change and
  the latter is Kan extension followed by sheafification.
- `Mathlib.CategoryTheory.Sites.Abelian`:
  `CategoryTheory.sheafIsAbelian`, the recorded Mathlib match for
  `def-pur-abelian-sheaf-kernel`; the kernel itself is
  `CategoryTheory.Limits.kernel` from `Limits.Shapes.Kernels`.
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`:
  the existing pointwise limit construction, evaluation preservation and comparison.

Proof-dependency imports are retained as the stage-3 plan:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: a closed immersion is finite.
- `WeilConjectures.SixFunctors.Finite.Exact`:
  `Etale.preservesFiniteColimits_lowerStar_of_isFinite`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`:
  `Etale.upperStar_abelian_exact`.
- `Sheaf.AlgebraicGeometry.OpenImmersionRestriction`:
  `Etale.openImmersion_restriction_leray`, its first, underived counit clause.
- `Sheaf.Paper.InverseImageStalkGerm`:
  `AlgebraicGeometry.inverseImage_stalk_germ`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.isIso_of_isIso_sheafFiber_map`.
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`:
  `Etale.lowerStar_closedImmersion_fullyFaithful_leftInverse_essImage`.
- `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion`:
  `Etale.fullyFaithfulLowerStar` and
  `Etale.isIso_upperStarLowerStarAdjunction_counit`.

The two older DAG records naming
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact` and
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm` have corresponding published
side modules at the `Sheaf` paths listed above; their actual source declarations
were read there. The construction uses the same declaration names and does not
restate either theorem or alter either dependency record.

Edge cases checked mathematically before writing:

- Z = X, O empty: the support kernel is the whole sheaf and the adjunction is the
  expected identity adjunction (up to the fixed inverse/direct-image identifications).
- Z empty, O = X: the open unit is an isomorphism, so its kernel is zero; the
  right adjoint takes values in the zero abelian sheaf category on the empty scheme.
- X empty: both preceding descriptions agree; no nonemptiness is assumed.
- Zero sheaves give zero kernels and the expected singleton Hom sets.
- Nonreduced closed subschemes and non-quasi-compact open complements remain allowed.
  The etale essential-image theorem 04CA applies; no pro-etale or finite-ring
  hypothesis was imported into the statement.
- There is no characteristic, finiteness, boundedness or injectivity restriction
  on F or G. The explicit u+1 coefficient universe is the dependency convention,
  with no equation imposed between independent universes.

Searches for an existing statement/construction:

1. `msearch.py ... leanfinder` query:
   "For a closed immersion the kernel of restriction to the complementary open in
   abelian etale sheaves is right adjoint to direct image".
   Eight results, led by `Scheme.kerAdjunction` and `Scheme.Modules.restrictAdjunction`;
   these concern ideals or structure-sheaf modules, not abelian etale support.
2. `msearch.py ... loogle` query:
   `CategoryTheory.Limits.kernel, CategoryTheory.Adjunction`: zero hits.
3. `msearch.py ... grep` query:
   `sectionsWithSupport|supportedKernel|supportKernel|closed.*[Aa]djunction`,
   Mathlib subdirectory `CategoryTheory`: eleven unrelated monoidal-closed hits.
4. `msearch.py ... leansearch` query:
   "The direct image along a closed immersion on the small etale site has a right
   adjoint given by a kernel". Eight ideal-sheaf or scheme-module hits, no match.
5. `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared `lean/Sheaf`
   for `sectionsWithSupport|supportedKernel|supportKernel|closed.*[Aa]djunction`:
   upstream `ProEtale.sectionsWithSupport` exists on a different site, while
   pro-etale finite-coefficient and derived etale constructions do not state this
   underived abelian etale assertion. No exact match.
6. Item-id search in the upstream source, and declaration-name searches for
   `supportedKernel`, `supportedClosedInverseImage`, `supportedKernel_closedAdjunction`
   in Mathlib, upstream, shared `lean/Sheaf`, and `dag/lean_names_upstream.json`:
   no existing declaration or node attachment.
7. DAG support-kernel search and `tools/blueprint_refs.py search 'supported kernel'`
   find `def-pur-flasque-support`, which explicitly concerns pro-etale finite module
   sheaves and the quasi-compact-complement comparison. It is not this notion.

Validation: `scompile.py Q133 lem-pur-etale-supported-kernel-adjunction <module>`
compiled the sandbox and installed-path view successfully with no errors or warnings.
The first run detected an unqualified Mathlib name; it was corrected to
`Functor.whiskerLeft`. No statement correction, disputed statement, hollow data,
additional axiom, local notation, local instance or auto-bound variable is present.
The one postponed theorem has the matching DAG node and all six natural-language
proof steps in its docstring. Both definitions contain actual Mathlib constructions.

## Second reading by Q133

This is the author's separate self-check; the dispatcher's independent maintainer
review remains the independent reading. No sub-agent was started, as instructed.
I reopened the node and final module together. The scheme binders, immersion classes
and `IsCompl` cover exactly the closed/open pair. The kernel is the actual open-unit
kernel in the existing sheaf categories, constructed naturally by the functor-category
limit. The closed inverse image uses the recorded `upperStar`. The first conjunct
is invertibility of the canonical closed-unit natural transformation, not just
existence of an unrelated isomorphism. The next two conjuncts express exactness,
and the final `Nonempty Adjunction` encodes the two-variable natural Hom bijections
for these very functors. All hypotheses and all conclusions are accounted for.
The empty and total support cases remain included. No mathematical mismatch or
node fault was found. The only elaboration fix was qualification of `whiskerLeft`;
it did not alter the intended map. No new definitions of dependency notions or
additional postponed helper theorems were introduced.
