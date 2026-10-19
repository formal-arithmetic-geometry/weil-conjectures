## Worker report

The module `Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds` states
`SheafOfModules.ringedTensorCohomologicalBounds`, with its sole proof `sorry`.
It also defines the helper `SheafOfModules.ringedDerivedScalarExtension` by selecting
the existing universal derived-change-of-rings pair. This helper has real data from
the dependency theorem, not a data-level `sorry`. The ordinary functor in that pair
has both its objects and its maps fixed to sheaf scalar extension, and the left-derived
universal property determines the selected derived functor up to compatible isomorphism.
Its counit is invertible on K-flat representatives, as specified by the dependency.
There is no extra theorem, new DAG notion, dependency repair, or statement correction.

Hypothesis and clause mapping:

- A small site is represented by `{C : Type u} [Category.{v} C]`, its topology
  `{J : GrothendieckTopology C}`, and `[EssentiallySmall.{r} C]`. This is the
  Grothendieck-topology presentation of the recorded site notion, with no assumption
  that the site has points, all pullbacks, or a terminal object. The essentially small
  condition expresses smallness relative to the module universe from the module-category
  dependency. Both site universes and the coefficient universe remain independent.
- The map of commutative ring sheaves is `{R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)`.
  `derivedChangeRingIndependentCoefficients J R` and its S analogue forget commutativity.
  `SheafOfModules.{r}` is the exact Mathlib match of the recorded module-category node,
  definitionally the category exposed by its `CategoryTheory.ringedSiteModules` abbreviation.
- `J.HasSheafCompose`, `J.WEqualsLocallyBijective`, and `HasSheafify` are the dependency's
  size/sheafification infrastructure for these abelian categories; they impose no ring
  flatness or geometric condition. The two `HasDerivedCategory.{w}` instances select
  the unbounded derived categories at the chosen morphism size, as in the recorded
  derived-category dependency. They can be supplied by the standard localizations.
- The functor F is `ringedDerivedScalarExtension φ`, selected directly from
  `derivedChangeOfRingsIndependentCoefficients φ`. The choice uses the universal-property
  specification, rather than a mere existence of unrelated objects or maps. The bound
  assertions are invariant under the resulting uniquely compatible isomorphism.
- Every integer bound is covered by `(a : ℤ)`. Both conjuncts quantify over every
  `M : DerivedCategory (SheafOfModules ... R)`.
- Clause (a) is the first conjunct: `M.IsLE a → (F.obj M).IsLE a`. The recorded
  `DerivedCategory.isLE_iff` identifies these with vanishing of H^i for every i > a.
- Clause (b)'s initial bound is `M.IsGE a`. Its Tor hypothesis quantifies over
  `(q : ℤ)` with `a ≤ q`, and `(p : ℕ)` with `0 < p`. The expression under `IsZero` is
  `(DerivedCategory.homologyFunctor ... S (-(p : ℤ))).obj
    (F.obj (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor ... R 0).obj
        ((DerivedCategory.homologyFunctor ... R q).obj M))))`.
  This is literally H^(-p)(H^q(M)[0] tensor_R^L S), the node's definition of higher Tor.
  Positive natural p indexes exactly all higher Tor degrees. `singleFunctor ... 0`
  and `DerivedCategory.Q` give the degree-zero module in the unbounded derived category.
- The conclusion in (b) is `(F.obj M).IsGE a`; `DerivedCategory.isGE_iff` says precisely
  H^i(F(M)) = 0 for every i < a. There is no `IsLE` hypothesis in this conjunct.
- No finite generation, boundedness beyond the stated one-sided bounds, flatness of S,
  or existence of points is assumed. The ring map, modules, and derived objects are
  unrestricted apart from their specified types and the displayed cohomological assumptions.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, whose public imports retain
  `GrothendieckTopology`/`Sheaf` for the topology presentation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation for the exact Mathlib match `SheafOfModules` used here.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and the standard localization construction.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsLE`, `DerivedCategory.IsGE`,
  `DerivedCategory.isLE_iff`, and `DerivedCategory.isGE_iff`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`:
  `SheafOfModules.derivedChangeRingIndependentCoefficients` and
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, including the full
  existential signature fixing ordinary objects/maps, additivity, the universal derived
  pair, triangulatedness, and the K-flat counit computation.

All stated proof dependencies are imported. The proof docstring follows the DAG's
six steps: same-bound flat replacement; the degree-zero Tor-acyclic calculation and
shifts; induction on finite upper truncations; quasi-isomorphism from the degreewise
colimit of compatible flat truncation resolutions; K-flatness of that colimit using
exactness and tensor commutation (with signed symmetry); and vanishing below a after
scalar extension, detectable after restriction to the same underlying abelian sheaves.
The additional proof imports are BoundedFlatReplacement, BoundedAboveFlatSheafKFlat,
TruncationTriangle, HomologySequence, FlatTruncationTower, FilteredColimitsTensor,
TruncationsAndHomotopyColimits, KFlat, and BifunctorShift, with the module paths from
those nodes' records. None closes an import cycle.

Edge cases checked: the zero complex, zero modules, zero ring sheaf, identity ring map,
empty site, all integer a (including zero and negative values), and q = a are included.
There is no requirement p = 0 vanish: the Tor hypothesis expressly restricts to p > 0.
A complex unbounded below is allowed in (a); a complex unbounded above is allowed in (b).
An empty retained cohomology range means zero layers and does not add a nonemptiness
assumption. No statement fault or disputed mathematical claim was found.

Searches before writing:

- `msearch.py`, LeanFinder: “Derived extension of scalars for sheaves of rings preserves
  upper cohomological bounds and preserves lower bounds for complexes with Tor acyclic
  cohomology”. Eight hits: standard IsLE/IsGE representative facts, Sheaf.H, projective
  and injective Ext/derived-functor vanishing. No full scalar-extension bounds statement.
- `msearch.py`, Loogle: `"DerivedCategory", "tensor"`. Zero hits.
- `msearch.py`, Mathlib grep in `Algebra/Homology`:
  `Tor.*[Aa]cyclic|[Aa]cyclic.*Tor|[Ii]sGE.*tensor|tensor.*[Ii]sGE|[Ii]sLE.*tensor|tensor.*[Ii]sLE`.
  Eleven hits, in KInjective/KProjective files; no matching statement.
- `rg` in upstream WeilConjectures and side `lean/Sheaf` for cohomological bounds,
  tensor IsLE/IsGE, and derived scalar extension. Upstream FlatModel has
  `DerivedCategory.isLE_tensor`, and `isGE_tensor_of_torAmplitudeIn`; their full signatures
  were read. They concern tensor inside a fixed monoidal derived category, and the latter
  requires a uniform Tor amplitude, so neither is the two-clause scalar-extension theorem.
  Side hits contain the recorded derived-change-of-rings interface and specialized
  coefficient-reduction functors, not these bounds on a general ringed site.
- Upstream search for the exact node id returned no hit. Searches for the two chosen
  declaration names in the upstream name index, Mathlib, upstream WeilConjectures, and
  side Lean returned no existing declaration. Existing generic module categories,
  cohomology, t-structure predicates, and the scalar-extension universal construction
  are all reused.

Source passages opened: `sites-cohomology.tex`, the compatible flat-resolution tower
at `lemma-resolution-by-direct-sums-extensions-by-zero` (Tag 077J), the degreewise
K-flat-colimit argument, and `definition-derived-tor` / `definition-tor` (Tag 06YU
and the following Tor definition). These agree with the node's interpretation.

Validation: `scompile.py NW lem-weil-pbc-ringed-tensor-cohomological-bounds` compiled
both its sandbox check and its library-module check cleanly, without warnings.

## Second reading by NW

I independently read the item's node, its five statement-dependency nodes and their
recorded source signatures, and the delivered module. There is one node and one module
in this delivery; there are no new definition nodes, dependency repairs, or statement
corrections to audit. The worker's statement and definitions require no change.

Source check: sites-cohomology.tex, the Flat resolutions section, especially
lemma-bounded-flat-K-flat, lemma-colimit-K-flat, and
lemma-resolution-by-direct-sums-extensions-by-zero (Tags 06YQ, 06YR, 077J), assumes only
a ringed site. Its compatible upper-truncation resolutions and exact filtered colimits
support the node's unbounded argument. The construction immediately before
 definition-derived-tor and definition-tor (Tag 06YU and the following definition) gives
Tor_p as H^(-p) of the derived sheaf tensor product. I also read the change-of-rings
dependency's full universal-pair statement and its source/proof documentation. Neither
source adds site points, flatness of the target ring, or a second cohomological bound.
The node accurately labels the two bounds as an agent consequence rather than a
verbatim assertion of 06YU or 077J.

Object, hypothesis, and conclusion checklist (the step-1 list, matched against Lean):

- Small site C: `{C : Type u} [Category.{v} C]`,
  `{J : GrothendieckTopology C}`, and `[EssentiallySmall.{r} C]`.
  Verdict: matches. The topology presents sheaves on the site's associated
  Grothendieck topology; it introduces neither terminal objects nor global pullbacks.
  I opened `CategoryTheory.Precoverage.IsSiteForCoverings` in SiteCoveringAxioms:
  its covering axioms are not confused with a topology or a global-pullback instance.
  Smallness relative to the module universe is precisely the size convention of the
  recorded module-category node.
- Sheaves of commutative rings and their map R -> S:
  `{R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)`.
  Verdict: exact; rings are unrestricted, including zero rings and positive
  characteristic. `derivedChangeRingIndependentCoefficients J R` and its S analogue
  forget commutativity using `sheafCompose`; they do not replace the ring sheaves.
- Abelian module categories: the two `SheafOfModules.{r}` categories over those
  underlying ring sheaves. Verdict: exact. I read `ringedSiteModules`, which is a
  transparent abbreviation of this Mathlib category, and Mathlib's SheafOfModules
  object/morphism structures and Abelian instance. They give semilinear restrictions,
  sectionwise linear morphisms, kernels and sheafified cokernels as in the node.
- Size and sheaf infrastructure: `J.HasSheafCompose`,
  `J.WEqualsLocallyBijective AddCommGrpCat.{r}`, and
  `HasSheafify J AddCommGrpCat.{r}`. Verdict: these are the recorded dependency's
  infrastructure for forgetting commutativity, scalar extension and the Abelian
  instance, not additional algebraic/geometric assumptions. The ring and module
  universe r remains independent of site object universe u and morphism universe v.
- Unbounded derived categories: the two `[HasDerivedCategory.{w} ...]` binders
  and `DerivedCategory`. Verdict: exact. I opened Basic.lean: these choose
  localizations at quasi-isomorphisms with morphisms in the chosen universe;
  `HasDerivedCategory.standard` supplies the unrestricted standard size. There is
  no bounded derived-category substitution or equality imposed on u, v, r, or w.
- Derived scalar extension F computed by K-flat resolutions:
  `ringedDerivedScalarExtension φ`. Verdict: exact. I traced the four successive
  `choose_spec` projections through `derivedChangeOfRingsIndependentCoefficients`:
  they pass E, its object identification, its map identification, and additivity;
  `.2.2.choose` then selects LF from the universal derived-pair clause. The ordinary
  functor is fixed on both objects and maps; the counit universal property determines
  LF up to compatible natural isomorphism and is invertible on every K-flat complex.
  This is not a choice from an unconstrained Nonempty functor. Bound assertions and
  Tor vanishing are invariant under that isomorphism, so no hollow definition arises.
- Integer a and arbitrary derived object M: `(a : ℤ)` and a separate `∀ M` in
  each conjunct. Verdict: matches every integer and every object, with the node's
  order of quantification; neither clause depends on the other clause's hypothesis.
- Clause (a), its hypothesis and conclusion:
  `M.IsLE a → ((ringedDerivedScalarExtension φ).obj M).IsLE a`.
  Verdict: exact. I read `DerivedCategory.TStructure.t`, `IsLE`, and `isLE_iff`:
  the predicates mean precisely vanishing of H^i for i > a, not termwise vanishing
  of the supplied representative. There is no lower-bound hypothesis.
- Clause (b), initial lower bound: `M.IsGE a`.
  Verdict: exact by `DerivedCategory.isGE_iff`, which gives H^i(M) = 0 for i < a.
- Clause (b), all Tor vanishings:
  `∀ (q : ℤ), a ≤ q → ∀ (p : ℕ), 0 < p → IsZero (...)`.
  Inside `IsZero`, source `homologyFunctor ... q` gives H^q(M),
  `CochainComplex.singleFunctor ... 0` places that module in degree zero,
  `DerivedCategory.Q.obj` localizes it, the same F extends its scalars, and target
  `homologyFunctor ... (-(p : ℤ))` takes H^(-p). Verdict: exactly the node's
  Tor_p^R(H^q(M),S), for every q >= a and every positive Tor degree. It is an
  S-module sheaf, and vanishing agrees with vanishing after restriction to R.
- Clause (b), conclusion and absence of further bounds:
  `((ringedDerivedScalarExtension φ).obj M).IsGE a`.
  Verdict: exactly vanishing below a. The second conjunct has no IsLE condition,
  no finiteness, no flatness hypothesis, and no point-existence hypothesis.

Edge cases: zero derived objects, zero cohomology sheaves, zero ring sheaves, identity
ring maps and the empty site are permitted by the binders. No Nonempty index type or
site is assumed. The empty scheme's site is included without introducing a scheme
hypothesis. The bound a = 0, negative bounds and all positive bounds are covered;
q = a is included. Tor degree p = 0 is deliberately excluded by `0 < p`; p = 1
is included with degree -1. Part (a) permits complexes unbounded below and (b)
permits complexes unbounded above. There is no characteristic restriction. Separate
u and v permit, in particular, a site with object universe t+1 and morphism universe t;
r can be chosen large enough for that small site and its coefficients.

Independent duplicate searches, using words different from the worker's queries:

- LeanFinder via msearch.py: "Total left derived extension of scalars is right t exact,
  and preserves connective complexes with scalar extension acyclic cohomology".
  Eight hits, including Ext.mapExactFunctor and ordinary Tor/Tor'; none is this
  ringed-site scalar-extension statement.
- Loogle via msearch.py: `"IsLeftDerivedFunctor", "IsGE"`. No hits.
- Mathlib grep via msearch.py:
  `changeOfRings.*IsLE|changeOfRings.*IsGE|[Tt]ensor.*[Tt]Exact|[Cc]onnective.*[Tt]or`.
  Fourteen hits, primarily imports of ordinary tensor right-exactness; no match.
- LeanSearch via msearch.py: "The left derived scalar extension functor on sheaves
  of modules preserves upper cohomology bounds and preserves lower bounds if each
  cohomology sheaf is Tor acyclic". Eight hits, including ordinary ModuleCat
  extendScalars, its adjunction, flatness-based exactness, and exact sheafification.
  Their displayed signatures concern underived modules, not the stated theorem.
- Direct rg over upstream WeilConjectures and side lean/Sheaf for scalar extension,
  change of rings and tensor bounds. I opened the actual upstream
  CategoryTheory/DerivedCategory/FlatModel.lean signatures of `isLE_tensor` and
  `isGE_tensor_of_torAmplitudeIn`. The former is tensor inside one monoidal derived
  category; the latter requires a uniform Tor amplitude, stronger than Tor
  acyclicity of this M's cohomology. Neither is the two-clause theorem.
- I checked every side module referencing `derivedChangeOfRingsIndependentCoefficients`.
  Most select coefficient reductions on particular pro-etale sites.
  `CategoryTheory.ConstantCompletion.extend` is more general in its rings, but its
  enclosing binders impose `{C : Type u} [SmallCategory C]`, ring/module universe u
  and standard localizations. It cannot supply the independent-universe helper here.
  The helper directly selects the already recorded universal pair without copying
  its tensor construction. Exact-name searches in Mathlib, upstream WeilConjectures
  and dag/lean_names_upstream.json found neither new declaration.

Docstrings and mechanical checks: the module and both declarations carry the source
place and the requested blueprint tag. The theorem docstring carries all six node
proof steps, including the finite-truncation induction starting below a, the eventual
cohomology isomorphism in each degree, exact degreewise colimits, signed symmetry,
and detection after restricting scalars. The proof imports cover every recorded
proof dependency. The only theorem proof is `sorry`; the helper is a real selection
from the universal derived-pair theorem. There are no file-local notations, instances,
private definitions, hidden let/show binders in the theorem, or overlong lines.
All variables and universes are explicitly bound. The node's lean.statement is
verbatim equal to the file's theorem signature (checked by exact string comparison).

Mismatches found: none. Changes: appended this independent second-reading section;
left the correct Lean module and node unchanged. Validation: scompile.py compiled
both the sandbox and library-module checks successfully, each in 3.0 seconds, with
no warnings or errors. The dry-run and delivery results follow below.

Delivery validation: deliver2.py --no-push printed OK: preflight passed and the
module compiled cleanly. The prescribed deliver2.py push is the final step.
