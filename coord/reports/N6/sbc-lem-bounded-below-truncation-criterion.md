## Worker report

Stage 2 restatement of `sbc-lem-bounded-below-truncation-criterion`, group N6,
2026-10-17. The delivery states
`AlgebraicGeometry.Etale.boundedBelow_truncation_criterion` in
`Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion`. Its only proof is `by sorry`.
No mathematical statement, statement dependency, proof, or proof dependency is changed.
The previous binding was withdrawn because `hypercohomologyCouple` no longer accepted its
functor and complex arguments. No repair-notes file exists for this item. The source and
archived binding in `lean_before_upsync_e47` were read, as were all six statement dependencies.

Sources read: the recorded master blueprint node in `sec-smooth-base-change/sk-rem-rest`,
order 1439; the current main-20261015 node and proof in `sec-smooth-base-change/sk-thm-sbc-derived`,
order 1494. Their truncation claims agree. The node's expanded square and three maps remove
the free-morphism ambiguity in the short blueprint paragraph.

Hypotheses and clauses, in order:

- The schemes and the morphisms g:T→S, f:X→S, e:Y→T, h:Y→X are exactly the binders
  `{Y T X S : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)`.
  `(_sq : ChosenCartesianSquare e h g f)` supplies the chosen fibre-product identification,
  both projection equations and commutativity. Thus the arbitrary named Y is the stated
  fibre product up to its specified isomorphism, without choosing a new pullback object.
- `(P : Set ℕ)` is the prime allowance used by the recorded torsion definition; that
  definition tests only prime elements, so extraneous composite members are immaterial.
- `(K : AbelianDerivedCategoryPlusTorsionOfPrimes T P)` supplies bounded-below membership
  and allowable torsion of all geometric cohomology stalks. `K.obj` is its ambient object.
  No explicit representative, strict lower bound, or torsion-preservation hypothesis is added.
- `(n : ℤ)` allows every integer cohomological degree, including negative ones.
- `(DerivedCategory.TStructure.t.truncLEι n).app K.obj` is precisely the canonical arrow
  τ≤n K→K, rather than an unspecified isomorphic source or arbitrary morphism.
- The first `IsIso` is its image under `hypercohomologyFirstFunctor g` = Rg_* and then
  `(DerivedCategory.homologyFunctor _ n).map`, giving the first displayed cohomology map.
- The second `IsIso` uses `hypercohomologyBaseChangeFunctor g f` = f⁻¹Rg_* and the same
  canonical arrow and degree-n cohomology functor, giving the second displayed map.
- The third `IsIso` uses `hypercohomologySecondFunctor h e` = Rh_*e⁻¹, again with that arrow
  and cohomology functor. The functor order agrees with the domains of h and e.
- The last conjunct quantifies over every bounded-below cochain complex `L` of abelian
  étale sheaves representing K, using `Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj)`.
  This is how the recorded spectral-sequence construction takes a representative; it
  does not select a resolution or require an injective representative.
- For every page `r : ℕ`, `2 ≤ r` selects E₂ and all subsequent pages, using the published
  convention `.page r p q = (.pageCouple (r-2)).E p q`. For every `q : ℤ` with `n < q`,
  each of the three clauses `IsZero (... .page r (n - q) q)` says precisely that H^q(K)
  cannot contribute on the diagonal p+q=n. No vanishing at q=n is asserted and no
  differential, filtration, or convergence hypothesis is assumed.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` (the complete chosen-square structure).
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`:
  `AlgebraicGeometry.Etale.AbelianDerivedCategoryPlusTorsionOfPrimes`, using
  `allowableTorsionPlusProperty`, `allowableTorsionSheafProperty` and the ambient inclusion.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`; its `truncLEι` is provided by the public import
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar`. The recorded derived direct image
  is used through the dependency's total `rightDerivedFunctor`; its bounded-below
  identification is `rightDerivedFunctorPlusCompatibility` from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, its restriction `mapDerivedCategoryPlus`,
  `mapDerivedCategoryHomologyFunctorIso`, and preservation of lower cohomological bounds.
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`:
  `AlgebraicGeometry.Etale.hypercohomologyFirstFunctor`, `hypercohomologyBaseChangeFunctor`,
  `hypercohomologySecondFunctor`, and `CategoryTheory.hypercohomologyCouple`.
  The dependency module is repaired below, retaining all its recorded declarations.
- Proof-plan imports also include the recorded negative-vanishing module
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`,
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, and the published
  `WeilConjectures.CategoryTheory.TruncationCouple` and `.ExactCouple`. Retired Sheaf
  duplicates from the old file are replaced by their recorded upstream modules.

The declaration docstring carries all three current DAG proof steps: lower-bound
preservation, the truncation triangle and long exact sequence, and induction on exact-couple
pages. The last step works for all representatives L; the supplied isomorphism identifies
its spectral sequence with one for K but is not used to establish the diagonal vanishing.

Edge cases checked before drafting: n negative and n=0; n below any lower bound of K;
K=0; empty schemes; P empty, all primes, or with irrelevant nonprime elements; q=n
(the possibly nonzero boundary degree) and q=n+1 (p=-1); initial page r=2 and every later
page. No smoothness, qcqs, invertibility on S, upper bound, or nonzero-object assumption
is needed. Scheme and coefficient universes retain the recorded `Scheme.{u}` and
`AddCommGrpCat.{u+1}` conventions; all variables are explicitly bound and autoImplicit is false.
No disputed mathematical statement or source-based correction was needed.

Searches (2026-10-17):

- `msearch.py ... leansearch` query: "The cohomology in degree n of the right derived
  functor is unchanged by canonical truncation above degree n". Eight hits: rightDerived,
  rightDerivedToHomotopyCategory, cosimplicial truncations, CochainComplex.truncate,
  quasiIso_truncGEMap_iff and truncGE; no exact full statement.
- `msearch.py ... leanfinder` query: "Cohomology in degree n of the right derived direct
  image is unchanged by truncation above n, and the truncation spectral sequence vanishes
  for q greater than n in total degree n". Eight hits: quasi-isomorphism criteria for
  truncLE/truncGE and DerivedCategory.isZero_of_isGE/isZero_of_isLE; ingredients only.
- `msearch.py ... loogle` query `"rightDerivedFunctor", "trunc"`: zero hits.
- `msearch.py ... grep` query `truncLE.*rightDerived|rightDerived.*truncLE|homologyMap.*trunc`:
  seven hits in CM5a, TruncGEHomology and TruncLEHomology; none is the full statement.
- `rg` and the item-id search in upstream WeilConjectures found the module-sheaf lemmas
  `Etale.isIso_homologyFunctor_map_rightDerivedFunctorPlus_map_truncLEι_app`,
  `Etale.isIso_homologyFunctor_map_baseChangeSource_map_truncLEι_app`, and
  `Etale.isIso_homologyFunctor_map_baseChangeTarget_map_truncLEι_app` in
  `SixFunctors/Etale/SmoothBaseChange/Derived.lean`, and the abstract plus-category
  comparison in `CategoryTheory/DerivedCategory/PlusDevissage.lean`. Their signatures and
  docstrings were opened. They do not give the abelian-sheaf conjunction with page support;
  the recorded allowable-torsion and spectral-couple interfaces must be retained here.
- `rg` in `lean/Sheaf` found the withdrawn criterion source and its consumer
  `BoundedBelowDerivedSmoothBaseChange.lean`. The old source was read in full, along with
  the current dependency modules. The theorem name is being restored for this same node,
  not introduced as a duplicate of a different notion.

## Dependency modules

`def-weil-pbc-hypercohomology-filtrations` is repaired under §1(B), in its existing owning
module `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`. The initial scompile reproduced
all three "Function expected at hypercohomologyCouple" failures. A temporary #check/#print
probe showed the published compiled declaration has only category B as a parameter and
has body `sorry`. Thus it supplies neither the dependence on F and L nor the specified
truncation-couple data. The current source obtained with `scompile.py --source` contains
that full construction but must be re-elaborated and delivered. F, its CommShift and
IsTriangulated instances, and K are now explicitly bound at `hypercohomologyCouple`.
All probe commands were removed. This is a repair of the recorded dependency interface;
no private spectral-sequence definition or arbitrary map is introduced.

The dependency still defines its D-terms as cohomology of F applied to canonical truncations,
its E-terms as cohomology of F applied to the shifted cohomology complexes, and its alpha,
projection and boundary maps as the actual canonical cohomology maps. The separately named
`hypercohomology_maps_exact` theorem supplies the exactness proofs for the real structure;
`hypercohomology_images_antitone` supplies monotonicity of the actual image filtration.
The three named functors are still Rf_*, g⁻¹Rf_*, and Rf'_*g'⁻¹.

Every clause of the dependency is retained: `hypercohomologyFiltrations` gives the three
image filtrations; `hypercohomologyFiltrations_spec` gives their finiteness, lower and upper
filtration bounds, page vanishing and convergence to the specified abutments; the three
bridge equations identify the first couple with TruncationCouple; the three E₂
identifications are the higher direct-image formulas; the termwise inverse image vanishes
below a, commutes with truncation through the specified inclusion equation, and commutes
with cohomology; the delta/phi comparisons identify the base-changed couple and all page
differentials, normalized by the canonical cohomology isomorphism; the final comparison
identifies the inverse image of the first image filtration with the middle filtration.
No assumption or conclusion of this dependency changes. Its node changes only in `lean`.
All three postponed theorems have proof docstrings for this same DAG node; definitions
contain real data, with only their proof obligations supplied by named theorems.

## Validation

The initial criterion-only compilation reproduced the exact withdrawn-interface defect.
Compiling the full dependency source first and the criterion second through scompile.py
passed without diagnostics. Both sandbox and library-path checks passed for each file,
with the dependency approximately 6 seconds and the criterion approximately 2 seconds.
The explicit-parameter version is compiled again before the final dry run. All validation
uses the prescribed file-only wrapper and private overlay; no global build or live edit.

The independent second reading is assigned by the dispatcher after this worker completes.

## Second reading by N6

Independent reading on 2026-10-17. I opened the item node, both delivered modules, all six
statement-dependency records and their declaration sources. I read the master blueprint
node (order 1439), its proof and the current main-20261015 version (order 1494). I also
read the dependency's master blueprint source and Stacks derived.tex Lemma 015J, including
its bounded-below and left-exact hypotheses, and etale-cohomology.tex Lemma 0DDE. Properness
in 0DDE is needed for the base-change *comparison* theorem, not for constructing these
spectral sequences or for the present truncation criterion. No properness or smoothness
assumption belongs in this item's signature.

My object/hypothesis/conclusion checklist, independently extracted from the node:

1. A set of allowable primes: `(P : Set ℕ)`. The recorded
   `allowableTorsionSheafProperty` tests membership only for prime divisors of positive
   annihilators. Allowing other natural numbers in P changes no allowable torsion object.
   Verdict: the same prime allowance, without an extra assumption.
2. Schemes T,S,X and maps g:T→S and f:X→S: `{Y T X S : Scheme.{u}}`,
   `(g : T ⟶ S)`, `(f : X ⟶ S)`. Verdict: all schemes and arbitrary scheme morphisms;
   no finiteness, characteristic, separation or flatness assumption.
3. The fibre product Y with projections e:Y→T, h:Y→X: the two morphism binders and
   `ChosenCartesianSquare e h g f`. I opened that structure: its `isoPullback` identifies
   Y with `pullback g f`, and `hom_fst`/`hom_snd` identify e/h with both projections;
   its inherited `CommSq` gives commutativity. Verdict: actual specified Cartesian data,
   rather than merely a commutative square or unrelated isomorphic schemes.
4. K in the bounded-below allowable-torsion derived category of abelian etale sheaves:
   `K : AbelianDerivedCategoryPlusTorsionOfPrimes T P`. The opened definition is the full
   subcategory for `homologyProperty (allowableTorsionSheafProperty T P)` intersected with
   `DerivedCategory.TStructure.t.plus`. `K.obj` is its ambient derived object.
   Verdict: correct abelian-sheaf category, bounded below with the stated stalk torsion;
   no module-coefficient replacement or termwise-bound hypothesis on K.
5. Every integral degree n: `(n : ℤ)`. Verdict: no restriction to natural degrees.
6. The canonical truncation inclusion: `(DerivedCategory.TStructure.t.truncLEι n).app
   K.obj`. I checked Mathlib's standard t-structure and `truncLEι = truncLTι (n+1)`.
   Verdict: the specified τ≤n K→K, not an arbitrary morphism with an isomorphic source.
7. First displayed isomorphism: the first `IsIso`, applying the degree-n
   `DerivedCategory.homologyFunctor` to the image of that inclusion under
   `hypercohomologyFirstFunctor g`. Its definition is `(lowerStar … g).rightDerivedFunctor`.
   The total-derived and plus-derived functors agree by the recorded
   `rightDerivedFunctorPlusCompatibility`. Verdict: exactly Hⁿ(Rg_*τ≤nK)→Hⁿ(Rg_*K).
8. Second displayed isomorphism: the second `IsIso`, with
   `hypercohomologyBaseChangeFunctor g f = Rg_* ⋙ f⁻¹_D`. I checked `upperStar`,
   `mapDerivedCategoryPlus` and its inclusion compatibility against the recorded
   inverse-image node. Verdict: exactly the derived pullback of the two complexes,
   followed by Hⁿ, with the same canonical arrow.
9. Third displayed isomorphism: the third `IsIso`, with
   `hypercohomologySecondFunctor h e = e⁻¹_D ⋙ Rh_*`. Verdict: exactly the third map,
   with both morphisms in the correct order and domains.
10. Only q≤n contributes in total degree n in all three truncation spectral sequences:
    the final conjunct quantifies over every bounded-below representative L and its
    `Nonempty (DerivedCategory.Q.obj L.obj ≅ K.obj)`, every `r : ℕ` with `2 ≤ r`, and
    every `q : ℤ` with `n < q`. Its three `IsZero` clauses are at `(n-q,q)` for the same
    three functors. I read the current server source of `BigradedExactCouple.page`
    using `scompile.py --source`: it is `(pageCouple (r-2)).E`, so r=2 is E₂.
    Verdict: exactly the forbidden part of the total-degree-n diagonal on E₂ and later
    pages. Quantifying over representatives expresses the recorded construction of a
    sequence for K and imposes no choice of injective resolution or extra hypothesis.

Edge cases: P empty permits the zero cohomology objects; zero K and empty schemes are
included. n=0, negative n, and n below a lower bound all remain in scope. q=n is correctly
unrestricted; q=n+1 gives p=-1 and is correctly zero. There is no index-set nonemptiness
assumption. All characteristics are allowed, with no prime-invertibility hypothesis.
The universes are the existing scheme and abelian-sheaf convention `Scheme.{u}` and
`AddCommGrpCat.{u+1}`; no independent undersized test-object universe or extra equality is
introduced. All variables are bound, and `autoImplicit` is false.

I independently searched with different wording. LeanFinder query "A connective derived
pushforward carries the canonical upper truncation inclusion to an isomorphism on nth
cohomology and has zero spectral terms in negative first degree" returned eight hits,
including `CochainComplex.quasiIso_ιTruncLE_iff` and strict-truncation isomorphisms, not
this conjunction. LeanSearch query "The nth cohomology of a left t-exact derived pushforward
depends only on the canonical upper truncation and all negative first-index hypercohomology
spectral sequence entries vanish" returned truncation/derived-functor ingredients only.
Loogle `"IsIso", "truncLEι"` returned four general t-structure truncation isomorphisms,
each requiring an already bounded-above object or another truncation; none is this item.
I also ran rg for `truncLEι`, `truncation_criterion`, `trunc.*homology`,
`homology.*trunc`, and declarations named `hypercohomology*` over Mathlib, upstream
WeilConjectures and the project's Lean. I opened the three candidate comparisons in
`SixFunctors/Etale/SmoothBaseChange/Derived.lean`: they use ModuleCat coefficients and
state only the individual isomorphisms. The general comparison in `PlusDevissage.lean`
requires an arbitrary functor and its lower-bound-preservation hypothesis and has no page
clause. `HypercohomologyLeftEdgeTruncation` describes a different left-edge map for an
object in [0,n]. `HypercohomologyConvergence` gives support/convergence, not the three
canonical isomorphisms. Thus no existing declaration replaces this full item.

Dependency repair: I compared the complete delivered `HypercohomologyFiltrations.lean`
with the recorded source. Apart from authorship, its sole change is to bind F, its
CommShift/IsTriangulated structures and K explicitly on `hypercohomologyCouple`. This
repairs the erased-parameter compiled interface without changing its mathematical data.
I checked the dependency against its own expanded node and blueprint: D/E are exactly the
derived truncation/single-cohomology terms; alpha, projection and boundary are actual
canonical maps. `hypercohomology_maps_exact` supplies only proof fields. The abutment map
is the image of `ιTruncLE`; the filtration is its `imageSubobject`, with only antitonicity
postponed. All three finite-filtration, half-plane vanishing and convergence clauses are
retained, including normalization of the diagonal colimit maps and image filtrations.
The three bridge equations, higher-direct-image E₂ identifications, termwise inverse-image
lower bound, truncation inclusion equation, cohomology comparison, canonical delta/phi
normalizations and page differential squares, and final inverse-image filtration equation
each match the respective dependency-node clause. Torsion, representative and common
termwise/cohomological lower-bound hypotheses are present in the specification exactly
where the dependency introduces them. No new node, private duplicate or hollow data was
added. I obtained the current `TruncationCouple` and `ExactCouple` server sources through
the wrapper: the single complex really is H^q(L) in degree q and the derived E-term really
is a cokernel into a differential kernel, as the proof docstring uses.

H5/H6/H8/H9: both modules have real definition data, postponed proof obligations are named
theorems, and all four delivered theorem bodies are `by sorry`. Every declaration has its
source/blueprint docstring; I matched the criterion's three proof paragraphs with all
three DAG proof steps. Both modules stay within 100 columns. The two node copies differ
from the repository only in `lean`; both `lean.statement` values are verbatim equal to
their main declaration signatures. There is no statement_change or new definition node,
so no correction/citer audit is required.

Mismatches found in this second reading: none. I retained the Lean and node records and
added this independent report. I specifically confirmed the first worker's §1(B) repair
instead of restoring the unusable published binding. Required scompile validation of both
sibling modules passed without diagnostics: dependency sandbox/library checks 5.9/7.0 s,
criterion sandbox/library checks 3.0/2.8 s (plus overlay/preliminary checks). All compilation
used the wrapper, in dependency order, within the normal per-file limits.
