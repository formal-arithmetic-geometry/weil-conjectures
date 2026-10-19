## Worker report

Module `Sheaf.Paper.SiteBoundedConstantModel` states
`CategoryTheory.exists_site_bounded_constant_model`, with a single `sorry` proof.
The source is the strengthened induction assertion in Stacks 094G, read in
`literature/stacks-project/sites-cohomology.tex`, lines 14247–14314. No statement
correction, new node, dependency repair, or disputed assertion is needed.

Hypotheses and clauses:

- A small site is `C : Type u`, `SmallCategory C`, and `J : Precoverage C`
  with `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`, and
  `HasPullbacks`, exactly the recorded site interface. Its topology is
  `J.toGrothendieck`. `X : C` and `hX : IsTerminal X` give the final object.
- The ring is `B : Type u`, `[CommRing B]`, `[IsNoetherianRing B]`.
- Constant-coefficient module sheaves are `Sheaf J.toGrothendieck (ModuleCat B)`.
  This encodes sheaves of modules over the constant ring: a B-action on all
  sections commuting with restriction extends uniquely to the constant ring
  sheaf action by local representatives of scalars and sheaf gluing. Conversely
  restriction along the constant-ring sheafification unit recovers the B-action.
  This retains the same additive sheaf and linear maps. This is also the
  `ModuleCat B` constant-sheaf and slice convention of the recorded
  `lem-weil-pbc-site-constant-restriction` Mathlib match; no arbitrary coefficient
  equivalence or ring identification is a parameter of this statement.
- `K : DerivedCategory (Sheaf ... (ModuleCat B))` is the derived object. The
  `HasDerivedCategory.{w}` parameters choose localization morphism sizes on the
  original and slice sites; they carry no extra mathematical condition and can
  all be supplied by `HasDerivedCategory.standard` at `w = u+1`.
- `a b : ℤ` and `hab : a ≤ b` specify the interval.
- `hvan` states `IsZero ((DerivedCategory.homologyFunctor ... q).obj K)` whenever
  `q < a ∨ b < q`, exactly vanishing outside the interval.
- `hloc` quantifies over every degree q and object V, giving a covering family
  `U i ⟶ V`, with `Presieve.ofArrows U f ∈ J V`. On each member its restricted
  cohomology sheaf is isomorphic to `constantSheaf ... M` for a module M with
  `Module.Finite B M`. This is local finite constancy, including zero degrees.
- The conclusion gives a covering family `U i ⟶ X`, with the same precoverage
  membership condition. Empty index sets are permitted when they cover.
- For each member, `M : CochainComplex (ModuleCat B) ℤ` is a genuine module
  complex. `∀ q, Module.Finite B (M.X q)` gives finite terms in every degree;
  `q < a ∨ b < q → IsZero (M.X q)` gives precisely the required bounds.
- The final `Nonempty (... ≅ ...)` is an isomorphism in the slice derived
  category. Its left side is canonical `overPullback.mapDerivedCategory`.
  Its right side is `DerivedCategory.Q.obj` of the result of
  `constantSheaf.mapHomologicalComplex` on M. Thus both terms AND differentials
  are induced by the same constant-sheaf functor; no separate unconstrained
  differentials are supplied.
- No points, enough-points, faithfulness of the constant functor, finite
  projectivity, or Tor-amplitude assumptions occur.

The explicit instance arguments to `mapDerivedCategory` are existing Mathlib
terms: additivity follows from preservation of binary products, limits follow
from the continuous adjunction, and colimits follow from
`Functor.sheafAdjunctionCocontinuous` for `Over.forget`. They are not postponed
helper theorems or extra assumptions. The final proof remains only `sorry`.

Dependency declarations used:

- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: the site node's recorded
  interface (`Precoverage`, `Sheaf`; object cohomology itself is not used).
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`,
  `GrothendieckTopology.overPullback`, with continuous/cocontinuous slice functor.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf` (through Sites.Abelian):
  `CategoryTheory.constantSheaf`, sheafification of the constant presheaf.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` (through ExactFunctor):
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`.

All locally recorded Sheaf proof-dependency modules are imported without
`public`: `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`,
`Sheaf.CategoryTheory.TruncationDescends`, and
`Sheaf.Paper.SiteSheafificationSectionsLocal`. Other proof nodes with no landed
module are not imported. The docstring carries all eight steps of the DAG
proof, including the empty-slice case and the roof-to-chain-map argument.

Edge cases checked against the source: `a=b` permits a single finite module in
that degree; all-zero K permits the zero complex; zero ring and zero finite
module are allowed; a covering by the empty family is allowed; a slice covered
by the empty sieve needs no faithfulness and uses the zero complex. Arbitrary
integers, including negative endpoints, are retained. The index set lives in
the small site's universe. No finite index set or nonempty site assumption is
added.

Searches for an existing statement (2026-10-15):

- `msearch.py ... leanfinder "A bounded derived complex on a small site with
  finite locally constant cohomology is locally a constant bounded complex of
  finite modules"`: 8 results, all specialized condensed-module constructions;
  none states this arbitrary-site derived local model.
- `msearch.py ... loogle '"constantSheaf"'`: 12 results, constant-sheaf functor,
  adjunctions and infrastructure; no bounded model theorem.
- `msearch.py ... grep
  'constantSheaf.*(complex|homology)|LocallyConstant.*Derived'`: 0 hits.
- `rg` with that expression and the proposed declaration name in upstream
  `WeilConjectures` and project `lean/Sheaf`: only an unrelated regular-immersion
  local constancy theorem and constant-sheaf cochain calculations; no match.
- `grep -rn 'lem-weil-pbc-site-bounded-constant-model'` in upstream
  `WeilConjectures`: no hits.
- Read the recorded dependency signatures and docstrings, including the
  constant-ring/module comparison declarations: their scheme/etale hypotheses
  do not state this arbitrary-site theorem. No existing theorem duplicates it.

Validation: scompile.py clean, 2.4 seconds (nice 19, two threads, 60 seconds
per file). Final dry-run result is recorded by deliver2.py.


## Second reading by NO

Read the node, its seven statement dependencies and their recorded interfaces,
all proof-dependency records, the delivered Lean, and Stacks
`sites-cohomology.tex`, section “Complexes with locally constant cohomology
sheaves”, especially the strengthened induction assertion of Tag 094G.
The section fixes an arbitrary site and ring; the lemma adds a final object,
Noetherian coefficients and bounded finite locally constant cohomology. The
node explicitly specializes the ring to a commutative ring, as does the Lean.
There is no statement_change, new node or dependency module to audit.

Object/hypothesis/conclusion inventory, matched individually (H3):

1. A small site: `{C : Type u} [SmallCategory C]`, `J : Precoverage C`, and
   `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange`,
   `HasPullbacks`. PASS: this is exactly the recorded site interface, not an
   assumption that all categorical pullbacks exist. I read the four classes
   in Mathlib Sites/Precoverage: HasPullbacks concerns covering arrows only.
   Sheaves use the generated topology `J.toGrothendieck`.
2. Its final object X: `(X : C) (hX : IsTerminal X)`. PASS: the specified object
   is terminal, not merely inhabited. No points of the site are introduced.
3. A commutative Noetherian coefficient ring: `(B : Type u) [CommRing B]
   [IsNoetherianRing B]`. PASS: IsNoetherianRing is the recorded Noetherian
   predicate, with no field, characteristic, finite-cardinality or projectivity
   condition.
4. K in the derived category of constant-B-module sheaves: `K :
   DerivedCategory (Sheaf J.toGrothendieck (ModuleCat B))`. PASS: ModuleCat-valued
   sheaves encode exactly modules over the sheafification of the constant ring
   B. Explicitly, constant scalars act on each section; a locally represented
   section of the constant ring acts locally using those scalars, and the
   products glue uniquely. Every sheaf-module action restricts back to this
   B-action. This identification preserves morphisms, restriction, constants,
   kernels and cokernels. It is the same encoding explicitly used by the
   dependency site-constant-restriction, whose Mathlib CoverLifting signature
   I opened. It is not a different coefficient ring or an arbitrary chosen map.
5. Localization sizes: the two `HasDerivedCategory.{w}` instance binders supply
   chosen derived localizations for the site and all slices. PASS: I opened
   DerivedCategory.Basic; HasDerivedCategory.standard supplies these in the
   common universe u+1. They add no mathematical exactness or existence-of-points
   restriction. The same w is available for all the small slice categories.
6. Integers a <= b: `(a b : ℤ) (hab : a ≤ b)`. PASS: arbitrary integer endpoints,
   in precisely the order required by the node and source.
7. Cohomological vanishing: `hvan` quantifies over every integer q and uses
   `q < a ∨ b < q` and `IsZero ((DerivedCategory.homologyFunctor ... q).obj K)`.
   PASS: I read homologyFunctor and homologyFunctorFactors; this is cohomology
   of any representative in the derived localization, not section cohomology.
8. Every cohomology sheaf is locally constant finite: `hloc` quantifies over q
   and V, then a covering `Presieve.ofArrows U f ∈ J V`, then a module M for each
   member with `Module.Finite B M` and a sheaf isomorphism after `overPullback`.
   PASS: this is local isomorphism to the constant sheaf of a finitely generated
   B-module. Requiring the property on every V is equivalent to its covering
   formulation at final X, by pullback and restriction of constant sheaves.
9. A covering of X: the outer conclusion `∃ I U f, Presieve.ofArrows U f ∈ J X`.
   PASS: there is one covering for K, independent of degree. No finite or
   nonempty index condition is imposed.
10. A bounded finite module complex on every member: `∀ i, ∃ M : CochainComplex
    (ModuleCat B) ℤ`, with `∀ q, Module.Finite B (M.X q)` and `∀ q, q < a ∨ b < q
    → IsZero (M.X q)`. PASS: terms are finite modules, zero outside precisely
    the original [a,b]; the complex already includes linear differentials and
    the square-zero equations. Finite does not mean finite projective.
11. The derived local identification: `Nonempty (... ≅ DerivedCategory.Q.obj
    ((Functor.mapHomologicalComplex (constantSheaf ...) (ComplexShape.up ℤ)).obj
    M))`. PASS: the left side is exactly slice restriction of K via the derived
    functor of `overPullback`; the right side sheafifies the same module complex
    termwise, including its differential maps. I read ExactFunctor's
    mapDerivedCategory and mapDerivedCategoryFactors and Sites/Over's
    overPullback. The displayed additivity/finite-colimit instance terms are
    existing Mathlib constructions, not extra hypothesis binders. Nonempty
    asks for an isomorphism, with no chosen or functorial model demanded.
12. No assumption of points: no point or enough-points binder occurs. PASS.

Edge cases (H3): empty covering index types are allowed in both hloc and the
conclusion. Slices covered by the empty sieve are allowed and can use the zero
complex; faithfulness on such a slice is never a theorem hypothesis. The zero
object K and zero ring are allowed. When a=b, a single finite module in that
degree is allowed, including the zero module. Negative bounds and degree zero
are covered. There are no scheme, characteristic or n-parameter restrictions.
An empty category cannot have the final object required by both source and
Lean; a degenerate topos or the site of an empty scheme is still allowed.
The small-site, coefficient and index data use the recorded common universe u,
which is arbitrary, so this is not restricted to countable or finite data.
The derived localization universe w is separately bound; no universe or free
variable is inferred implicitly.

Independent H4 searches with different queries:

- msearch leanfinder: “locally constant finite cohomology sheaves admit locally
  bounded complexes of constant finite modules”: eight hits, specialized
  condensed/compact-Hausdorff locally constant functors, no theorem of this form.
- msearch loogle `"mapDerivedCategory"`: twelve hits, including the exact functor
  interface used here, no local bounded constant model theorem.
- msearch grep `constant.*bounded|bounded.*constant|finite.*constant.*model`:
  twenty-five unrelated bounded-constant estimates, no match.
- Direct rg on upstream WeilConjectures, project lean/Sheaf, and Mathlib's
  Algebra/Homology and CategoryTheory/Sites using
  `constant.*bounded|bounded.*constant|exists_site_bounded_constant_model|locally.constant.*cohomolog`:
  unrelated torsion and Fourier-transform bounded-constant constructions,
  pro-etale bounded-constructible commentary, and local-cochain results only.
  None asserts this arbitrary-site theorem, so existing:true would be wrong.

H4/H5/H6/H8/H9: all notions are supplied by the dependency interfaces or Mathlib;
there are no new definitions, private copies, hollow constructions, proved
helper lemmas, local notations or local instances. The only theorem body is
sorry. The module and theorem docstrings cite Tag 094G and the exact blueprint
id. I checked the proof docstring against all eight DAG proof steps: slice
restriction and constants, empty slices, the one-degree base case, local cycle
lifts, the finite-cohomology cone and induction, the right-fraction/top-component
boundary calculation, local constancy of the module map and its differential
relation, and the cone-triangle comparison followed by composite coverings.
The namespace and all variable/universe binders are explicit; every line has
at most 100 characters. The node lean.statement equals the file signature
verbatim (checked by extracting the text before `:= by`).

Mismatch and repair: the proof docstring uses the recorded
lem-pc-quasi-isomorphisms-multiplicative-system but its Mathlib module was not
imported. Added the non-public proof import
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`, which supplies the two
calculus-of-fractions instances and imports the general right-fraction API.
The mathematical statement, signature, dependencies and node record are
unchanged. No other mismatch was found. Server single-file compilation and
deliver2 preflight are run on the repaired module before delivery.
