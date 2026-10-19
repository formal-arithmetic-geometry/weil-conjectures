## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion` states
`SheafOfModules.isFlat_iff_local_equationalCriterion`, with `sorry` as its entire proof.
There are no new definitions, auxiliary theorems, or extra nodes. Only the item's `lean`
record changes. Its natural-language statement, dependencies, and proof remain unchanged.

This is a restatement of the withdrawn interface, not an existing:true rebind of its stale
file. The node's `lead_note` records the withdrawn declaration and an unknown
`monoidalClosed` error. There is no item-specific file in `coord/repair-notes`.
The replacement uses the current recorded flatness and site definitions and compiles
against the current overlay. It does not reference `monoidalClosed` or construct a new
monoidal instance. Two infrastructure imports supply the standard small-site abelian
sheafification instances; no extra sheafification hypotheses are imposed.

Clause-by-clause correspondence:

- A small site is `{C : Type u} [SmallCategory C] (J : Precoverage C)` with
  `(_hJ : J.IsSiteForCoverings)`. This is the currently recorded site component, including
  isomorphism covers, bind composition, and existence of covering pullbacks. It does not
  impose the former, stronger `IsStableUnderComposition` or global pullback classes.
- The commutative ring sheaf is `(A : Sheaf J.toGrothendieck CommRingCat.{u})`.
- The A-module sheaf is `M : ringedSiteModules.{u}` over the ring sheaf obtained from A
  by `sheafCompose ... (forget₂ CommRingCat RingCat)`.
- Flatness is exactly `IsFlatOnSite (J := J.toGrothendieck) (R := A) M`, the recorded
  exactness predicate for the sheafified sectionwise tensor functor. The biconditional
  `↔` states necessity and sufficiency.
- Every object and every nonnegative finite length are `∀ (U : C) (n : ℕ)`.
- The coefficient and module sections are `a : Fin n → A.obj.obj (op U)` and
  `s : Fin n → M.val.obj (op U)`.
- The relation is `(∑ p : Fin n, a p • s p) = 0`, used as an implication premise.
- The covering is `∃ S : Presieve U, S ∈ J U`. For each member it quantifies
  `∀ (V : C) (f : V ⟶ U), S f → ...`. A presieve records the arrows of the covering
  family, with no nonemptiness or finiteness condition on that family. Repeated arrows
  can use the same witnesses; the site's recorded convention allows reindexing.
- Its member-dependent nonnegative length and sections are `∃ (l : ℕ)` with
  `b : Fin n → Fin l → A.obj.obj (op V)` and `t : Fin l → M.val.obj (op V)`.
- Every section factors by
  `∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q`.
- Every coefficient column annihilates the original row by
  `∀ q : Fin l, (∑ p : Fin n, A.obj.map f.op (a p) * b p q) = 0`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (full body and source docstring read).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (transparent abbreviation to Mathlib `SheafOfModules`, full body and docstring read).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`
  (full body/docstring, including sheafification universes, read locally and checked
  against `scompile.py --source`). This is `exactFunctor` of `siteSheafTensorRight`.
- Proof-only import `Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`:
  `SheafOfModules.isFlat_over`, with its full signature and proof docstring read.
  This older same-size flatness interface is only part of the stage-3 proof plan;
  the theorem's statement uses the currently recorded `IsFlatOnSite` definition.
- Proof-only Mathlib import `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over` and `overFunctor`, and the source docstrings, implement the
  recorded localized ringed-site dependency without a private construction.
- Proof-only Mathlib import `Mathlib.LinearAlgebra.TensorProduct.RightExactness`:
  `lTensor_exact` and `rTensor_exact` implement the two tensor right-exactness clauses.
- Public Mathlib imports `CategoryTheory.Sites.LeftExact` and
  `Algebra.Category.Grp.FilteredColimits` provide the standard abelian sheafification
  infrastructure needed to elaborate the current flatness definition on a small site.

Source checked: `literature/stacks-project/sites-modules.tex`, `lemma-flat-eq`,
Tag 08FC, equivalence (1) and (2), and its proof via condition (3). Maps from finite free
module sheaves are specified by the images of their basis sections, so the two displayed
section identities express exactly its factorization and zero-composite conditions.
The declaration docstring carries all six current DAG proof steps and named dependencies.

Edge cases checked before writing:

- `n = 0`: the relation is the empty sum; use the identity covering and `l = 0`.
  Both quantified equations have empty index types and are vacuous.
- `l = 0` is allowed and says the restricted sections are zero; no artificial positivity.
- The zero module satisfies the criterion with `l = 0` on an identity cover and is flat.
- Empty covering families are allowed when the site admits them. Their witness condition
  is vacuous, as in the source; no nonempty-cover assumption is introduced.
- The empty category makes all section conditions vacuous, consistently with its trivial
  module-sheaf category. No object or covering index nonemptiness is assumed.
- The zero ring and arbitrary characteristic are allowed by `CommRingCat`.
- The single common universe is the small-site convention of the archived interface:
  C, its hom sets, coefficients, and modules are small in u. Any finite collection of
  their set-size bounds can be enlarged to a common universe; none is forced to be finite
  or countable. All variables and the universe u are explicitly bound.

Searches for an existing exact statement:

- `msearch.py ... leansearch "A sheaf of modules is flat if and only if finite relations
  locally factor through finite free modules"`: eight results, ordinary module flatness
  and ordinary equational criteria, no sheaf-on-site theorem.
- `msearch.py ... leanfinder "A sheaf of modules on a site is flat if and only if every
  finite relation between sections locally factors through a finite free module"`:
  eight results, finite-presentation sheaves and ordinary module equational criteria;
  none is the site's local-covering equivalence.
- `msearch.py ... loogle '"Module.Flat"'`: twelve ordinary ring-module results, no match.
- `msearch.py ... grep 'isFlat_iff|equationalCriterion|IsFlatOnSite'
  Algebra/Category/ModuleCat`: zero Mathlib matches.
- `rg` for `isFlat_iff_local_equationalCriterion`, `IsFlatOnSite`, and the item id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and shared `lean/Sheaf`:
  the only exact named criterion is the item's withdrawn stale side-project module.
  It uses the obsolete recorded `IsFlat` and stronger covering classes. It is replaced
  at its original path. Related flatness modules reuse `IsFlatOnSite` and the current
  site convention; none supplies this exact statement as an independent declaration.
- The existing independent-universe criterion node was read. It has different explicit
  infrastructure hypotheses and a covering-sieve conclusion, so it is not an exact
  declaration of this node's covering-family statement.
- `rg` for the declaration in `dag/lean_names_upstream.json`: no upstream match.

No statement correction or mathematical dispute. The withdrawn Lean signature is updated
only to the current definitions that the unchanged natural statement already cites.

Validation: `scompile.py Q116 lem-weil-pbc-site-flat-equational-criterion
<FlatEquationalCriterion.lean>` passed both sandbox and module-path compilation with no
errors or warnings. A first attempt exposed a missing locally-bijective sheafification
instance; importing the two standard Mathlib infrastructure modules fixed elaboration.
The required delivery dry run is recorded below after it completes.

`deliver2.py Q116 lem-weil-pbc-site-flat-equational-criterion --no-push` printed
`OK (dry run)`: compilation and preflight passed, except for the independent second
reading, which the tool explicitly reserves for the second reader. Nothing was pushed.

## Second reading by Q116

I opened the node `lem-weil-pbc-site-flat-equational-criterion`, its three statement
dependencies, the replacement module, and Stacks Project Tag 08FC (sites-modules.tex,
`lemma-flat-eq`). The node and Lean signature correspond clause by clause as follows.

- The node's small site is rendered by `{C : Type u} [SmallCategory C]`, a
  `Precoverage C`, and the explicit hypothesis `_hJ : J.IsSiteForCoverings`. This
  supplies the source's isomorphism-cover, transitivity, and covering-pullback axioms
  without adding global pullback or stronger composition classes. Verdict: exact.
- The sheaf of commutative rings is
  `A : Sheaf J.toGrothendieck CommRingCat.{u}`. Verdict: exact.
- The sheaf of A-modules is
  `M : ringedSiteModules.{u} ((sheafCompose J.toGrothendieck
  (forget₂ CommRingCat.{u} RingCat.{u})).obj A)`, using the recorded transparent
  `ringedSiteModules` abbreviation. Verdict: exact object and coefficient action.
- Flatness is `IsFlatOnSite (J := J.toGrothendieck) (R := A) M`, the recorded
  sheafified sectionwise tensor exactness predicate. Verdict: exact replacement of the
  withdrawn stale `IsFlat` interface; no mathematical hypothesis was added.
- The relation quantifies `∀ (U : C) (n : ℕ)`, coefficients
  `a : Fin n → A.obj.obj (op U)`, sections `s : Fin n → M.val.obj (op U)`, and premise
  `(∑ p : Fin n, a p • s p) = 0`. Verdict: exact finite relation for every object,
  including `n = 0`.
- The covering is `∃ S : Presieve U, S ∈ J U`; for each member the theorem uses
  `∀ (V : C) (f : V ⟶ U), S f → ...`. This is the current presieve encoding of the
  source's covering family and imposes no finiteness or nonemptiness. Verdict: exact
  current site formulation.
- For each covering member, the Lean existential `∃ (l : ℕ) (b : Fin n → Fin l → ...)
  (t : Fin l → ...)` renders the source's finite `l_i`, coefficients `b_{ipq}`, and
  sections `t_{iq}`. Verdict: exact, with `l = 0` permitted.
- The factorization clause is
  `∀ p, M.val.map f.op (s p) = ∑ q, b p q • t q`, exactly
  `s_p|_{U_i} = ∑_q b_{ipq}t_{iq}`. Verdict: exact.
- The zero-column clause is
  `∀ q, (∑ p, A.obj.map f.op (a p) * b p q) = 0`, exactly
  `∑_p a_p|_{U_i}b_{ipq}=0`. Verdict: exact, with the commutative-ring multiplication
  and restriction map in the correct order.
- The biconditional has no additional conclusion or hidden quantifier. Verdict: exact.

Source assumptions were checked directly in Tag 08FC: it assumes an arbitrary ringed
site and module, then gives (1) iff (2); the Lean specialization to a small
`Precoverage` site and a commutative-ring sheaf is precisely the node's stated setting.
The dependency declarations were opened: `Precoverage.IsSiteForCoverings` has the
required three site clauses, `ringedSiteModules` is Mathlib's `SheafOfModules`, and
`IsFlatOnSite` is exactness of the recorded sheaf tensor functor. No dependency is a
special-case notion or an unusable stale declaration.

Edge cases checked: `n = 0` uses the empty sum; `l = 0` is allowed; the zero module and
zero ring are included; arbitrary characteristic is included; empty categories and
empty covering presieves are not excluded; and the single universe `u` covers the site,
coefficients, and module as required by this node. No nonempty index, positivity, finite
cover, Noetherian, or characteristic hypothesis was introduced.

Existing-definition searches were repeated with `msearch.py` LeanSearch and LeanFinder
queries for a sheaf-module local finite-relation criterion, Loogle queries for
`Module.Flat` and flat sheaves, and `rg` over Mathlib, `WeilConjectures`, and shared
`lean/Sheaf` for `isFlat_iff_local_equationalCriterion`, `equationalCriterion`, and
`IsFlatOnSite`. Results were ordinary module criteria or finite-presentation APIs; no
exact site theorem exists. The only same-named declaration was the withdrawn stale
module, which uses obsolete `IsFlat` and stronger classes and therefore was not rebound.

The worker had already repaired the withdrawn signature, which used `IsFlat` together with
`[J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]`.
The replacement uses the node's current `IsFlatOnSite` and explicit
`_hJ : J.IsSiteForCoverings`, preserving the unchanged mathematical relation criterion.
Imports were updated to the current FlatOnSite and SiteCoveringAxioms infrastructure;
the declaration docstring was updated with the six proof steps and all blueprint
dependencies. No further Lean change or statement correction was needed in the second reading.

The independent search additionally found upstream
`CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations` in
`WeilConjectures.CategoryTheory.Sites.FlatLocalRelations`. I opened its signature and
surrounding variables: it assumes `[IsNoetherianRing R]` and has
`F : Sheaf J (ModuleCat.{u + 1} R)` over one fixed ring, rather than an arbitrary sheaf
of commutative rings. It is therefore not an exact existing declaration for this node.
The independent-universe side theorem was also opened; it has a covering-sieve conclusion
and explicit sheafification hypotheses, not this covering-presieve signature.

The replacement contains one theorem with its entire proof `sorry`, no definitions,
no hidden data, no local instances or notation, and explicit `universe u`.
The module and theorem docstrings contain the source and blueprint identifier; the
six proof steps match the node. I checked that `lean.statement` is verbatim equal to
the theorem signature before `:= by`. The second reader reran the required scompile
wrapper successfully, with no errors or warnings.
