## Worker report

The module `lean/Sheaf/CategoryTheory/PresentableCardinalEnlargement.lean` states
`SSet.Presentability.presentable_cardinal_enlargement` with proof `sorry`. The node
statement and proof are unchanged. No new definition nodes or dependency modules were
needed: the statement dependency `def-coef-presentable-infinity-category` has the
recorded module `Sheaf.CategoryTheory.PresentableInfinityCategory`.

Hypothesis and conclusion correspondence:

- The universe parameters `u v`, quasicategory `C : SSet.{max (u + 1) v}`, and
  `[SSet.Quasicategory C]` render the specified infinity category in an ambient universe.
  `hC : IsPresentable.{u, v} C` is exactly the node's presentability hypothesis.
- `S : Set (C _⦋1⦌)` is the small family of arrows, and `[Small.{u} S]` says it is small
  in the smaller universe. For `s : S`, `s.1` is the corresponding edge of `C`.
- The existential cardinals `κ₁ κ₂ : Cardinal.{u}` render the source's `λ < κ` in the
  smaller universe. `κ₁.IsRegular` and `κ₂.IsRegular` give infinite regularity using
  Mathlib's `Cardinal.IsRegular`; `κ₁ < κ₂` is the strict inequality and
  `Cardinal.aleph0 < κ₂` is the required uncountability of the larger cardinal.
- `IsKappaAccessible.{u, max (u + 1) v} C κ₁` and the corresponding clause for `κ₂`
  say that `C` is both accessible at the two ranks.
- `(∀ (μ ν : Cardinal.{u}), μ < κ₂ → ν < κ₁ → μ ^ ν < κ₂)` is the literal cardinal
  power bound for every pair below the two ranks.
- For every edge `s`, the two conjuncts
  `IsKappaCompact ... C κ₂ (C.δ 0 s.1)` and
  `IsKappaCompact ... C κ₂ (C.δ 1 s.1)` state compactness of both endpoints. The
  simplicial face maps are the canonical target/source endpoint maps, so no endpoint
  is selected or omitted.
- The final expression is
  `IsEssentiallySmall` of the full subcomplex
  `SSet.Enhanced.fullSubcomplex C (fun c => IsKappaCompact ... C κ₂ c)`, hence it is
  exactly the full subcategory on all `κ₂`-compact objects, up to equivalence. No chosen
  list of compact objects replaces that full subcategory.

The recorded dependency declaration used is `SSet.Presentability.IsPresentable` and the
same module's `IsKappaAccessible`, `IsKappaCompact`, `IsEssentiallySmall`, and
`SSet.Enhanced.fullSubcomplex` interfaces. I read their full signatures and docstrings;
`IsKappaCompact` includes the filtered-colimit existence and preservation condition, and
`IsKappaAccessible` includes local smallness, filtered colimits, an essentially small
compact full subcategory, and presentations of every object.

Edge cases checked before writing: `S = ∅` makes the endpoint clause vacuous; a one-edge
family checks both faces independently; `C = Δ⁰` checks that the full compact subcategory
is the whole one-object category. The power clause includes `μ = 0` (empty function set
when `ν > 0`) and `μ = ν = 0` (the singleton function set), so no positivity assumption
was silently added. The statement permits arbitrary edge degeneracies, arbitrary
characteristic, and does not assume a nonempty category or a chosen colimit.

Searches made:

- `msearch.py leanfinder` query `presentable infinity category common larger regular
  cardinals small family arrows compact endpoints`: ordinary-category presentability
  hits only; no coherent infinity-category cardinal-enlargement theorem.
- `msearch.py loogle` query `IsPresentable IsKappaAccessible IsKappaCompact Cardinal
  power`: zero hits (`IsPresentable` unknown in the Mathlib namespace).
- `msearch.py grep` query `presentable_cardinal_enlargement|Cardinal.*power.*IsKappaCompact`
  under Mathlib `CategoryTheory`: no hits.
- `rg` over `WeilConjectures` and project `lean/Sheaf` for
  `presentable_cardinal_enlargement|IsKappaAccessible|IsKappaCompact`: only the
  recorded `PresentableInfinityCategory` definitions; no theorem with this statement.
- `grep -rn` for the literal node id in the upstream `WeilConjectures` tree: no result.

No existing declaration has the node's infinity-category statement, so the module is
necessary. No `STATEMENT-DISPUTED` or node fault was found. Validation used the required
`scompile.py` wrapper and compiled the module cleanly; the only permitted warning is the
postponed theorem proof.

## Second reading by Q43

I independently read the sandbox node and module, the recorded dependency node
`def-coef-presentable-infinity-category`, and the entire module
`Sheaf.CategoryTheory.PresentableInfinityCategory`. There is no repair handoff for
this item, no statement correction, and no new node or dependency module in this
delivery. The mathematical statement and its Lean signature are correct unchanged.

The source is HTT, not a Stacks result. I opened the actual Harvard HTT PDF named
by the node, including Proposition the project server, Proposition the project server and its preceding
power condition, Corollary the project server, the cardinal choice in Lemma the project server, and
Definition A.2.6.3 / Remark A.2.6.4. These support accessibility after a suitable
enlargement, closure of compact objects under bounded colimits, and the endpoint
bound. The source's saturation hypothesis belongs to the surrounding localization
application; this cardinal-choice lemma uses only presentability and the small
family. No saturation, minimal-model, finiteness or algebraic hypothesis is needed
here. Source: https://people.math.harvard.edu/~lurie/papers/HTT.pdf.

Here is my object/hypothesis/conclusion checklist, in the order of the node:

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Smaller universe and containing ambient universe | `universe u v`, with `C : SSet.{max (u + 1) v}`. Pass: the small universe is `u`, the ambient one contains it, and `v` is independent. |
| Infinity category C | `[SSet.Quasicategory C]`. Pass: simplicial coherent infinity category, not an ordinary `CategoryTheory.Category`. |
| C is presentable | `hC : IsPresentable.{u, v} C`. Pass: exactly the recorded dependency, accessibility together with all small simplicial colimits. |
| Small set of arrows S in C | `(S : Set (C _⦋1⦌)) [Small.{u} S]`. Pass: arbitrary actual edges, with smallness only on their subtype. No nonempty, cardinal bound on C, or equivalence condition on the arrows. |
| There exist lambda and kappa in the smaller universe | `∃ (κ₁ κ₂ : Cardinal.{u})`. Pass: the witnesses follow C and S and can depend on the entire small family. |
| Both infinite regular | `κ₁.IsRegular ∧ κ₂.IsRegular`. Pass: `Cardinal.IsRegular` includes `aleph0 ≤` (read `Regular.lean:41`). |
| Lambda strictly less than kappa; kappa uncountable | `κ₁ < κ₂ ∧ Cardinal.aleph0 < κ₂`. Pass: neither strict inequality is replaced by a weak one. |
| C accessible at both cardinals | The two `IsKappaAccessible.{u, max (u + 1) v} C κ₁/κ₂` conjuncts. Pass: both refer to the same C and same smaller universe. |
| Every pair mu below kappa, nu below lambda satisfies the power bound | `∀ (μ ν : Cardinal.{u}), μ < κ₂ → ν < κ₁ → μ ^ ν < κ₂`. Pass: universal pair, correct inequalities and exponent order, no positivity restriction. |
| Both endpoints of every member of S are kappa-compact | `∀ (s : S), IsKappaCompact ... C κ₂ (C.δ 0 s.1) ∧ IsKappaCompact ... C κ₂ (C.δ 1 s.1)`. Pass: target is face 0, source is face 1; both are present. |
| Full subcategory of all kappa-compact objects essentially small | `IsEssentiallySmall ... (SSet.Enhanced.fullSubcomplex C (fun c => IsKappaCompact ... C κ₂ c)).toSSet`. Pass: predicate on every vertex, not only generators, endpoints or a selected collection. |

I checked the dependency declarations rather than relying on their names.
`IsKappaCompact` includes existence of filtered colimits and preservation of every
such colimiting coherent cocone by the covariant corepresented space functor;
`IsKappaAccessible` includes local smallness, filtered colimit existence, an
essentially small compact full subcategory and presentations of all objects.
`IsEssentiallySmall` is equivalence to a quasicategory in `SSet.{u}`, via common
universe lifts. I also read the actual `fullSubcomplex` vertex predicate in
`EnhancedDiagramsCones.lean:50`, `IsFunctorEquivalence` there at line 233, and
`Spaces.corepresented` / `Spaces.PreservesColimit` in `InfinityCategoryOfSpaces.lean`.
These are the notions required by the node. They add no instance requirement to
the delivered theorem beyond its displayed quasicategory and small-family
instances. The ambient universe used by compactness grows to accommodate the
space category; no equality of independent universes has been imposed.

Edge cases: the empty S gives a vacuous endpoint quantifier and still yields
both ranks; repeated endpoints and degenerate identity edges are permitted.
For the one-object quasicategory the compact full subcategory is the entire
category, so neither endpoint clause imposes a spurious distinction. The empty
quasicategory is not presentable (it has no empty colimit); no extra nonemptiness
hypothesis is needed. An initial/zero object is treated by the same vertex
predicate, and the empty colimit is allowed. The cardinal quantifier includes
`μ = 0`, `ν = 0`, and `0 ^ 0 = 1`; both witnesses are infinite, and the larger
one is explicitly uncountable. There is no scheme, coefficient ring,
characteristic, or degree n to restrict. Smallness does not require the whole
edge set or the whole category to be small.

Independent searches, with phrasing different from the first reader:

- `msearch.py Q43 lem-coef-presentable-cardinal-enlargement leanfinder`
  with `Quasicategory accessible at a larger regular cardinal with a bounded set
  of compact morphism domains and codomains`: eight hits, all ordinary-category
  accessibility/presentability declarations. No coherent infinity-category theorem.
- The same wrapper with `loogle` and
  `"IsCardinalAccessibleCategory", "exists"`: one hit,
  `Cardinal.SharplyLT.exists_cofinal_of_isCardinalAccessibleCategory_cardinalDirectedPoset`.
  This concerns ordinary directed posets and is not the item.
- The same wrapper with `leansearch` and `A small family of morphisms in a
  presentable infinity category has compact source and target at a common
  sufficiently large accessibility rank`: eight morphism-property/small-object
  hits, none asserting compactness or accessibility inside a quasicategory.
- The wrapper's `grep` for
  `enlarge|common.*cardinal|exists_regular_cardinal_forall` returned unrelated
  topology hits. I separately ran targeted `rg` across Mathlib's Presentable,
  Quasicategory and Cardinal directories, upstream `WeilConjectures`, and the
  project's `lean/Sheaf` for the enlargement name, accessibility with
  quasicategories, compact endpoints, `SharplyLT`, and regular-cardinal bounds.
  Relevant hits were ordinary-category sharpness, the cardinal bound helper,
  and the upstream Serre-cardinal application. No duplicate item was found.
  A literal id/declaration search in upstream, `dag/lean_names_upstream.json`
  and `lean/Sheaf` also found no existing declaration of this item.

To distinguish the semantic hits, I read the pinned
`CategoryTheory/Presentable/LocallyPresentable.lean:35-103`,
`Presentable/Basic.lean:145-152`, and `Presentable/SharplyLT/Basic.lean:45-67`.
These require ordinary category structures and use Hom-set presentability;
they do not replace the dependency's coherent mapping-space predicates.
The set-theoretic bound `HasCardinalLT.exists_regular_cardinal_forall` alone
does not supply the coherent conclusion either. The delivered module remains
necessary; there is no private copy of an existing notion.

Mismatches repaired:

1. H8: the original four-line proof summary omitted the endpoint-presentation
   bound, explicit power-successor choice, bounded compact hull, cofinal poset
   replacement, filtered subset cover, assembly, and compact-stage retract
   argument. I replaced it with all seven proof steps from the node, including
   their cited dependency ids and empty/zero cases. This is documentation only;
   no proof was written, and the only theorem still has proof `by sorry`.
2. Stage 2 import rule: the recorded, landed proof dependency
   `Sheaf.CategoryTheory.DirectedCoverColimitAssembly` was missing. I read its
   signature and added a proof-only `import`. I likewise added a proof-only
   `Mathlib.SetTheory.Cardinal.Regular` import for the recorded Mathlib leaf
   `Cardinal.isRegular_succ`. The cardinal arithmetic leaf is already imported.
   The remaining proof dependency nodes have no Lean module recorded on the
   reviewed base, so there is no module to import for them yet.

I found no H3 statement mismatch, hollow definition, unbound variable/universe,
extra theorem, or need for a statement correction. The node's `lean.statement`
is byte-for-byte the signature in the file, checked after editing; all Lean
lines are at most 100 characters. The required `scompile.py Q43
lem-coef-presentable-cardinal-enlargement
lean/Sheaf/CategoryTheory/PresentableCardinalEnlargement.lean`, run from the
sandbox, exited 0: sandbox check 1.4 s, library-path check 1.6 s, no warnings
or errors. The initial invocation from the read-only repository had only a
relative-path FileNotFoundError; rerunning from the sandbox resolved it.
