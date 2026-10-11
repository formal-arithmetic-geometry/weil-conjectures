## Worker report

The delivery states `LocalizedModule.graded_localization_exact` in
`Sheaf.Algebra.Module.GradedLocalizationExact`, with proof `sorry`. It adds the full set-valued
fraction definition `LocalizedModule.homogeneousPieceAway` in
`Sheaf.Algebra.Module.LocalizedHomogeneousPiece`. No mathematical theorem is proved, and the
definition has no postponed data or proof obligation. The item's statement is unchanged.

Hypotheses and clauses, in order:

- The commutative ring is `{A : Type u} [CommRing A]`. Its integer-indexed additive subgroup
  decomposition and multiplicative compatibility are `𝓐 : ℤ → AddSubgroup A` and
  `[GradedRing 𝓐]`. Mathlib's `GradedRing` includes `DirectSum.Decomposition` and
  `SetLike.GradedMonoid`; the latter's unit-in-degree-zero property is automatic for a unital
  internally graded ring, so this excludes no case of the node.
- Each of the three modules has its own universe `v₀`, `v₁`, `v₂`, additive commutative group,
  and `Module A` instance. The families `𝓜₀`, `𝓜₁`, `𝓜₂` are integer-indexed additive subgroups.
  Their `DirectSum.Decomposition` instances render the direct sums, and
  `SetLike.GradedSMul 𝓐 (𝓜ⱼ i)` renders `A_a M_b ⊆ M_(a+b)`.
- `s : A`, `d : ℤ`, `hd : 0 ≤ d`, and `hs : s ∈ 𝓐 d` are precisely homogeneity and
  nonnegative degree. No positivity, injectivity of multiplication, or domain assumption is used.
- `f i` and `g i` are `A`-linear maps. `hf` and `hg` say, for every integer `n` and element
  `x` of the corresponding piece, that its image belongs to the piece with that same `n`.
- `hex : ∀ i, Function.Exact (f i) (g i)` is image equals kernel at the middle module.
  `Function.Exact` means `g y = 0 ↔ ∃ x, f x = y`, without injection or surjection at the ends.
- `LocalizedModule.Away s M` is exactly localization at powers of `s`, the declaration
  recorded by `def-weil-pbc-module-localization-away`. The new definition uses this type and
  `LocalizedModule.mk m ⟨s^k, ⟨k, rfl⟩⟩`, so denominators and fraction equality are Mathlib's.
- `homogeneousPieceAway 𝓜 s d n` consists precisely of fractions whose numerator has degree
  `n + k*d`. Solving `n = e - k*d` gives the node's grading convention. At `n = 0` this is
  exactly the elements `m/s^k` with `m ∈ M_(kd)`. The set presentation avoids requiring a
  new additive-group instance to express image/kernel exactness. Under the stated grading
  hypotheses these sets are additive subgroups: take a common denominator for sums, use
  graded scalar multiplication for the numerator, and negate numerators for negatives.
- The local `let fₛ` and `let gₛ` use `IsLocalizedModule.map` at `Submonoid.powers s`, with
  the canonical `mkLinearMap`s. Reading its definition and `map_mk'` confirms that these are
  `m/s^k ↦ f(m)/s^k`, respectively `g(m)/s^k`.
- The first conclusion is `Function.Exact fₛ gₛ`, exactness of the whole localized triple.
  The next two conclusions, `∀ n, Set.MapsTo ...`, explicitly express degree preservation
  and hence the availability of restrictions to degree zero.
- The final conclusion is, for every `y` in the middle degree-zero set,
  `gₛ y = 0 ↔ ∃ x ∈` the first degree-zero set, `fₛ x = y`. Together with the MapsTo clauses,
  this is exactly image equals kernel for the two restricted maps, without extra conditions.
- `I : Type w` is an arbitrary set of positions of adjacent triples. `I = Unit` gives the
  single triple in the node. For an exact sequence take the triples at its positions;
  the theorem returns all their localized and degree-zero exactness assertions. Thus the
  finite/infinite consequence is rendered directly by `∀ i`, with no finiteness or cardinal
  bound on `I` and no countability assumption. Endpoint conditions can be represented by
  the adjacent zero module, as usual. Empty `I` is allowed.

Dependency declarations read and used: `def-weil-pbc-module-localization-away` is a Mathlib
leaf and therefore has no `lean` record. Its `mathlib_match` names `LocalizedModule.Away`
(`Mathlib.Algebra.Module.LocalizedModule.Basic`, lines 1472–1478), the protected abbrev for
`LocalizedModule (Submonoid.powers s) M`. The same module supplies `LocalizedModule.mk`,
`mkLinearMap`, and `IsLocalizedModule.map`. The new definition node supplies
`LocalizedModule.homogeneousPieceAway`. Mathlib's `DirectSum.Decomposition`, `GradedRing`,
and `SetLike.GradedSMul` were read in full with their docstrings and are reused directly.
The proof docstring records both DAG proof steps and their named localization-exactness tool.

Edge cases checked mathematically: `d = 0` gives numerators in `M_0` for degree-zero fractions;
`k = 0` includes `m/1`; `s = 0` collapses localization and all its homogeneous pieces to the
zero element, so the exactness assertion remains true; nilpotent `s`, zero modules, and the
zero ring also cause no exception. Negative numerator degrees and negative localized degrees
are included using `ℤ`. Taking common denominators preserves degrees even when `d = 0`.
Empty index sets and finite/infinite families are covered. No node fault or
`STATEMENT-DISPUTED` issue was found.

Source read: the local Stacks checkout is not present on this machine, so I opened
https://stacks.math.columbia.edu/tag/09MR . Its proof forms the localized degree-zero
Mayer–Vietoris long exact sequences used here. This is the same source and paragraph as the
node; there is no statement correction.

Searches (actual calls are logged in `searches.jsonl`):

- LeanFinder, `exactness of homogeneous localization of graded modules and degree zero
  fractions`: ordinary `LocalizedModule.map_exact`, `IsLocalizedModule.map_exact`,
  `ModuleCat.localizedModule_functor_map_exact` and local exactness criteria; none includes
  graded module pieces.
- Loogle, `GradedModule, LocalizedModule`: no hits, unknown identifier `GradedModule`.
- Mathlib grep, `graded.*localization|degreeZero|map_exact`, under `Algebra/Module`:
  ordinary localization exactness only.
- LeanSearch, `homogeneous degree component of localization of a graded module at powers
  of a homogeneous element`: service returned Internal Server Error; recorded unavailable,
  with no mathematical verdict attributed to it.
- LeanFinder, `homogeneous fractions m divided by s to the k in the localized graded module
  with degree n plus k times d`: `HomogeneousLocalization.Away.mk`, `val_mk` and related
  declarations. Their types concern a graded ring localized as a ring, not an arbitrary
  graded module, so they do not define this notion.
- Mathlib grep, `homogeneous.*(module|fraction)|graded.*localiz|localized.*grade`, under
  `Algebra/Module`: no hits.
- The same conceptual grep in `WeilConjectures/` and `lean/Sheaf` found ring-localization
  and projective-space polynomial-ring material, no module homogeneous-piece definition
  or theorem matching this node. Searching `lem-sc-graded-localization-exact` in upstream
  source returned no declaration; all newly introduced declaration names were also checked
  in Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`, with no collisions.
- DAG grep for homogeneous localization found statements that use it, no defining node for
  arbitrary module pieces. `tools/blueprint_refs.py search 'graded localization'` returned
  `def-pc-proj`, `def-pc-standard-graded-algebra`, and `prop-nagata-rees-localization`,
  all ring-specific. None duplicates the new definition.

Validation: the two modules compiled together on the server in dependency order without
errors or warnings (1.4 seconds). The only theorem proof is `sorry`.

## New nodes

`def-sc-localized-homogeneous-piece` defines the underlying set of degree-`n` fractions
`m/s^k` with `m ∈ M_(n+kd)` in `LocalizedModule.Away s M`. Its source is Stacks Tag 09MR's
Mayer–Vietoris paragraph, the degree-zero parts used there. Its statement is self-contained,
and it cites the existing module-localization-away node. Defining the set for an arbitrary
family of additive subgroups does not assert grading properties without hypotheses; the
item supplies the compatible grading. The Mathlib, source, DAG, and blueprint searches above
found ring homogeneous localization but no definition for arbitrary module pieces. The new
node records those searches and is added to the item's `stmt_deps`; no dependency module or
statement correction is needed.

## Second reading by H1

I independently read the item node, its new dependency node, both Lean modules, and the
citer `lem-sc-invert-s-cohomology-mayer-vietoris-diagram`.

The item node's objects and hypotheses render as follows. The commutative ring and its
integer grading are `{A : Type u} [CommRing A]`, `𝓐 : ℤ → AddSubgroup A`, and
`[GradedRing 𝓐]`; `GradedRing` supplies precisely the direct-sum decomposition and graded
multiplication required by the node. The homogeneous element and degree hypotheses are
`(s : A) (d : ℤ) (hd : 0 ≤ d) (hs : s ∈ 𝓐 d)`. The arbitrary index set is `(I : Type w)`;
the three families of modules are `M₀ M₁ M₂ : I → Type v₀/v₁/v₂`, with the three additive
group and module instance families. Their decompositions and graded scalar actions are the
six `DirectSum.Decomposition` and `SetLike.GradedSMul` binders. The maps are
`f : ∀ i, M₀ i →ₗ[A] M₁ i` and `g : ∀ i, M₁ i →ₗ[A] M₂ i`; `hf` and `hg` are exactly
same-degree preservation, and `hex : ∀ i, Function.Exact (f i) (g i)` is exactly image
of `f` equal to kernel of `g`.

For each `i`, the two `let` bindings use `IsLocalizedModule.map` on powers of `s` and
Mathlib's canonical `mkLinearMap`, so they render the maps `m/s^k ↦ f(m)/s^k` and
`m/s^k ↦ g(m)/s^k`. The first conclusion is `Function.Exact fₛ gₛ`. The next two are
`∀ n, Set.MapsTo` into the corresponding `homogeneousPieceAway` sets, rendering degree
preservation. The final clause is
`∀ y ∈ homogeneousPieceAway ... 0, gₛ y = 0 ↔ ∃ x ∈ homogeneousPieceAway ... 0,
fₛ x = y`, exactly exactness after restriction to degree zero. The outer `∀ i` encodes
the node's termwise finite or infinite consequence; `I = Unit` gives the single triple.
No hypothesis is stronger or missing, and quantifier order is preserved.

The dependency definition renders the node's `P_n(M,s,d)` as the set of all
`LocalizedModule.mk m ⟨s^k, ⟨k, rfl⟩⟩` with `m ∈ 𝓜 (n + (k : ℤ) * d)`. This is the
node's `m/s^k` convention, including degree zero at `n = 0`, and reuses
`LocalizedModule.Away` rather than introducing a private localization notion. Both
modules carry the required source and `(blueprint: ...)` docstrings; the theorem proof is
left as the named `sorry` required at stage 2.

Edge cases checked independently: `I` may be empty or infinite; `I = Unit` gives one
triple. The universes of `A`, the three module families, and `I` are independent. The
cases `d = 0`, `n = 0`, `k = 0`, negative degrees, zero modules, the zero ring, `s = 0`,
and nilpotent `s` are admitted by the binders and set definition. No domain, injectivity,
Noetherian, finiteness, or characteristic assumption is present. The empty and zero cases
therefore remain covered.

Searches were rechecked with `rg` over `lean/Sheaf`, the slopmaster2 source, and Mathlib,
and with the recorded LeanFinder, Loogle, and LeanSearch queries in `searches.jsonl`.
Only generic ungraded localization exactness and ring-only homogeneous localization were
found; no declaration matches arbitrary graded module homogeneous pieces or this theorem.
The Stacks page for Tag 09MR was also read; the node follows the Mayer--Vietoris
localization paragraph identified by the blueprint. No existing declaration was found.

No mismatch was found and no Lean or node correction was needed. The citer
`lem-sc-invert-s-cohomology-mayer-vietoris-diagram` continues to hold: its step invoking
this item asks exactly for termwise exactness after localization and degree-zero extraction.
