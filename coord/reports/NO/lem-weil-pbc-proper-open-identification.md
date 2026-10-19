## Worker report

Recorded existing `AlgebraicGeometry.Etale.properOpenIdentification` in
`Sheaf.AlgebraicGeometry.ProperOpenComparison`; no new module or declaration.
Read the complete signature, docstring and construction in the group checkout and
confirmed the same complete source with `scompile.py --source
Sheaf.AlgebraicGeometry.ProperOpenComparison`. This is the specified isomorphism,
not an assertion of an unspecified isomorphism between the endpoints. The local
variables `r`, `e`, and `c` in its body exhibit both intermediate identifications.

Hypotheses and clauses, matched individually:

- Schemes are `{T₁ T₂ X : Scheme.{u}}`; no finiteness, nonemptiness, or
  Noetherian condition is imposed on them.
- The proper morphism is `(f : T₁ ⟶ T₂) [IsProper f]`.
- The two open immersions are `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)` with the
  corresponding `IsOpenImmersion` instances.
- The compatibility `u j₁ = j₂` is `(h : j₁ ≫ f = j₂)`.
- Finite coefficients are `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Commutativity is precisely the convention in the explicitly cited comparison
  definition; the item's phrase “as in” imports that convention.
- Bounded-below input is `K : DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- `V`, `b`, and `p` are `pullback f j₂`, `pullback.fst f j₂`, and
  `pullback.snd f j₂`. The section is `properOpenSection f j₁ j₂ h`,
  constructed by `pullback.lift j₁ (𝟙 X)` with the given equality.
  `properOpenSectionGeometry` supplies its open immersion, closed image,
  and the Cartesian square used for extension by zero.
- The first identification is the local `e`: the component at `K` of
  `extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2`, followed by the
  image under `s!` of `upperStarIdDerivedPlus`. Its endpoints are exactly
  `b⁻¹ j₁! K` and `s! K`, including the identity inverse-image normalization.
- The second identification is the local `r`: `asIso` of the canonical
  `derivedBaseChangeMapPlus` at `j₁! K` for the chosen pullback square.
  `isIso_derivedBaseChangeMapPlus_of_openImmersion` supplies its invertibility.
  Its endpoints are `j₂⁻¹ Ru_* j₁! K` and `Rp_* b⁻¹ j₁! K`.
- The final identification is local `c`, the component of the characterized
  isomorphism from `clopenSectionDirectImage`, with the closed-image proof
  and the equation `s ≫ p = 𝟙 X` supplied by the pullback construction.
- The result is the actual `Iso` with source
  `(upperStar … j₂).mapDerivedCategoryPlus.obj
  ((rightDerivedLowerStarPlus … f).obj
  ((openImmersionLowerShriek … j₁).mapDerivedCategoryPlus.obj K))`
  and target `K`. Its body is literally `r ≪≫ Rp_*.mapIso e ≪≫ c`.
  Finally `properOpenComparison` is defined using
  `(properOpenIdentification Λ f j₁ j₂ h K).inv`, so this is exactly the
  isomorphism used in the cited comparison, including the specified maps.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.ProperOpenComparison`:
  `AlgebraicGeometry.Etale.properOpenSection`, `properOpenSectionGeometry`,
  `properOpenIdentification`, and `properOpenComparison`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` is the derived category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; the bounded-below
  category is Mathlib's `DerivedCategory.Plus` on that same category.
- `def-weil-pbc-scheme-conventions` explicitly has no declaration or notion
  of its own. The recorded Mathlib scheme/open/proper conventions are the
  ones in the signature. No replacement definition is introduced.

Edge cases checked by reading the binders and construction: empty schemes,
empty open immersions, the identity proper morphism, the zero complex, and
all bounded-below degrees remain allowed. The zero finite commutative ring
is allowed (no `Nontrivial` assumption). The coefficient/site universes are
exactly the established small-etale encoding, with arbitrary scheme universe
`u` and coefficients in `u + 1`. None of the local variables in the existing
construction is an extra hypothesis. No statement correction or disputed
statement is needed. No proof was written or altered.

Searches made on 2026-10-15:

- `msearch.py leanfinder`: “Restriction of derived proper direct image of
  extension by zero along an open immersion is canonically the original
  etale sheaf complex”. Eight hits, headed by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`; all concern
  Zariski modules or ordinary restrictions, rather than this etale composite.
- `msearch.py loogle`: `properOpenIdentification,
  extensionZeroBaseChangeDerivedPlusIso`. Service reports load and asks to
  try later; no usable hit.
- `msearch.py leansearch`: “Canonical isomorphism from restriction of proper
  derived pushforward of extension by zero to the original etale complex”.
  Unavailable: Internal Server Error; no verdict inferred from the outage.
- `msearch.py grep`, Mathlib AlgebraicGeometry:
  `properOpenIdentification|properOpenComparison|extensionByZero`. Zero hits.
- `rg` of the upstream `WeilConjectures` and project `lean/Sheaf` for
  `properOpenIdentification|properOpenComparison|lem-weil-pbc-proper-open-identification`:
  exactly the existing project definition at ProperOpenComparison.lean:67,
  comparison at line 100, and its use of the inverse at line 109; no upstream
  hit. Reading this complete existing definition establishes the match above.

Validation: the prescribed deliver2 dry run checks the existing declaration
with a compiled import/#check probe and runs server preflight. No delivered
Lean file needs compilation because this delivery reuses a published module.
The independent second reader will add their own reading and deliver.

## Second reading by NO

Independently read the item JSON, its six proof steps, its blueprint source
`sec-smooth-purity/sk-def-sf-operations/lem-weil-pbc-proper-open-identification.md`,
the source and current corrected DAG statement of the comparison definition, and
all three statement-dependency records. The item's source place is the blueprint
passage, not a Stacks tag; it imposes no background Noetherian or characteristic
hypothesis. The comparison dependency explicitly fixes finite commutative rings.
Read the complete published `ProperOpenComparison.lean` locally and again through
`scompile.py --source Sheaf.AlgebraicGeometry.ProperOpenComparison`; they agree.

Object/hypothesis/conclusion checklist (all verdicts: matches):

1. Schemes T₁,T₂,X: `{T₁ T₂ X : Scheme.{u}}`, with arbitrary bound `universe u`.
2. Proper u:T₁→T₂: `(f : T₁ ⟶ T₂) [IsProper f]`; f is the node's u.
3. Open j₁,j₂ with common source X: `(j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)` and
   `[IsOpenImmersion j₁] [IsOpenImmersion j₂]`.
4. Commutativity: `(h : j₁ ≫ f = j₂)`, precisely u∘j₁=j₂.
5. Finite coefficients, as in the comparison: `(Λ : Type (u + 1))
   [CommRing Λ] [Finite Λ]`. Commutativity comes from the cited dependency's
   explicit convention, not an added restriction. No invertibility or
   nontriviality condition on Λ.
6. Bounded-below K: `DerivedCategory.Plus (Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} Λ))`. Read `DerivedCategories.lean` and upstream
   `SixFunctors/Etale/Derived/Coefficients.lean`: this is their established
   constant-coefficient étale module-sheaf encoding, not structure-sheaf modules.
7. V,b,p,s: `pullback f j₂`, its `fst` and `snd`, and
   `properOpenSection f j₁ j₂ h`. The last definition is the actual
   `pullback.lift j₁ (𝟙 X) ...`, with the two required projection equations.
   `properOpenSectionGeometry` provides precisely the open immersion, closed
   image and Cartesian square needed here; these are conclusions, not binders.
8. b⁻¹j₁!K ≅ s!K: the body's `e` uses
   `(extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2).app K`, followed by
   s! applied to `upperStarIdDerivedPlus`. Opened the exchange definition:
   it is the inverse canonical adjunction mate localized termwise, with
   exactly the square (id,s,j₁,b), not a bare existential isomorphism.
9. j₂⁻¹Ru_*j₁!K ≅ Rp_*b⁻¹j₁!K: the body's `r` is the component of
   `asIso (derivedBaseChangeMapPlus ... sq.toCommSq)` at j₁!K. Opened
   `DerivedOpenRestriction.lean`: its theorem proves this canonical map
   invertible for arbitrary f and an open a. The chosen square here is the
   actual pullback, so no proper-base-change theorem is smuggled in.
10. Rp_*s!K ≅ K and the specified composite: opened
    `ClopenSectionDirectImage.lean`, including its full characterization
    equation. It determines the component restriction via the derived unit
    and composition/identity comparisons. Its chosen isomorphism is therefore
    determined, not arbitrary data chosen from mere existence. The body's
    `c` uses exactly p,s, closed image, and s≫p=id.
11. θ and its use in the comparison: the definition returns
    `r ≪≫ (rightDerivedLowerStarPlus ... p).mapIso e ≪≫ c`, so its
    actual construction witnesses both intermediate clauses and their specified
    composite. `properOpenComparison` applies j₂! to this very Iso's inverse
    and then the descended counit. Reusing this construction is an exact match;
    an additional existence theorem would duplicate the same notion.

Edge cases: empty X and empty schemes are permitted wherever the morphisms
exist; zero complex, arbitrary negative lower bounds, and degree zero are
included by `DerivedCategory.Plus`. There is no index set or natural-number n
binder to restrict. The zero finite commutative ring is permitted. No field,
Noetherian, finiteness-of-scheme, characteristic or prime-to-characteristic
assumption occurs. Universe u is bound and arbitrary; the u+1 coefficient
and module universes are exactly those of the recorded étale coefficient API.
No unused or unbound variable is introduced in this existing-only delivery.

Independent H4 searches (2026-10-15):

- LeanFinder: “A clopen section of a proper map induces the canonical derived
  restriction isomorphism on etale sheaves”; returned ordinary restriction
  and open-subscheme comparisons, not a second étale derived construction.
- Loogle: `"clopen"`; 12 returned hits are general topological predicates,
  clopen sets and indicator facts, with no étale derived comparison.
- LeanSearch: “Derived direct image of extension by zero along an open closed
  section is the identity”; service Internal Server Error, recorded as
  unavailable, with no mathematical verdict inferred.
- rg across Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  Sheaf/AlgebraicGeometry for `properOpen`, clopen section word orders, and
  the exact component names. Only the published project construction matches
  the whole node; upstream trace-formula clopen pieces are different notions.
  Read the matching definition in full rather than inferring from its name.

No mismatch found and no mathematical statement, dependency, signature, or
module changed. No new nodes or dependency modules. The existing construction
has real composite data; its geometric and invertibility inputs are named
postponed theorems. Nothing was proved or altered here. Existing-only reuse
requires no new module/docstring; the published docstring identifies θ and
all three canonical components. The DAG's six-step proof plan remains intact.
Validation is the prescribed deliver2 import/#check probe and server preflight;
there are no delivered sibling Lean files to compile.
