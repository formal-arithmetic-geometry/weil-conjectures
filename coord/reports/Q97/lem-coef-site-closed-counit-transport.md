## Worker report

This repairs returned head 5ef3debaf55e, points F1–F4. The item statement and all its
non-lean node fields remain unchanged. There are two delivered modules: the item and a
section 1(B) repair of `thm-sf-ambient-adjoint-class`.

`SiteClosedCounitTransport.lean` now states the result for
`C : ComparisonClassAdjunction Λ i c₀ G adj plusEtaleOrigin t.plus`, where
`c₀ = Compactification.ofIsProper i`. Its counit is literally
`(C.homEquiv c₀ _ hJ _ hH).symm (𝟙 _)`, and the general adjunct formula uses that
same `C.homEquiv c₀`. No existential family of Hom bijections remains.

Clause and hypothesis correspondence:

- Global finite-field datum: `D : WeilConjectures.FiniteFieldDatum.{u}`.
- Prime different from the characteristic: `l`, `[Fact l.Prime]`, `_hl : l ≠ D.p`.
- Finite extension and positive coefficient level: `E`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, `n`, `_hn : 1 ≤ n`;
  `Λ := Padic.coefficientExtensionRing l E n`. Its `Finite` instance is explicit,
  and is also supplied by the dependency's recorded positive-level finiteness theorem.
- Separated finite-type k-schemes: `aZ : Z ⟶ Spec (.of D.k)` and `aP` with
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` for both structural maps.
  This is exactly separatedness and finite type, including the quasi-compact clause.
- Closed immersion over k: `i`, `[IsClosedImmersion i]`, `_hi : i ≫ aP = aZ`.
- Comparison functors: local notations `S T = comparisonUpperStar.mapDerivedCategory`
  and `U T = comparisonLowerStar.rightDerivedFunctor`, on the actual small sites.
- Ordinary closed exceptional adjunction: `G` and `adj : F ⊣ G` for
  `F = Etale.rightDerivedLowerShriekOfCompactification A c₀`.
  These are the identity-open compact-support coordinates explicitly stipulated in
  the node: its open factor is `𝟙 Z`, and its proper factor is `i`. The ordinary
  identity-open normalization identifies F with Ri_*; the adjunction comparison to
  any chosen ordinary closed right adjoint is counit compatible. Keeping G and adj
  is exactly the requested C interface, with no second arbitrary adjoint assumption.
- Transported exceptional functor: local notation `J := U P ⋙ G ⋙ S Z`, the
  specified comparison composite, without a separately declared duplicate functor.
- Specified relative adjunction: `C` at exactly c₀, on `plusEtaleOrigin` and `t.plus`.
  Its repaired `homEquiv_normalized` uses the canonical compact-support comparison
  constructed from the named direct-image mate, not an isomorphism chosen from
  a mere Nonempty. This retains step 2 of the node's proof.
- Bounded-below H: `H : DerivedCategory.Plus ...`; bounded-below IH:
  `hIH : t.plus (G.obj H.obj)`. There is no constructibility condition.
- Specified unit and alpha: `α := (S Z).map (G.map
  ((derivedComparisonAdjunction A P).unit.app H.obj))`; `IsIso α` is asserted.
- Delta: `δ L := ((compactSupportSiteComparison Λ c₀).app L).symm`.
  This is the canonical direct-image mate in the identity-open compactification
  coordinates. The comparison definition assembles exact open extension,
  `fixedComparisonDirectImageMatePlus Λ i`, and the specified Plus/ambient
  compatibility isomorphisms; it contains no arbitrary selected comparison.
- The eta isomorphism transports the bounded-below representative G H to J S_P H;
  `hJ` supplies precisely its bounded-below etale-origin property, so the relative
  counit is well typed. Its proof witness is existential, not the Hom bijection.
- Ordinary counit: `adj.counit.app H.obj`. Transported counit E: the inverse image
  of the identity under `C.homEquiv c₀`, with source J S_P H and target S_P H.
- Equation (*): `(δ ⟨G.obj H.obj, hIH⟩).hom ≫ Fpro.map α ≫ E =
  (S P).map (adj.counit.app H.obj)`, with
  `Fpro = rightDerivedLowerShriekOfCompactification A c₀`. Under its canonical
  identity-open normalization this is exactly δ_IH followed by i_* alpha followed
  by E. Keeping the compactification presentation displays the same specified
  C rather than replacing it by an unrelated pushforward adjunction.
- General formula: for every bounded-below L and ordinary morphism f,
  `C.homEquiv c₀ ... ((δ L).inv ≫ (S P).map f) =
  (S Z).map (adj.homEquiv L.obj H.obj f) ≫ α`.

Dependencies used:

- `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`:
  `ComparisonClassAdjunction`, its `homEquiv`, `homEquiv_normalized` and naturality
  fields, and `exists_comparisonClassAdjunction` (repaired in this packet).
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`, `compactSupportSiteComparisonPlus`, using
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus` and `isIso_fixedComparisonDirectImageMatePlus`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit` is a proof dependency for invertibility of alpha.
- The dependency's imports supply `WeilConjectures.FiniteFieldDatum`,
  `Padic.coefficientExtensionRing`, `derivedComparisonAdjunction`,
  `DerivedCategory.plusEtaleOrigin`, `plusEtaleOrigin_mapDerivedCategory_obj`,
  `Compactification.ofIsProper`, and the etale and pro-etale compactification functors.
- The recorded ordinary closed adjoint and finite exceptional construction were read;
  the theorem uses their explicitly stipulated counit-compatible adjunction coordinates.
  The unused imports of `EtaleClosedAmbientAdjoint` and `SfFiniteExceptionalInverseImage`
  have been removed, as requested in F2.

Edge cases: identity closed immersion gives the comparison triangle identity. Empty Z,
zero H, and zero f make the relevant maps zero without excluding any object. Every
positive n is allowed, and no constructibility is imposed. The universes are unchanged:
Schemes are in u, and module coefficients and site values are in u+1. The actual small
pro-etale topology is used; no replacement large or condensed site is substituted.

Repair searches: `rg` for `ComparisonClassAdjunction`, `homEquiv_normalized`,
`fixedComparisonDirectImageMatePlus`, and `compactSupportSiteComparison` in the named
project/source directories found exactly the reusable interfaces above. Inspection of
`FiniteCoefficient.Derived.LowerShriekComparison` with `scompile.py --source` showed
that its old comparison still uses a chosen Nonempty isomorphism; this is why its use
in the recorded C interface needed the canonical replacement. `rg` for the target
name and the original source searches found no existing theorem stating both clauses.

The retained original msearch records are unchanged: LeanFinder query “The etale to
proetale comparison transports the exceptional closed immersion counit using the unit
of full faithfulness and the canonical direct image comparison” returned only generic
comparison/adjunction results; Loogle `CategoryTheory.Adjunction,
CategoryTheory.Functor.FullyFaithful` returned generic restriction lemmas; Mathlib grep
`proetale.*counit|etale.*exceptional|exceptional.*counit` returned zero hits.
Fresh repair searches used the same grep (zero hits), Loogle
`CategoryTheory.Adjunction.homEquiv, CategoryTheory.Adjunction.counit` (12 generic hits,
including homEquiv_symm_id, without any site or normalized relative adjunction), and
LeanFinder “Counit normalization of the closed exceptional adjoint transported from
etale to proetale via the canonical direct image comparison” (eight generic counit
hits, including Condensed.profiniteSolidCounit; no relative site-transport theorem).

No statement dispute or source-based statement correction is required.

## Dependency modules

`thm-sf-ambient-adjoint-class`: the current shared file has already repaired the
legacy/finite-coefficient duplicate imports reported in F1. This delivery retains those
imports and repairs the remaining normalization defect: its old
`homEquiv_normalized` used `rightDerivedLowerShriekOfCompactificationComparisonIso`,
whose proper factor is chosen from Nonempty. It now imports the existing canonical
comparison module and uses `compactSupportSiteComparison Λ c₀`. The structure's other
fields and the existence theorem signature and proof are unchanged. This is the
specified transported adjunction of the node, not a free family of bijections.
Only the dependency node's lean field changes.

## Second reading by Q97

Self-check on this repair, with both node statements and both files open (no additional
agent was started, as required by the dispatcher's instructions): F1's free existential
Hom-bijection was removed, C is fixed at the identity-open compactification, and E is
its inverse image of the identity; both formulae use the same normalized C. The
additional canonical-comparison repair prevents the chosen-comparison problem from
surviving the import fix. F2's duplicate J and unused imports are removed. F3's six
separated/finite-type structural-map instances and over-k equation are explicit. F4's
helpers were eliminated; the sole item declaration has its exact source places,
blueprint tag, and complete four-step proof docstring. The retained dependency's
structure and theorem already have source/blueprint docstrings. No statement or
non-lean node metadata was changed. All binders and the universe u are explicit.

Validation: `deliver2.py Q97 lem-coef-site-closed-counit-transport --no-push`
reported `OK (dry run): commit 1cfda20daf passes the preflight and compiles;
nothing pushed`. This validates both final modules separately in dependency order,
including the shortened docstring and explicit invertibility of alpha. Final metadata
self-check: each copied node differs from the shared node only in lean, each recorded
signature is verbatim, and every Lean line is at most 100 characters.

## Return L verification

The retained packet repairs immutable head 619d1198c780's file-only compilation
failure at `.inv`: delta is defined by taking the component isomorphism first,
`((compactSupportSiteComparison Λ c₀).app L).symm`. Consequently `(δ L).inv`
is the inverse of an Iso, with the source and target required by the general adjunct
formula. The saved Lean work was retained as instructed after the initial dry run
passed; no theorem signature or proof was changed during this verification.

Current-base validation on 2026-10-17 UTC:
`deliver2.py Q97 lem-coef-site-closed-counit-transport --no-push` reported
`OK (dry run): commit 2227c0126d passes the preflight and compiles; nothing pushed`.
Both delivered modules compile separately in dependency order. The signature strings
in both node records occur verbatim in their modules; the maximum line lengths are
92 and 100, respectively, and each theorem retains only `sorry`. The delivery wrapper
preserves the current base's `reviewed_lean` metadata, ignoring the stale sandbox copy.
