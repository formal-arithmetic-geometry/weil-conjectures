## Worker report

The module `Sheaf.RingTheory.NaiveCotangentLocalizeBase` states
`Algebra.naiveCotangent_localize_base`, with proof `sorry`, and constructs the
canonical comparison using existing Mathlib data. The only new definitions
are `Algebra.naiveCotangentLocalizeBaseSquare` and
`Algebra.naiveCotangentLocalizeBaseMap`, the square and chain map explicitly
specified by this node. Both are built from existing maps; neither chooses
unspecified data or postpones a data construction.

The source was read in `literature/stacks-project/algebra.tex`,
`lemma-NL-localize-bottom` (Tag 07BS), including the preceding flat-base-change
lemma and standard-presentation discussion. No statement correction is needed.

Hypotheses and clauses, individually:

- The arbitrary commutative ring is `{A : Type u} [CommRing A]`.
- The multiplicative subset containing one is `S : Submonoid A`.
  Its ring localization is exactly Mathlib's `Localization S`.
- The arbitrary target ring and homomorphism from the localization are
  `(B : Type v) [CommRing B] [Algebra (Localization S) B]`.
- The induced A-algebra structure is `[Algebra A B]` with
  `[IsScalarTower A (Localization S) B]`. This is exactly the requirement that
  its structure map be the displayed composite, not an extra restriction:
  every homomorphism from the localization supplies these compatible
  structures by composition. No other property of A → B is assumed.
- The presentation `P_R = R[x_b | b ∈ B] → B` is
  `(Algebra.Generators.self R B).toExtension`. Its underlying polynomial
  ring, evaluation map and designated section are Mathlib's existing ones;
  the section sends b to `MvPolynomial.X b`.
- Its conormal module and differential module are the existing
  `Extension.Cotangent` and `Extension.CotangentSpace`, namely I/I² and
  `B ⊗[P_R] KaehlerDifferential R P_R`. Its differential is the existing
  `Extension.cotangentComplex`, with `cotangentComplex_mk` giving `[h] ↦ 1 ⊗ dh`.
- Putting this arrow into degree-zero single complexes and taking its
  Mathlib homotopy cofiber gives the two-term cochain complex in degrees
  minus one and zero. Indeed the cone terms are the biproduct of the source
  in degree n+1 and target in degree n; the only nonzero cross differential
  is the given cotangent differential, with positive sign. This is the
  existing cone encoding also used by `IndEtaleNaiveCotangentAcyclic`.
  There is no second implementation of conormal or differential modules.
- The canonical coefficient-localization map fixing x_b is
  `Generators.defaultHom (Generators.self A B)
    (Generators.self (Localization S) B)` followed by `toExtensionHom`.
  Inspection of `defaultHom` shows its variable assignment is
  target-section ∘ identity-B-map ∘ source-value, hence exactly x_b ↦ x_b.
  Its algebra hom therefore sends coefficients through A → Localization S.
- `naiveCotangentLocalizeBaseSquare` uses `Extension.Cotangent.map` and
  `Extension.CotangentSpace.map` of this specified extension hom, and its
  commutativity is the existing `map_comp_cotangentComplex` identity.
  The latter identity is reused by `congrArg`, not reproved or postulated.
- `naiveCotangentLocalizeBaseMap` is the map of the two cones obtained from
  that square through `Functor.mapArrow` and
  `HomologicalComplex.homotopyCofiber.mapArrowHom`. It therefore fixes the
  intended canonical map, including its two component formulas.
- The derived conclusion is
  `IsIso (DerivedCategory.Q.map (naiveCotangentLocalizeBaseMap S B))`.
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} B)]` is the dependency's
  chosen localization-universe parameter, not a mathematical restriction.
- The homotopy conclusion is
  `∃ e : HomotopyEquiv _ _, e.hom = naiveCotangentLocalizeBaseMap S B`.
  Mathlib's `HomotopyEquiv` supplies the reverse chain map and homotopies of
  both composites to the respective identities. Its `Homotopy` has degree
  minus one for the cochain shape. Equality fixes the forward map to the
  canonical one; this is not existence of an unrelated equivalence.
- No injectivity, finite generation, finite presentation, domain,
  nontriviality or exclusion of zero from S occurs in any binder.

Dependencies used, with source declarations inspected:

- `def-weil-pbc-module-localization`: recorded module
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`, together
  with its imported `Localization` and localization algebra structures.
- `def-weil-pbc-smooth-ring-map`: recorded
  `Mathlib.RingTheory.Smooth.Basic`, `Algebra.Smooth`. The part needed here
  is the standard naive-cotangent presentation already given by its imported
  `Mathlib.RingTheory.Extension.Cotangent.Basic`: `Generators.self`,
  `Generators.toExtension`, `Extension.Cotangent`,
  `Extension.CotangentSpace`, and `Extension.cotangentComplex`.
  Smoothness is not assumed. The node's recorded Mathlib-match note already
  identifies this presentation; no interface repair or duplicate is needed.
- `def-weil-pbc-kahler-differentials`: recorded
  `Mathlib.RingTheory.Kaehler.Basic`, `KaehlerDifferential`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
  the existing cotangent differential uses these actual modules.
- `def-weil-pbc-module-tensor-product`: Mathlib match `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with `TensorProduct.lift` and
  `LinearMap.rTensor` in the recorded modules; the existing cotangent-space
  module is precisely this tensor product.
- `def-weil-abstract-derived-category`: recorded
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- Proof-only imports follow the recorded matches:
  `Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial`),
  `Mathlib.RingTheory.Flat.Localization` (`IsLocalization.flat`),
  `Mathlib.RingTheory.Ideal.CotangentBaseChange`
  (`Ideal.tensorCotangentEquiv`, `Ideal.tensorCotangentHom_surjective`), and
  `Mathlib.RingTheory.Kaehler.Polynomial`
  (`KaehlerDifferential.mvPolynomialBasis`). The complete five-step proof
  is in the theorem docstring, including the zero-ring case.

Edge cases checked before writing: S = {1} gives the coefficient comparison
with an identity localization; arbitrary infinite sets of generators are
covered by `Generators.self` without any finiteness binder; noninjective
localization of a ring with zero divisors causes no change in the definitions;
B may be the zero ring. In particular if 0 ∈ S, the localization and any ring
receiving a unital homomorphism from it are zero rings, so the cone has zero
modules and the stated equivalence still holds. The ring and target universes
u and v are independent; the module category uses max u v to accommodate the
actual conormal and tensor modules. All variables and universes are explicit.

Searches for an exact existing statement:

- `msearch.py leanfinder`: “The canonical comparison of naive cotangent
  complexes when localizing the base ring is a homotopy equivalence”. Eight
  hits, headed by `Generators.cotangentCompLocalizationAwayEquiv`, plus
  `tensorH1CotangentOfIsLocalization`. These concern localization of the
  target or individual modules, not this canonical full-complex base map.
- `msearch.py loogle`: `"Cotangent", "IsLocalization"`. Two hits:
  `Algebra.tensorH1CotangentOfIsLocalization` and its toLinearMap lemma.
  Neither states the present result.
- `msearch.py leansearch`: “Localizing the base ring at elements invertible
  in the target preserves the naive cotangent complex”. Eight hits,
  including formally smooth localization and localization of H1 or Kähler
  differentials; no exact full-complex comparison.
- `msearch.py grep`: `cotangent.*local|local.*cotangent` in
  `RingTheory/Extension`. Ten hits, principally target principal-localization
  comparisons in `Cotangent/LocalizationAway.lean`; no exact match.
- `rg` of Mathlib's cotangent source gave the maps and square identity used
  here, and `Generators.defaultHom` gave the desired coefficient map without
  a helper existence theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` checked the new declaration names for clashes.
  A search of the item id in `lean/WeilConjectures` found no declaration.
  Searches for naive cotangent complexes found the existing cone encoding in
  `Sheaf.RingTheory.IndEtaleNaiveCotangentAcyclic`, the component-level
  presentation homotopy equivalences, and general derived cotangent-resolution
  interfaces. None states this canonical base-localization comparison.

Validation: `scompile.py NF lem-sfb-naive-cotangent-localize-base` compiled
both sandbox and module modes successfully, with no errors or warnings.
The first dry run identified a signature-record delimiter mismatch; the node
record now omits `:=`, as the preflight signature reader requires. Direct
public imports of the recorded Kähler and tensor-product modules were also
added before the final dry run. Only the main theorem is postponed; both definitions contain real data and
reuse existing Mathlib identities. The node copy changes only `lean`.

## Second reading by NF

Independent reading by the maintainer's second reader (cc review service,
2026-10-24) of delivery 2997270b; the delivered section only stated that no
second worker reading took place. Node statement as a list, with the Lean:

- Commutative ring A: `{A : Type u} [CommRing A]` — exact.
- Multiplicative subset S, ring localization of def-weil-pbc-module-localization:
  `S : Submonoid A`, `Localization S` — exact (Submonoid = contains 1, closed
  under products; no other condition).
- Ring map S⁻¹A → B, B an A-algebra by composition: `[Algebra (Localization S) B]`
  `[Algebra A B] [IsScalarTower A (Localization S) B]` — exact; the tower is the
  "by composition" clause, not a stronger hypothesis.
- C_{B/R} on P_R = R[x_b | b ∈ B], I_R = ker: `(Generators.self R B).toExtension`
  (Mathlib, the presentation recorded in def-weil-pbc-smooth-ring-map's match:
  `H1Cotangent = (Generators.self R S).toExtension.H1Cotangent`), conormal
  `Extension.Cotangent`, differentials `Extension.CotangentSpace` = B ⊗_{P} Ω_{P/R},
  differential `cotangentComplex` ([h] ↦ 1 ⊗ dh by `cotangentComplex_mk`) —
  exact. Degrees −1,0: `homotopyCofiber` of the degree-0 single map; its terms
  are K^{n+1} ⊞ L^n, so I/I² ⊞ 0 in degree −1, 0 ⊞ Ω in degree 0, differential
  the given map — the two-term complex up to the canonical biproduct-with-zero
  identifications (same encoding as the landed IndEtaleNaiveCotangentAcyclic,
  where `CochainComplex.mappingCone` is a `def` equal to `homotopyCofiber`).
- Coefficient map A[B] → (S⁻¹A)[B], x_b ↦ x_b: `Generators.defaultHom` has
  `val = P'.σ ∘ algebraMap B B ∘ P.val = X ∘ id ∘ id`, i.e. x_b ↦ x_b; its
  `toAlgHom` is aeval on variables over the coefficient map — exact.
- Canonical B-linear chain map: `naiveCotangentLocalizeBaseSquare`
  (`Cotangent.map`, `CotangentSpace.map` of that hom, commutation by Mathlib's
  `map_comp_cotangentComplex`) and `naiveCotangentLocalizeBaseMap`
  (`homotopyCofiber.mapArrowHom` of the single-functor image) — real data, no
  choice, matches the node's two component formulas.
- Isomorphism in D(B): `IsIso (DerivedCategory.Q.map …)` with the dependency's
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} B)]` — exact.
- Homotopy equivalence with chain inverse and homotopies of degree −1:
  `∃ e : HomotopyEquiv _ _, e.hom = naiveCotangentLocalizeBaseMap S B` — the
  forward map is pinned to the canonical one; Mathlib's `Homotopy` for
  `ComplexShape.up ℤ` has components X^i → Y^{i−1} — exact.
- No injectivity, finiteness, nonzero-ring hypothesis: none in the binders.

Edge cases: S = {1}; 0 ∈ S (Localization S = 0, so B = 0, all modules zero,
statement still typed and true); A → S⁻¹A non-injective; infinite B (variable
set arbitrary). Universes: A : u, B : v independent, modules in max u v (the
polynomial ring R[B] lives in max u v), derived-category universe w free.

Source: Stacks algebra.tex, Tag 07BS (lemma-NL-localize-bottom): "Let S ⊂ A be
a multiplicative subset, S⁻¹A → B a ring map; NL_{B/A} → NL_{B/S⁻¹A} is a
homotopy equivalence" — node and Lean agree with it.

One definition per notion: the project's `Algebra.CotangentResolution.Naive.complex`
(Q101, owned by the theorem node lem-trf-lci-naive-cotangent-model, single
universe, Arrow CommRingCat.{u}) is neither a stmt_dep nor typable at
independent universes u, v; the item uses the Mathlib construction recorded by
def-weil-pbc-smooth-ring-map, as the landed ind-étale item does. No new
cotangent-complex definition; no name clash for the three new declarations in
lean/Sheaf, lean/WeilConjectures or the upstream names list. Dependency records
in the snapshot are byte-identical to the live ones; the node copy changes only
`lean`; `lean.statement` is verbatim the file signature.

Changes made: none to the Lean or the node; this section replaces the
dispatcher-wording placeholder.
