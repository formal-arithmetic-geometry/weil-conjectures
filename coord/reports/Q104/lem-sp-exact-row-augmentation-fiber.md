## Worker report

The module `Sheaf.Algebra.Homology.ExactRowAugmentationFiber` states
`CochainComplex.ExactRowAugmentation.exactRowAugmentationFiber` with one `sorry`.
The auxiliary definitions contain real data and use Mathlib's cone, shift,
single-complex, short-complex augmentation, and strict cone-map constructions.
There is no new axiom, no chosen arbitrary comparison, no new definition node,
and no change to the node's mathematical statement dependency lists except adding the landed
`def-pur-cochain-coefficient-universe-transport` node, whose `OriginalModules`
and ring-forgetting helper the theorem uses.

Hypotheses and their Lean rendering:

- A site is `{𝒞 : Type uC} [Category.{vC} 𝒞] {J : GrothendieckTopology 𝒞}`.
  The module universe is `max uC vC r`, expressing exactly that the site is
  small relative to the module universe, without identifying its object and
  morphism universes. `r` is arbitrary. The ring universe `s` is independent.
- A commutative ring sheaf is `S : Sheaf J CommRingCat.{s}`. the existing
  `CochainUniverseTransport.liftedRingForgetHasSheafCompose` forgets
  commutativity without changing sections or restriction maps, using
  matching-family limits; no additional size condition is imposed on `s`.
- Module sheaves are `OriginalModules.{uC, vC, s, max uC vC r} S`, the landed transparent
  abbreviation for the dependency's `CategoryTheory.ringedSiteModules`
  over the original ring sheaf with commutativity forgotten. All maps
  `a,d,q,α,β,γ,δ` are morphisms in this existing module category, hence are
  sectionwise S-linear natural maps.
- Exactness of `0 → A → B → C → D → 0` is `[Mono a]`, `[Epi q]`,
  `(ShortComplex.mk a d had).Exact`, `(ShortComplex.mk d q hdq).Exact`.
  The equalities `had : a ≫ d = 0` and `hdq : d ≫ q = 0` are the complex
  equations already entailed by the displayed exact row, not extra conditions.
- `[HasDerivedCategory.{w} (OriginalModules.{uC, vC, s, max uC vC r} S)]` selects the localization
  in the node's chosen morphism universe, precisely the recorded abstract
  derived-category convention. The abelian structure is Mathlib's inherited
  structure on module sheaves, without a second choice of structure.
- The second row has the same four exactness conditions and two zero
  composites, with primes. All four row morphisms and all three commutativity
  conditions are quantified, in the direction from the primed row to the first.
  Composition is written in Lean's left-to-right `≫` convention.

Every clause of the conclusion:

- `singles d q hdq` is the existing short complex of degree-zero single
  complexes. Its first cone is the two-term complex P in degrees -1 and 0.
  `augmentation` is `mappingCone.descShortComplex` on this short complex,
  so it has the given q coordinate and zero on the other cone summand.
- `fiber d q hdq` is literally `(mappingCone (augmentation d q hdq))⟦-1⟧`.
  The projections `toB`, `toC`, `toD` first project out the cone's zero
  summands, and then use `HomologicalComplex.singleObjXSelf`. `IsIso` for
  each projection gives the canonical coordinate identifications. The
  `IsZero` clause covers every other integer degree. The two differential
  equalities identify the differentials with d and -q, including the sign.
- The existential chain map `i` has source the degree-zero single A shifted
  by +1. Its degree -1 component composed with `toB` is exactly a (with the
  canonical single-coordinate identification); all other components are zero.
  Because `toB` is an isomorphism, these equations uniquely determine i.
  Thus the existential is the canonical map described in the node, not an
  unspecified comparison or a weaker arbitrary quasi-isomorphism.
- `QuasiIso i` states that this very chain map is a quasi-isomorphism. The
  derived-category isomorphism e is explicit, with `e.hom = Q.map i`.
  Its source is `Q.obj (A[0]⟦1⟧)`, the standard representative of A[1];
  `Q.CommShift` is part of the recorded dependency's convention.
- For every other exact row, `i'` and `e'` obey the identical normalization.
  They are quantified before the row diagram, so the comparisons do not
  depend on a chosen diagram. Their coordinates also determine them uniquely.
- `twoTermMap` is the strict cone map induced by β,γ. `fiberMap` uses the
  augmentation square proved by the existing `map_descShortComplex`, takes
  the strict cone map with δ, and shifts by -1. Its three coordinate equations
  give exactly β,γ,δ. This construction has no homotopy correction term.
- The chain-map identity is `i' ≫ fiberMap ... = (singleFunctor.map α)⟦1⟧' ≫ i`.
  The final equality is the same naturality square in the derived category,
  using the specified e,e' whose homs are Q(i),Q(i'). Together with the
  universal row and diagram quantifiers, this is naturality for every
  commuting exact-row diagram. Identity and composition are inherited from
  Mathlib's strict `mappingCone.map_id`, `mappingCone.map_comp` and the shift.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the exact recorded general-site module category (its full docstring read).
- `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`,
  `SheafOfModules.CochainUniverseTransport.OriginalModules` and
  `liftedRingForgetHasSheafCompose`: the unchanged original ring and
  module sheaves with independent sizes (full declarations and proofs read).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, its localization and shift
  structures: the recorded abstract derived category (signatures and
  docstrings read; `isIso_Q_map_iff_quasiIso` also inspected).
- `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`,
  `CochainComplex.mappingCone.descShortComplex`, `map_descShortComplex`:
  canonical augmentation and its strict naturality.
- `Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`,
  `CochainComplex.singleFunctor`, `HomologicalComplex.singleObjXSelf`:
  degree-zero sheaves and their coordinate identifications.
- The Mathlib cone and shift implementations, `homotopyCofiber.fstX/sndX`,
  `mappingCone.map`, and their full signatures and surrounding docstrings
  were inspected directly. The cone uses the opposite summand ordering from
  the Stacks display but the same differential after these named projections.

Source check: the current `literature/blueprint/latest` proof of
`sk-lem-sp-tower`, first paragraph, uses the left fiber C_m[1] and its strict
transitions. Stacks `derived.tex`, definition-cone (014E), and `homology.tex`,
definition-shift-cochain (011G) and definition-quasi-isomorphism-cochain
(0115), were read to check the definitions and the double sign. The generic
exact-row result is the node's explicit expansion, not a claimed verbatim
Bhatt–Scholze theorem.

Edge cases checked mathematically before writing: the zero row; A=B=0 with
q the identity (the fiber is acyclic, and its differential really is -q);
a an identity and d=0 (the n=m coefficient specialization); and arbitrary
zero objects in the rows. The universal degree statements include negative
and positive degrees without bounded-index assumptions. In characteristic 2
-q=q, but no step uses characteristic 2. Sheaf epimorphicity, rather than
surjectivity on every object's sections, is required, so the statement does
not silently strengthen the node's sheaf exactness.

Searches made:

- `msearch.py leanfinder`, query "An exact sequence 0 to A to B to C to D to 0
  gives a natural quasi-isomorphism A[1] to Cone([B to C] to D[0])[-1]":
  8 hits. The closest `mappingCone.quasiIso_descShortComplex` concerns a
  short exact sequence of complexes and its cone-to-quotient map. It does
  not state this four-term fiber with its specified coordinates/naturality.
- `msearch.py loogle`, query `CochainComplex.mappingCone, QuasiIso`: 2 hits,
  the same short-exact cone result and an unrelated CM5b factorization.
- `msearch.py grep`, query `mappingCone.*(kernel|quasiIso)|kernel.*mappingCone`
  in `Algebra/Homology`: 4 uses of the short-exact cone result, no match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, and the upstream name
  index for `exactRow`, `ExactRow`, `augmentationFiber`, `AugmentationFiber`,
  four-term/augmentation patterns and the node id: no declaration stating
  this result. The existing Koszul quotient towers were read for how their
  canonical `descShortComplex` augmentations and strict transitions use
  these same Mathlib APIs, without importing or duplicating their notion.

No statement dispute or dependency repair is needed. The only postponed
proof is the theorem named above, whose docstring includes all four proof
steps and the dependency node ids. Compilation and delivery checks are
recorded below when complete.

Validation: `scompile.py Q104 lem-sp-exact-row-augmentation-fiber` passed
for this complete file in both sandbox mode and its intended library module
path, with exit code 0 and no warnings. All variables and universe levels
are explicitly bound; `autoImplicit false` is set. The file has exactly one
`sorry`, in the named theorem, and every line is at most 100 characters.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
