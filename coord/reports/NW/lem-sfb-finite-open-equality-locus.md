## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteOpenEqualityLocus` states
`AlgebraicGeometry.finite_open_equality_locus`. Its only theorem has proof `sorry`;
there are no new definitions, auxiliary theorems, dependency modules, or statement changes.

I read the node, all five statement dependencies and their recorded declarations,
and the proof dependencies and their Mathlib matches. I read Stacks Project
`spaces-more-groupoids.tex`, Tag 04PK, `lemma-finite-diagonal`, proof (the construction
of the exceptional closed image and its complement, for scheme test objects).
The existing example Sheaf compact-object module is withdrawn; its node now refers
to `WeilConjectures.CategoryTheory.CompactObject`, whose module header and declaration
I also read.

Hypothesis and clause correspondence:

- Any scheme morphism q:M→T is `{M T : Scheme.{u}} (q : M ⟶ T)`. The explicit universe
  `u` is arbitrary, covering the chosen size bound for every scheme and test scheme.
- The two open subschemes are `(Z₁ Z₂ : M.Opens)`, with their induced scheme structures
  `Z₁.toScheme`, `Z₂.toScheme` and canonical open immersions `Z₁.ι`, `Z₂.ι`.
  This encodes open subschemes by their actual ambient opens and restricted sheaves.
- Finiteness of each restricted map is precisely `[IsFinite (Z₁.ι ≫ q)]` and
  `[IsFinite (Z₂.ι ≫ q)]`. There is no separatedness hypothesis on q.
- The displayed D is written explicitly as
  `q '' ((Z₁ : Set M) \ (Z₂ : Set M)) ∪ q '' ((Z₂ : Set M) \ (Z₁ : Set M))`.
  Applying q to the ambient difference is the same subset of T as applying the
  restricted q_i to the corresponding subset of Z_i, since `Z_i.ι` is inclusion.
- Closedness is the first conjunct `IsClosed (...)` of exactly this union.
- `∃ V : T.Opens, (V : Set T) = (...)ᶜ ∧ ...` gives the specified complement,
  with its open structure, not an arbitrary open satisfying only the later property.
  `V.toScheme` carries the restriction of the structure sheaf and `V.ι` its inclusion.
- For EVERY `(T' : Scheme.{u}) (h : T' ⟶ T)`, the first universal conjunct states
  `Set.range h ⊆ (V : Set T) ↔
  (pullback.fst q h) ⁻¹ᵁ Z₁ = (pullback.fst q h) ⁻¹ᵁ Z₂`.
  The two inverse-image opens are exactly the base-changed open subschemes in
  `pullback q h`: by the fibre-product universal property,
  Z_i×_T T' is the base change of Z_i→M along `pullback.fst q h`.
  Thus equality is equality as ambient open subschemes, not an arbitrary isomorphism
  between the two schemes. `Scheme.Opens.toScheme` uses the ambient restricted sheaf.
- The second universal conjunct states this equality iff
  `∃! k : T' ⟶ V.toScheme, k ≫ V.ι = h`. This is the full representing universal
  property of the inclusion for the stated equality subfunctor of h_T. The unique
  factorization bijections are natural: precomposition preserves their composite
  with V.ι, and uniqueness identifies the resulting factorizations. No extra
  naturality hypothesis or choice of noncanonical maps is being assumed.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and the ambient opens `Scheme.Opens`.
- `def-weil-size-convention`: the recorded metatheoretic convention, realized by
  explicit `universe u` and `Scheme.{u}`, including all test schemes in that bound.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.fst`; existence for schemes from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; canonical open subschemes and inclusions use
  `Scheme.Opens.toScheme` and `Scheme.Opens.ι` in `Mathlib.AlgebraicGeometry.Restrict`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`. I also read `IsIntegralHom` in Morphisms.Integral;
  this theorem needs the finite clause only.

All recorded proof dependencies have Mathlib matches and their modules are imported:
finite closed maps (`IsProper` for finite morphisms, `Scheme.Hom.isClosedMap`, and
`Scheme.Hom.finite_preimage_singleton` in Morphisms.Proper, UniversallyClosed,
QuasiFinite); affine opens (`Scheme.isBasis_affineOpens` in AffineScheme); base change
of open immersions (`isOpenImmersion_stableUnderBaseChange` in OpenImmersion);
arbitrary-subset base-change images (`Scheme.image_preimage_eq_of_isPullback`
in PullbackCarrier); unique open factorization (`IsOpenImmersion.lift`, `lift_fac`,
`lift_uniq` in OpenImmersion). Statement imports are public; proof-only imports are plain.
The theorem docstring gives all four proof steps with their dependency node ids.

Edge cases checked before writing:

- If Z₁=Z₂ then D is empty, V=T, every base-changed pair agrees, and every test
  map factors uniquely through the top open.
- If both opens are empty the same conclusions hold without requiring M or T
  nonempty. If exactly one is empty, V is the complement of that finite map's
  closed image, and the pulled-back open is empty exactly over this complement.
- An empty test scheme has empty image, equal empty pullback opens, and a unique
  map to V. Empty M or T is allowed; no nonemptiness hypotheses occur.
- Nonreduced schemes and arbitrary residue-field extensions are allowed: the
  equality is of open subschemes with the inherited sheaves, and the proof uses
  the scheme fibre-product image identity rather than treating schemes' point
  sets as literal set-theoretic fibre products.
- No separatedness, quasi-separatedness, finite type or quasi-compactness of q
  is assumed. For example, when M is the line with doubled origin and q maps to
  the ordinary line, the two standard affine opens map finitely (isomorphically)
  to T, D is the origin, and V its complement; the stated formula gives this result.

Searches actually run for this delivery:

- `msearch.py` LeanFinder query: "Equality locus of two open subschemes finite over
  a base scheme is open and represents equality after arbitrary base change".
  Eight hits, including `FormallyUnramified.isOpenImmersion_diagonal`,
  `isPullback_opens_inf` and finite pullback projections, none an exact statement.
  I read FormallyUnramified.lean:124–139: it needs a formally unramified morphism
  and describes its diagonal, rather than equality of two relatively finite opens.
- `msearch.py` Loogle query: `"IsFinite", "IsOpenImmersion"`. Zero hits.
- `msearch.py` grep query: `eqLocus|equality.?locus|finite.*opens|opens.*finite`,
  subdirectory AlgebraicGeometry. Twenty-five hits concerning general finiteness,
  affine covers and quasi-finite loci, no exact equality-locus theorem.
- `msearch.py` LeanSearch query: "The equality locus of two open subschemes finite
  over the base is an open subscheme representing equality under base change".
  Eight hits on `Scheme.isoOfEq`, open-immersion range congruences and isomorphisms
  for equal opens; none supplies the asserted relative open equality locus.
- `rg` in both project source trees and `dag/lean_names_upstream.json`, query
  `equality.?[Ll]ocus|finite_open_equality|FiniteOpenEquality|finite.*[Oo]pen.*equal`.
  Relevant hits were the consumer `UnmarkedFiniteOpenPartsSpace`, which needs
  this node, and `FppfCoproductEqualityLocus`, which concerns coproduct sheaves
  rather than two open subschemes finite over a base. No exact existing statement.
- `grep -rn 'lem-sfb-finite-open-equality-locus' lean/WeilConjectures` returned
  no hit. `rg 'finite_open_equality_locus|FiniteOpenEqualityLocus'` in Mathlib,
  WeilConjectures, Sheaf and the upstream names inventory returned no hit before
  creating this module, so the chosen declaration name is new.

Validation: the prescribed `scompile.py` compiled the delivered module against the
published live library cleanly. No warnings, errors, unbound variables, or extra
axioms/definitions were introduced. The theorem proof is intentionally `sorry`.
There are no node faults or statement disputes.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
