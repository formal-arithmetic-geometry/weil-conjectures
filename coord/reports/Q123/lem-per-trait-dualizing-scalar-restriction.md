## Worker report

The module `Sheaf.AlgebraicGeometry.TraitDualizingScalarRestriction` states
`AlgebraicGeometry.Etale.traitDualizing_scalar_restriction`, with `sorry` as its only
proof. Its helper `traitNormalizedDualizing` has real data: the ordinary etale
`dualizingComplex`, derived tensor with the published signed finite Tate sheaf
in degree zero, then `shiftFunctor _ (-2 * e)`. It introduces no alternative
exceptional functor, Tate line, tensor product, scalar map, or restriction functor.

The source was opened as the local ILO PDF, PDF pages 255--258, printed
249--252. Printed p.250 identifies the actual scalar map to the endomorphisms
of K_Y before assuming purity of Y, and reduces detection to a nonempty open.
The item restricts this argument to the complete mixed-characteristic setting
of section 3.7. Its natural-language statement and proof are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Prime l: `(l : ℕ) [Fact l.Prime]`. The coefficient field F_l is
  `ULift.{u + 1} (ZMod l)`, the same field transported to the required coefficient
  universe. There is no condition on l beyond primality and invertibility on R.
- S = Spec R: `(R : Type u) [CommRing R]` and `p : T ⟶ Spec (.of R)`.
  All schemes have universe u; coefficients and module objects have universe u+1,
  exactly as in the recorded ordinary etale category.
- The node's definition of a trait is rendered by `[IsNoetherianRing R]`,
  `[IsDomain R]`, the local structure inherited from
  `[IsStrictlyHenselianLocalRing R]`, `hdim : ringKrullDim R = 1`, and
  `hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal`. Localness is not
  redundantly bound a second time.
- Completeness for the maximal-ideal topology is
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`, which includes separatedness
  and completeness, without adding an arbitrary topology to R.
- Strict henselianity is the existing `IsStrictlyHenselianLocalRing R`.
  Its superclass is `HenselianLocalRing R` and its remaining field is
  `IsSepClosed (IsLocalRing.ResidueField R)`. This is the source's monic
  simple-root lifting condition and separably closed residue field.
- Mixed characteristic is `[CharZero R]` together with
  `hmixed : 0 < ringChar (IsLocalRing.ResidueField R)`. For a domain, characteristic
  zero of R is equivalent to characteristic zero of its fraction field.
  `hl : IsUnit (l : R)` is precisely invertibility of l on the affine base.
- Integrality of T is `[IsIntegral T]`, including nonemptiness. Regularity is
  `hregular : IsRegularScheme T`, the recorded locally Noetherian plus stalkwise
  regular predicate. No smoothness, flatness, dominance, or purity of T/S is assumed.
- Finite type is `[LocallyOfFiniteType p] [QuasiCompact p]`, as in the recorded node.
- Quasi-projectivity is the displayed existential `hprojective`: an immersion i
  into `ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of R))` over S.
  There are n+1 homogeneous coordinates, so this is P^n_S, including n=0.
  `IsImmersion i` is Mathlib's locally closed immersion predicate. The existing
  `IsQuasiProjective` only applies over fields and cannot be used for this base.
- `[HasCompactification p]` exposes the structural witness needed by the existing
  ordinary exceptional-adjoint definition. It excludes no case: quasi-projectivity
  gives an immersion into proper relative projective space, and
  `HasCompactification.of_isImmersion` constructs a compactification from exactly
  that factorization and the already assumed `QuasiCompact p`. It is not an
  extra compactifiability hypothesis on the schemes covered by the item.
- The integer e is introduced with its defining characterization `hvirtual`.
  Around each x it supplies an open V containing x, a factorization
  `i ≫ q = V.ι ≫ p`, the existing `IsRegularImmersion c i` and
  `SmoothOfRelativeDimension r q`, and `e = (r : ℤ) - (c : ℤ)`.
  This is the local factorization definition in the node, not an arbitrary
  normalization integer or a global factorization assumption. Both r and c may
  be zero; e may be negative. The upstream regular-immersion predicate uses the
  ideal-sheaf kernel and locally weakly regular generating sequences on the
  ambient scheme; at points of the closed subscheme the ideal is proper, giving
  exactly the regular sequences in the dependency. The regular-sequence
  definition itself is not replaced.
- `traitNormalizedDualizing l p e` is exactly K_T. The theorem's first `t.plus`
  clause places it in ordinary D+. The full-subcategory embedding identifies
  its Hom sets with those used in the theorem, so endomorphisms are exactly
  End in D+, with no change to the category of coefficients.
- The first `Function.Bijective` says the actual function `a ↦ a • 𝟙 K_T`
  is bijective. In a coefficient-linear category this is the scalar ring map;
  it preserves 1, addition and multiplication by the module and composition
  laws. Thus this expresses that the specified scalar-action map is an
  isomorphism, rather than existence of an unspecified identification.
- Nonempty open j is quantified as `(j : U ⟶ T) [IsOpenImmersion j] [Nonempty U]`.
  The object j* K_T is the image under the existing ordinary etale
  `(upperStar (ModuleCat ...) j).leftDerivedFunctor`. Its `t.plus` clause makes
  explicit the D+ typing implicit in the node. The following bijectivity clause
  is precisely the second scalar-action isomorphism.
- The universally quantified equality of the pullback of `a • 𝟙 K_T` and
  `a • 𝟙 (j* K_T)` is the identity of A under those two actual scalar
  identifications. `Function.Injective` of that very functor's map on End(K_T)
  states the final injectivity clause, on every endomorphism.
- There is no hypothesis of punctual purity, a pinning, or an invertible Gysin
  class, and no choice of an unconstrained map is used.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (current source read with
  `scompile.py --source`) reexports `AlgebraicGeometry.Etale.DerivedCategoryModule`,
  with `DerivedCategory.Plus`/`DerivedCategory.TStructure.t.plus` from Mathlib.
  `DerivedCategoryModule A T` is the derived category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A)`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`; and the already landed extension
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateSheaf`. The latter's existing definition
  node `def-asd-finite-etale-tate-sheaf` is added to stmt_deps, as permitted for
  an already landed notion. No node is created and no dependency is modified.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  The actual ordinary exceptional adjoint is the existing
  `rightDerivedUpperShriek` of
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`, and its constant image
  is `dualizingComplex` from the sibling `Derived.Dualizing` module.
  These are the ordinary compact-support right adjoints, not pro-etale or
  constructible-only functors.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme = IsLocallyNoetherian ∧ IsRegular`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its quasi-compact imports:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the already existing
  `AlgebraicGeometry.IsRegularImmersion` from
  `WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion` supplies the
  regular closed-immersion condition appearing in hvirtual.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`
  and `IsWeaklyRegular`; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its smooth superclass).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.

All recorded proof-dependency modules available at writing time are imported
without `public`, except statement dependencies already publicly imported.
`lem-per-complete-trait-constructible-biduality` has no Lean record, so there is
no module to import yet; it remains the explicit first proof step. This is a
proof dependency, not a missing notion required to type this statement.
The theorem docstring records all five proof steps and the named inputs,
including the normalization of scalar action by evaluation and restriction.

Edge cases checked before writing: the empty T is excluded exactly by integrality;
the empty U must be excluded since its endomorphism ring is trivial; j = identity
and U = T are included. Dimension-normalization values e=0 and e<0 are included;
local factorization codimension c=0 is included and no positive codimension
assumption is inserted. P^0 is allowed. Vertical schemes over the closed point
are not excluded by dominance or flatness assumptions. l=2 is included when
invertible in R. The coefficient field is nonzero because l is prime. There
is no equality imposed between unrelated universes, and ULift only changes
representation of F_l. Ordinary restriction, not exceptional base change, is
used on the nonempty open.

Searches performed (all returned no exact match for this statement):

- `msearch.py ... leanfinder` with “Scalar endomorphisms of a relative etale
  dualizing complex over a complete strictly henselian trait are detected on any
  nonempty open subscheme”: eight hits, including `Scheme.Etale`,
  `Algebra.IsEtaleAt`, `FormallyUnramified`, and etale-locus lemmas; none concerned
  dualizing endomorphisms.
- `msearch.py ... leansearch` with “scalar endomorphisms dualizing complex etale
  scheme connected restriction”: eight hits about formally etale scalar
  restriction, module sheaf scalar restriction, and linear trace/determinant;
  none states this assertion.
- `msearch.py ... loogle 'dualizingComplex, IsQuasiProjective'`: zero hits,
  unknown identifier `dualizingComplex` in the Mathlib search service.
- `msearch.py ... grep 'dualizing|biduality|virtualRelative'`: ten textual hits,
  in adjunction documentation, homotopy-fiber documentation, order duality, and
  unrelated inner-product duality; no relevant declaration.
- `rg` on the upstream WeilConjectures source for `dualizing`, `virtual`,
  `IsQuasiProjective`, `IsRegularImmersion`, scalar/End, and the item id found
  the reused ordinary dualizing construction, field-only quasi-projectivity,
  and the regular-immersion predicate; the item-id grep had no hits.
- `rg` on the project's `lean/Sheaf` found the existing signed Tate-sheaf and
  regular-scheme modules, with no scalar-endomorphism assertion for the trait.
  The final proposed declaration names have no upstream/project/name-index hits.
- DAG definition searches found the already landed signed twist node; no new
  definition node is needed. `blueprint_refs.py search 'virtual relative dimension'`
  reported zero blueprint-node matches. The local virtual-dimension formula is
  written directly from the existing regular-immersion and smooth predicates.

Validation: scompile.py checked the delivered file separately, as both sandbox
and library module, with no errors or warnings (4.6 seconds in each position
on the final compile before the dry run). All binders and universe variables
are explicit. No statement correction and no STATEMENT-DISPUTED issue.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
