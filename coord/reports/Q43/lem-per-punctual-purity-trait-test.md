## Worker report

The module states `punctual_purity_of_complete_mixed_trait_test` with a `sorry` proof.
The item's mathematical statement is unchanged. The landed node
`def-per-punctual-purity` is added to `stmt_deps`, and the module imports
`Sheaf.AlgebraicGeometry.PunctualPurity` and uses its `IsPunctuallyPure`.
The four local purity/Kummer definitions have been deleted; only the theorem is delivered.

Source read: ILO Exposé XVI, Definitions 3.2.1 and 3.2.2, Propositions 3.2.3--3.2.5,
printed pp.244--245 (PDF pages 250--251), and §3.7 first paragraph, printed p.254
(PDF page 260). The first paragraph reduces to integral regular quasi-projective flat
schemes over strictly henselian mixed-characteristic traits. Completion invariance
is Proposition 3.2.4; the node's proof explains the additional complete-base reduction.
The source does not require excellence of the arbitrary regular scheme.

Hypothesis and clause correspondence:

- Prime ℓ is `(ℓ : ℕ) (hℓ : ℓ.Prime)`.
- The finite coefficient field is `regularClassCoefficients ℓ 1`, the existing
  `ULift (ZMod (ℓ^1))`; the lift changes only the universe.
- Ordinary small-etale derived categories are `DerivedCategoryModule` and the
  published `DerivedCategory.singleFunctor`, with the existing module-sheaf category.
- Local scheme, residue field and closed-point inclusion are, respectively,
  `Spec (W.presheaf.stalk w)`, `Spec (W.residueField w)` and `Spec.map (W.residue w)`.
- The local dimension is the natural witness `d` with
  `ringKrullDim (W.presheaf.stalk w) = d`. Regular Noetherian local rings have finite
  dimension, so this neither assumes a finite global dimension for W nor excludes
  Noetherian schemes with unbounded local dimensions.
- The imported `IsPunctuallyPureAt` supplies the finite dimension, Noetherian local
  spectrum, regular immersion and invertibility witnesses needed for the actual class.
  These witnesses are intrinsic for regular Noetherian W with ℓ invertible.
- The class family is the published `regularImmersionClasses`, selected from the
  recorded unique normalized class family. `punctualPurityClassMap` realizes its
  level-one, untensored supported Ext class in D+ and transposes it through
  `closedSupportPlusAdjunction`, with the canonical exact-direct-image comparison.
  The predicate is `IsIso` of this specific map, with target twist d and shift 2d.
  The fully faithful inclusion D+ → D preserves and reflects its invertibility.
- Purity at every point is the published `IsPunctuallyPure ℓ hℓ W`, defined as
  `∀ w : W, IsPunctuallyPureAt ℓ hℓ W w`. Nonclosed points remain included.
- A trait is the spectrum of `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's local nonfield PID criterion is equivalent
  to the node's Noetherian local domain, principal maximal ideal and dimension one.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
  Strict henselianity is the upstream `[IsStrictlyHenselianLocalRing R]`, whose
  definition extends `HenselianLocalRing R` and requires separably closed residue field.
- Mixed characteristic is `[CharZero R]` and
  `∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p`. For a domain,
  characteristic zero of R is equivalent to characteristic zero of its fraction field.
- Invertibility of ℓ on the trait is `IsUnit (ℓ : R)`.
- The test scheme has `[IsIntegral V]`, `IsRegularScheme V`, and structure morphism
  `f : V ⟶ Spec (.of R)` with `Flat f`, `LocallyOfFiniteType f`, `QuasiCompact f`.
  `[IsNoetherian V]` is automatic from finite type over the Noetherian affine trait;
  it is explicit to supply the recorded class-calculus instance, without changing
  the mathematical range of test schemes.
- Quasi-projectivity is the explicit existential N and an immersion into
  `ProjectiveSpace (ULift (Fin (N+1))) (Spec (.of R))`, with its equality over the
  trait. This is P^N_S, including N=0, using `IsImmersion` for locally closed immersion.
- The testing conclusion is `IsPunctuallyPure ℓ hℓ V`.
- The arbitrary conclusion quantifies over every `W : Scheme.{u}` with
  `[IsNoetherian W]`, `IsRegularScheme W` and `IsUnit (ℓ : Γ(W, ⊤))`.
  It concludes `IsPunctuallyPure ℓ hℓ W`, with no excellence assumption.

Dependency declarations read and used (the geometric/derived constructions below are
now used through the public import of the owning punctual-purity module):

- `Sheaf.AlgebraicGeometry.PunctualPurity`:
  `AlgebraicGeometry.Etale.IsPunctuallyPure`, `IsPunctuallyPureAt`,
  `punctualPurityClassMap`, `regularImmersionClasses`, `supportedExtPlusHom`;
  the full declarations and docstrings were read from the current shared source.

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  the conjunction of local Noetherianity and the upstream stalkwise `IsRegular`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the ordinary module-derived
  encoding. This source was read through `scompile.py --source` because it was
  absent from the older local source checkout.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `Scheme.finiteEtaleTateTwist`, used through the published `regularClassTwist`.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`:
  `RegularImmersionClassFamily`, `regular_immersion_class_calculus`,
  `regularClassCoefficients`, `regularClassTwist`, and their canonical Ext realization.
  Its current server source was also read with `scompile.py --source`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  together with the existing `QuasiCompact` predicate.

The three proof-dependency imports retained from the reviewed packet are nonpublic:
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` for
`IsRegularLocalRing.isDomain`, and
`Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint` for
`AlgebraicGeometry.etaleSheavesGsetsPoint`, and
`Sheaf.RingTheory.CompleteMixedRegularPairApproximation` for
`RingTheory.exists_complete_mixed_regular_pair_approximation`. These imports are
unchanged as requested by this return. The six-step source-based proof is unchanged
in the theorem docstring. The now-recorded `TransverseGysinLimit` proof dependency
was also inspected; no dependency module or node record is included in this repair.

Searches actually run through msearch.py (recorded in searches.jsonl):

- LeanFinder: “Punctual etale cohomological purity reduces to regular integral flat
  quasi projective schemes over complete strictly henselian mixed characteristic
  traits”: eight generic etale results; none states this reduction.
- Loogle: `"IsDiscreteValuationRing", "IsStrictlyHenselianLocalRing"`: zero hits.
- Mathlib grep in AlgebraicGeometry: `Punctual|punctual|Trait|trait`: zero hits.
- LeanSearch: “punctual cohomological purity at closed point regular local ring”:
  eight hits on local closed points and stalks; no purity criterion or reduction.
- Direct rg of upstream WeilConjectures and lean/Sheaf found Frobenius weight
  predicates named punctually pure, but no punctual *cohomological* purity predicate
  or this trait reduction at the original search time. Searching the item id upstream
  found no declaration. The repair's current shared-source search finds the landed
  `PunctualPurity.lean`, which is now reused as required by the return.
- Blueprint search “punctual purity” returned three weight-theoretic nodes, none
  defining this cohomological condition. The ancestor command identifies
  lem-per-artin-gabber-affine-curve, consistent with the source ancestry.
- Upstream IsQuasiProjective was read: its base must be a field, so the theorem
  uses the node's explicit relative projective-space immersion over the trait.

Edge cases checked: the empty regular scheme satisfies the pointwise conclusion
vacuously; test schemes are nonempty by integrality. Zero-dimensional stalks use
codimension zero and the actual normalized identity class, with no positive-dimension
restriction. N=0 projective space remains included. The equal-characteristic and
prime-field cases of W remain included; only the tests are restricted to mixed
characteristic. ℓ=2 is permitted. The zero ring cannot be a trait because of IsDomain.
No finite bound on the dimensions of all stalks is imposed. Test rings and schemes
share universe u with W, so local rings and approximation rings are not excluded
by an independently smaller universe. Derived coefficient objects use u+1 as required.

No own statement correction was made. The class-calculus dependency's docstring contains
a pre-existing disputed uniqueness argument; this delivery uses its recorded
unique-family statement unchanged.

## Return repair: H4/H12

The return on immutable head `069ea2823082` accepts every mathematical clause but
identifies Q03's first-landed definition as the owner of punctual purity. Before
editing, the retained packet passed the prescribed initial dry run (commit
`2a479ed1c1`). Passing that mechanical gate did not resolve the duplicate notion.

The repair adds only the landed `def-per-punctual-purity` to the item's `stmt_deps`,
imports `Sheaf.AlgebraicGeometry.PunctualPurity`, and deletes
`punctualKummerClasses`, `punctualKummerYonedaMap`, `IsPunctuallyEtalePureAt` and
`IsPunctuallyEtalePure`. Both occurrences in the theorem, in `htest` and the
conclusion, now use `IsPunctuallyPure`. The redundant direct imports of class
calculus, regular schemes and residue fields are removed because the owning module
publicly imports them. The explanatory module prose is updated to name the imported
predicate; the theorem's six-step proof docstring is unchanged. `lean.declarations`
contains only the theorem, and `lean.statement` is its exact revised signature.
No dependency module, definition node or dependency-node record is delivered.
No statement correction is needed: `statement`, `proof` and `proof_deps` are unchanged.

## Second reading by Q43

The repair worker opened the current item node, its complete module and the full
landed punctual-purity module. The duplicate-definition mismatch is repaired by
using the first-landed predicate. Its level-one F_ℓ coefficients, actual unique
normalized supported Kummer class, canonical transpose, local stalk spectrum,
residue quotient, finite local dimension and pointwise isomorphism criterion match
the node's introductory clause. IsIso in D+ is equivalent to IsIso of the same map
in the ordinary derived category through the fully faithful inclusion.

The theorem's remaining signature is unchanged: prime ℓ; all complete strictly
henselian mixed-characteristic DVRs with ℓ a unit; integral regular flat finite-type
V over their spectra; an explicit immersion into relative P^N with its equality
over S; and every regular Noetherian W with ℓ invertible. R, V and W share universe
u. The Noetherian instance for V is automatic over the Noetherian trait. Empty W,
zero-dimensional local rings, N = 0, ℓ = 2, and equal-characteristic W remain
included. No excellence or additional geometric assumption is introduced.
This is the repair author's self-check; the maintainer supplies independent review.

## Validation

The repaired module passed the prescribed `scompile.py` single-file check with no
errors or warnings: sandbox 6.0 s, library 5.9 s. The local structural check compares
the packet with the current shared base: only `lean` and the single authorized
landed-node addition to `stmt_deps` differ. The sole declaration is the theorem,
its recorded signature is verbatim, the only proof is `sorry`, and every Lean line
has at most 100 characters. Final dry-run and delivery results follow from the
normal `deliver2.py` wrapper.

The final dry run passed: `OK (dry run): commit f5fd84fbef passes the preflight
and compiles; nothing pushed`. The staged set is exactly the report, item node and
item module. Delivery uses the unchanged repaired Lean and node packet.
