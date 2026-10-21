## Worker report

The delivery states `AlgebraicGeometry.Scheme.constant_periodic_resolution_nonzero` in
`Sheaf.Paper.ConstantPeriodicResolutionNonzero`. Its only postponed proof is that theorem.
The unchanged node statement is represented by an existential presentation of its explicitly
specified periodic complex, with term identifications fixing every negative differential and
all components of its augmentation. This avoids postponing any construction's data: no complex,
morphism, coefficient transport, or constant-section function is defined using `sorry` or a
choice from an undetermined existence theorem.

Source read: blueprint `main-20261015`, sec-proetale-coefficients,
`sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md`, paragraph
“The examples”. The DAG extends the displayed Z/ell² example to any exact square-zero divisor;
the scalar calculation in its proof justifies precisely this generalization. The whole item,
all six statement dependencies, and their recorded source declarations were read. The generic
scalar-resolution proof dependency has no Lean record yet and supplies no import; it is not
needed to form this statement. Its later statement can be imported when available.

The hypothesis and clause correspondence is as follows.

- A commutative ring with no nonzero-ring hypothesis is `(R : Type r) [CommRing R]`.
- The element, square-zero hypothesis, and exact-zero-divisor hypothesis are `(t : R)`,
  `ht : t ^ 2 = 0`, and
  `hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)`.
  Membership in this principal ideal is exactly membership in tR.
- The arbitrary scheme is `(V : Scheme.{u})`, independently of `r`.
  Its site and topology are Mathlib's `V.ProEt` and `ProEt.topology V`. The helper
  `constantPeriodicSiteSmall` obtains essential smallness at coefficient size
  `max r (u+1)` from `essentiallySmallSelf`; it adds no hypothesis.
- F is everywhere the literal quotient `R ⧸ Ideal.span ({t} : Set R)`.
  `constantPeriodicModuleFunctor R V` first restricts scalars along the canonical
  equivalence `ULift R ≃+* R`, lifts the module carrier, and applies the constant module
  functor. These are genuine functor compositions. Thus its values on R and F are R_V
  and F_V with the original module and quotient scalar actions. The lift changes only size.
  The resulting coefficient sheaf is the underlying ring sheaf of the constant
  commutative ring sheaf, as required by the recorded K-flat and flatness predicates.
- `constantPeriodicScalar R t V` is the image of the actual linear map
  `LinearMap.mulLeft R t`. `constantPeriodicQuotientMap R t V` is the image of the
  actual quotient linear map `(Ideal.span ({t} : Set R)).mkQ`.
- The first conjunct is the literal equality `kernelSubobject μ = imageSubobject μ`.
- The second gives a cokernel isomorphism to F_V and requires
  `cokernel.π μ ≫ e.hom = constantPeriodicQuotientMap R t V`. This normalizes the
  isomorphism by the specified quotient map; a bare arbitrary isomorphism is insufficient.
- The third conjunct supplies P and identifications `P.X i ≅ C(R)` for every `i ≤ 0`.
  Every `i > 0` has `IsZero (P.X i)`. For every `i < 0` its differential, under those
  identifications, is exactly μ. Because a cochain complex already has zero nonadjacent
  differentials and its positive terms are zero, this specifies every other differential
  as zero too, including the differential from degree zero.
- For every integer i, the same third conjunct asserts the recorded
  `SheafOfModules.IsFlatOnSite (P.X i)` at the independent coefficient size.
- The augmentation goes to the actual single complex
  `(HomologicalComplex.single _ (.up ℤ) 0).obj F_V`. Its degree-zero component, after
  the canonical single-term identification, is the quotient map from the identified
  degree-zero term. Every component away from degree zero is explicitly zero.
  `CochainComplex.IsKFlatResolutionIndependentCoefficients ε` says precisely that this
  augmentation is a quasi-isomorphism and its source is K-flat. Together with the
  kernel/image and normalized cokernel clauses, this is exactness at every position
  of the augmented sequence, including its final surjection.
- The fourth conjunct sends `t • 𝟙 F` through the same constant module functor and
  asserts it is zero: multiplication by the constant scalar t on F_V vanishes.
- The fifth conjunct is conditional on `Nonempty V`. Its function is the actual
  additive sheafification unit of the lifted constant F-module evaluated at
  `op (ProEt.mk (𝟙 V))`, composed with `ULift.up`; its domain is the original F.
  Thus `Function.Injective` is the node's injectivity of F → F_V(V), without any
  connectedness hypothesis.
- The final conjunct is
  `Nontrivial F → Nonempty V → ¬ IsZero F_V`. Nontriviality is not imposed on the
  exactness or resolution clauses. No conclusion is drawn about nonvanishing for empty V.

The existential presentation of P is unique up to the term-identification-preserving
isomorphism: its terms, differentials, and augmentation components are all fixed. It
therefore represents exactly the complex specified in the node, without replacing its
canonical quotient augmentation by an unconstrained map. The proof docstring reproduces
all five steps of the node, including the empty-scheme qualification.

Recorded dependency declarations used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`,
  and `Scheme.ProEt.mk`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatResolutionIndependentCoefficients` and its defining K-flat predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`: the original
  `siteConstantModuleFunctorGeneral`/`siteConstantModulePresheafGeneral` construction,
  retained by public import. Its construction is generalized by sized realization helpers
  in the item module; its landed module and node record are unchanged.
- `Sheaf.CategoryTheory.FiniteTypeConstantExact`:
  `SheafOfModules.strictPerfectConstantSheaf_exact`, imported for proof step 2.
- `Sheaf.CategoryTheory.SiteConstantModuleUnit`:
  `siteConstantModuleUnitSections_locallyBijective`, imported for proof step 4.
  Its original size restriction can be transported for the proof; no such theorem is
  used to manufacture the section map or any other data in the present statement.

Edge cases checked before writing: the zero ring satisfies the hypotheses and the
resolution becomes zero; t=0 forces R=0 under the annihilator hypothesis; Z/4 with t=2
and k[e]/(e²) with t=e are valid nonzero examples; Z/8 with t=4 fails the annihilator
hypothesis and is correctly excluded. Empty V retains every exactness/flatness clause
but triggers neither nonempty conclusion. Disconnected and non-quasicompact V have no
extra restriction. Coefficients may be larger or smaller than the scheme universe.
No statement correction or mathematical dispute is needed.

Searches actually run:

- `msearch.py leanfinder`: “Constant periodic resolution by multiplication by an exact
  square zero divisor on a proetale site is K-flat and nonzero constant quotient”.
  Eight results concerned formal etaleness and smoothness, with no matching resolution.
- `msearch.py loogle`: `constantSheaf, CochainComplex`. The response was zero hits and
  “unknown identifier 'constantSheaf'”; this query was not a successful exhaustive search.
- `msearch.py grep`: `periodic|Periodic`, directory `Algebra/Homology`.
  The only hits were the documentation of `AlternatingConst.lean`, whose complexes have
  alternating identity/zero differentials, not multiplication by this square-zero scalar.
- `rg` over `lean/Sheaf` and `lean/WeilConjectures` for periodic/Periodic and for the item
  id found the existing `SquareZeroPeriodicTensor` module. Its statements compute Tor
  and derived self-tensor and do not state this item's resolution and injective-section
  clauses. It is a consumer, so it is not imported as infrastructure.
- For the dependency repair, `msearch.py leanfinder`: “constant module sheafification
  functor for an essentially small site with independent coefficient universe”.
  Results included condensed-module functors, `SheafOfModules.freeFunctor`, and the
  general `PresheafOfModules.sheafify`; none supplied the required constant functor.
- `msearch.py grep`: `constant.*[Mm]odule|[Mm]odule.*constant`, directory
  `Algebra/Category/ModuleCat`, returned no hits.
- `rg` in the project, upstream declarations and `dag/lean_names_upstream.json` for the
  proposed declaration names returned no collision. The existing
  `constantModuleHomFunctor`/`constantModuleHomUnit` were read in full: they canonically
  transport coefficients but retain the same fixed `max(site universes)` size restriction.
  They therefore cannot be used when r exceeds the site size. Their construction is
  generalized, rather than silently imposing a universe equality.

## H13 return repair

The returned immutable head bff0fb0f19a0 replaced the landed dependency binding and dropped
its General declarations from the dependency inventory. The saved packet's initial dry run
passed (940aae22bee), but that did not resolve the independent H13 finding.

Applied the reviewer's second permitted repair: the sandbox copy of
`def-sf-site-constant-module-functor.json` is byte-identical to the current live node,
including its `module`, `file`, `statement`, `declarations`, attribution and note. The landed
`SiteConstantModuleFunctorGeneral.lean` is not edited. All ten sized helper declarations
are moved into `Sheaf.Paper.ConstantPeriodicResolutionNonzero`, their docstrings carry
`lem-sfb-constant-periodic-resolution-nonzero`, and they are listed in the item's
`lean.declarations`. The separate Sized module is removed from the delivery. No new node
or dependency-module repair is submitted. The helper definitions retain their actual
constant presheaves, module sheafification, canonical ring isomorphism and additive unit.
The theorem signature, six conjuncts, all hypotheses and independent r/u universes are
unchanged from the reviewed packet. This preserves every prior General consumer.

Validation after the move: `scompile.py` exited 0 for both the sandbox name (23.0 s)
and the library module name (18.1 s), without errors or warnings. The theorem signature
matches `lean.statement` verbatim, the only `sorry` is its theorem proof, all 16 declarations
are inventoried, all helper docstrings carry the item id, and Lean lines are at most 100
characters. The dependency JSON was checked byte-for-byte against live; all item fields
other than `lean` match live. No library build or direct repository/Git mutation was run.

## Second reading by O1

The dispatcher forbids starting other agents and delegates independent delivery review to
the maintainer. This section records the worker's final rereading, not a claim that another
agent performed an independent review. With the node and final Lean source open, the six
conjuncts were checked against kernel/image, normalized cokernel, the full periodic resolution,
t-annihilation, injective constants, and conditional nonvanishing. The only initial mismatch
was technical: the existing constant module interfaces forced the coefficient universe to
the site size. The sized helpers now generalize those constructions inside the item module;
the item retains independent r and u. The dependency node record is restored byte-for-byte
to live. The first draft also used the natural-number single complex;
this was corrected to the integer-indexed `HomologicalComplex.single` in degree zero.
The zero cutoff and all other augmentation components were checked explicitly. Every helper
is real Mathlib data and the only sorry is the item's theorem. The item node differs from
live only in `lean`; the dependency node copy is byte-identical to live. The theorem signature is copied verbatim from its module.

Dry-run repair: the first record extraction stopped at a named argument’s `:=`. The item
record now copies the entire signature through the final theorem proof delimiter. No Lean
statement changed.
