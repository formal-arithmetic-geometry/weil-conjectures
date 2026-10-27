## Worker report

The module `Sheaf.AlgebraicGeometry.TraitLineSectionOrderNormalization` states
`AlgebraicGeometry.Scheme.trait_line_section_order_normalization`, with one `sorry`.
Its eight helpers have complete definitions. They name the canonical uniformizer section,
generic open, special fibre and its projection, the denominator-cleared normalization
relation, the local order condition, global-unit normalization, and evaluation of a
function at a trait's generic point. All nine declarations belong to this node and are
listed in `lean.declarations`; none asserts an extra postponed theorem.

I read the node, all seven statement-dependency nodes and their recorded declarations,
and the statements and records of the proof dependencies. The source was opened in
the primary BLR scan named by the node
(https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf): Neron Models, 4.3, printed page 104, PDF page
110, paragraphs on order at a special-fibre generic point, extension to a frame,
normalizing a unit, and evaluation on an unramified trait. The node's nine-step proof
supplies the extension to equal orders on multiple components and arbitrary traits
with the same uniformizer. The theorem docstring records those nine steps, with their
DAG citations. No statement correction, disputed statement, new node or dependency
repair is needed.

### Hypotheses and conclusions, clause by clause

- A DVR R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Its uniformizer is `(π : R) (hπ : Irreducible π)`.
  Mathlib `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this
  with the specified principal maximal ideal, including nonzero/nonunit conditions.
- Z is `(Z : Scheme.{u})`, with structure map `(f : Z ⟶ Spec (.of R))` and
  `[Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]`. Thus finite type retains
  both clauses of its recorded definition. No separatedness, connectedness,
  nonemptiness, completeness, henselianity or residue-field hypothesis is imposed.
- E and k are canonical rather than extra chosen isomorphic copies: E is the
  fraction field, represented geometrically by the principal open D(pi), and
  k is `R ⧸ IsLocalRing.maximalIdeal R`. `traitGenericOpen f π` is precisely the
  generic fibre as an open subscheme. Indeed every nonzero element of a DVR is a
  unit times a power of π, so E = R[1/π], and base change identifies Z_E with D(pi).
  Sections of L on that open are exactly sections of the restricted line bundle.
  This representation does not assume integral Z or choose a component of Z_E.
- `traitSpecialFiber f` is the actual `pullback f (Spec.map (ofHom
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))`; `traitSpecialFiberι` is
  its first projection. Thus the special fibre is scheme theoretic, with its
  underlying topological space used for components, irreducibility and emptiness.
- Generic points of special-fibre components are exactly those z for which
  `closure ({z} : Set (traitSpecialFiber f)) ∈ irreducibleComponents
  (traitSpecialFiber f)`. No arbitrary list of components or missing component
  can make this condition vacuous. Schemes are sober, so this detects every
  component generic point, including when there are several components.
- `hstalk` explicitly retains the stipulated DVR at each such point: it binds
  `hd : IsDomain (Z.presheaf.stalk (traitSpecialFiberι f z))`, the DVR class for
  that domain structure, and irreducibility of the germ of the canonical π.
  The existential domain witness only supplies the typeclass needed to state
  the DVR hypothesis; it does not replace the stalk by an arbitrary DVR.
- Invertibility is `(L : Z.Modules) [L.IsInvertible]`, the exact recorded
  `Scheme.Modules.IsInvertible`. The section is
  `(s : Γ(L, traitGenericOpen f π))`. `Modules.IsFreeGenerator s` means it
  generates at every point of the generic fibre: on a line bundle,
  stalkwise generation is equivalent to a trivialization on this entire open.
  This uses the existing definition in FreeGenerator.lean, not a private copy.
- For a local frame t over V, `TraitLineSectionNormalizedOn f π L s n V t`
  restricts both sections to V intersect D(pi) and says
  `π^(n.toNat) • t = π^((-n).toNat) • s`, with π also restricted there.
  Since π is a unit on D(pi), this is exactly t = π^(-n) s for EVERY integer n.
  It does not use the meaningless inverse of π at a special point.
- `TraitLineSectionHasOrder ... z n` says there is an open neighborhood V of z
  and a frame t on V satisfying that normalization relation. This is precisely
  BLR's definition that π^(-n) s extends to a generator at z. The equivalent
  localized-stalk description is recovered by taking the germ; conversely a
  generator germ, its inverse coefficient, and the equality in the localization
  have representatives after shrinking a neighborhood. Thus this does not
  assume extension away from a neighborhood of the point.
- The theorem quantifies `∀ n : ℤ` and requires this order n at EVERY component
  generic point. This is exactly the equal-values condition on the integers n_i;
  no order function with extra arbitrary data needs to be supplied.
- Its first conclusion is `∃! t : Γ(L, ⊤), Modules.IsFreeGenerator t ∧
  TraitLineSectionNormalizedOn ... n ⊤ t`: a unique global frame extending
  the prescribed normalized generic section. Restriction to the generic open
  is injective by smooth flatness and π being a nonzerodivisor, so uniqueness
  also holds among all extending sections, whether or not framed in the predicate.
- The empty-special-fibre sentence is contained in that first conclusion:
  with `IsEmpty (traitSpecialFiber f)`, the universal order condition is empty,
  so the conclusion holds for EVERY n without a further assumption. D(pi) = Z
  in this case. In particular Z itself may be empty.
- `IrreducibleSpace (traitSpecialFiber f)` includes nonemptiness, exactly as
  the second part of the node requires. `(a : Γ(Z, traitGenericOpen f π))`
  with `IsUnit a` represents the generic unit without choosing an inverse.
- `TraitUnitNormalization f π a m` says there is b in Γ(Z,O_Z) with `IsUnit b`
  whose restriction is π^(-m) a. Again its actual equality uses positive and
  negative parts of m. The conclusion gives m with this property AND
  `∀ m', TraitUnitNormalization ... m' → m' = m`. In particular uniqueness
  is for normalization alone, not only for normalization bundled with evaluation.
- The evaluation clause quantifies over EVERY `(A : Type u)` with commutative
  ring, domain, DVR and R-algebra structures, requiring exactly
  `Irreducible (algebraMap R A π)`. Thus π is a uniformizer of A and the
  ramification index is one, as required. A is otherwise unrestricted.
- The point is any `(x : Spec (.of A) ⟶ Z)` satisfying
  `x ≫ f = Spec.map (ofHom (algebraMap R A))`, precisely an R-morphism.
  The generic point map is the SPECIFIED composite `Spec.map (ofHom
  (algebraMap A (FractionRing A))) ≫ x`, rather than an arbitrary generic lift.
- The clause asserts existence of h showing that this composite lands in D(pi),
  followed by its valuation equality. This is a conclusion, not an extra
  assumption: the evaluation clause cannot be made vacuous by withholding a lift.
  `traitGenericUnitValue` uses `appLE` and `ΓSpecIso` to pull back a to
  `FractionRing A`. The choice of proof h is immaterial by proof irrelevance.
- The value is `-WithZero.log ((IsDiscreteValuationRing.maximalIdeal A).valuation
  (FractionRing A) (traitGenericUnitValue ...)) = m`. Mathlib's valuation here
  is multiplicative exp(-ord); negative log is the normalized additive valuation,
  giving a uniformizer value one and a unit value zero. The evaluated a is nonzero
  since it is the pullback of a generic unit. Hence no value at zero is being
  mistaken for the normalized valuation of a nonzero element.
- One explicit universe u is shared by schemes and the rings that define them,
  in accordance with Mathlib's category of schemes. No auxiliary universe equality,
  independent smaller test-algebra universe, finiteness on a residue field, or
  restriction on the value or sign of n or m is introduced.

### Dependencies used

Statement dependencies retain their recorded interfaces:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing` and `irreducible_iff_uniformizer` (lines 58--60,
  93--95 read). `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`
  gives `IsDiscreteValuationRing.maximalIdeal`, and its imported
  `HeightOneSpectrum.valuation` on the fraction field supplies normalized values.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`,
  `Spec.map` (full definitions at 42--49, 470--480 read) and `Scheme.ΓSpecIso`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (full affine-local class at 62--65 read).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its imports:
  `LocallyOfFiniteType` (43--46) and `QuasiCompact` (QuasiCompact.lean 43--46).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded
  base-change conventions use `Limits.pullback`, with `pullback.fst` the
  projection to Z and `pullback.snd` the projection to the new base. The entire
  module was read, including `moduleBaseChange` and the fibre comparisons.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, whose complete class
  requires a Zariski neighborhood and trivialization at every point (55--64).
- `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`:
  `Scheme.Modules.IsFreeGenerator` (97--102), already attached to
  `def-sc-local-free-generator`. It is used directly for generating sections.

The plain proof imports retain the stated proof plan: `IsRegularScheme`,
`Algebra.isRegularRing_of_smooth`, `HasRingHomProperty.Spec_iff`,
`Algebra.Smooth.flat`, `Module.Flat.lTensor_preserves_injective_linearMap`,
`Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`,
`Algebra.smooth_fibre_regular_local`, `IsRegularLocalRing.isDomain`,
and `AlgebraicGeometry.tilde` with `tilde.toOpen` and its restriction maps.
Their modules and statements were read from their recorded paths. Affine-stalk
localization is already available through the scheme/affine imports.

### Edge cases checked

For n = 2 the normalization equality is π² t = s; for n = -2 it is t = π² s;
for n = 0 it is t = s. The same sign checks hold for unit normalization. The
special fibre can be empty and Z can be empty, without a Nonempty assumption.
Several special components are permitted and every component is tested. Extra
components lying wholly over the generic point are retained by D(pi); extension
there is already prescribed by s. IrreducibleSpace is used only for the unit
corollary, whose exponent would not be unique on an empty special fibre. Taking
Z = Spec R and a = π^r for any integer r gives m = r and evaluation value r;
a generic unit of order zero has m = 0. The definitions use no affine-intersection
or separatedness condition. The test-trait clause does not restrict characteristic,
completeness or residue fields. All binders are explicit, with autoImplicit false.

### Searches made

All remote searches were run using the prescribed `msearch.py Q92` wrapper:

1. LeanFinder: "A generic frame of an invertible sheaf on a smooth scheme over
   a DVR extends uniquely after scaling by the common order along special fibre
   components". Eight hits: local fraction representation, clearing denominators,
   tilde constants and stalk units. No normalization/extension theorem.
2. Loogle: `Scheme.ord, IsInvertible, IsUnit`. Zero hits; the service reported
   the unknown identifier Scheme.ord. This is not evidence against other names;
   the semantic and text searches supplied the substantive search.
3. LeanSearch: "Invertible sheaf generic section equal orders uniformizer
   extends global frame". Eight hits, including `RingedSpace.isUnit_of_isUnit_germ`,
   `isUnit_res_of_isUnit_germ`, local fraction sections and section extensionality.
   None states extension or equal vertical orders.
4. Mathlib grep: `generic.*frame|vertical.*order|line.section.*order`, restricted
   to AlgebraicGeometry. Zero hits.
5. Local rg of the project's WeilConjectures and Sheaf AlgebraicGeometry modules
   for line sections, generic frames, vertical order and uniformizers found
   related smooth-trait generic-open and Cartier-divisor results, but no exact
   statement. `grep -rn` for the node id in WeilConjectures found no declaration.
6. Local rg for free-generator/generating-section notions found the existing
   `Modules.IsFreeGenerator` and `Modules.GeneratesAt`; their definitions and
   relevant restriction interfaces were read, and the former reused. Local rg
   for valuation conventions found the maximal-ideal adic valuation and
   `-WithZero.log` convention in the DVR valuation characterization modules.
7. Local rg for all nine proposed declaration names across Mathlib,
   WeilConjectures, Sheaf and `dag/lean_names_upstream.json` found no collisions.

### Validation

The prescribed scompile.py compiled the module separately as sandbox and library,
both clean, in 7.5 and 8.6 seconds respectively. One theorem proof is exactly
`sorry`; every helper has actual data or an explicit predicate body. The final
module is checked for 100-character lines and carries source/blueprint docstrings
for all nine declarations. The node copy changes only `lean`, preserving the
accepted statement and split. The required deliver2.py dry run follows.

The deliver2.py dry run printed `OK (dry run): commit 45383a45c21 passes the
preflight and compiles; nothing pushed`. This includes the final proof-plan import
of Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties. The signature in the
node record was checked byte for byte against the theorem header; all Lean lines
have at most 100 characters and the file has exactly one postponed theorem.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
