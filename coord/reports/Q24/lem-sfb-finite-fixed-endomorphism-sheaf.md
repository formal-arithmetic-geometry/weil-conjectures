## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFixedEndomorphismSheaf` states the complete
node in `AlgebraicGeometry.finite_fixed_endomorphism_sheaf`. No mathematical
statement has changed. The only node-field change is `lean`. All mathematical
theorems have `sorry` proofs; all five helper definitions contain actual data.
The second theorem `commonFixedEndomorphism_preimage` is exactly the node's
invariant-open clause, named because defining its section map requires the
proved equality of opens. Its docstring gives its proof. It is a clause of this
node, not an independent missing mathematical prerequisite.

The objects and clauses correspond as follows.

- A commutative ring is `{R : Type u} [CommRing R]`. A finite set is an arbitrary
  `{I : Type v}` with `[Finite I]` on the main theorem. These universes are
  independent. The endomorphisms are `σ : I → R →+* R`. There are no action laws,
  bijectivity hypotheses, nontriviality hypotheses, or finiteness assumptions on R.
- The exact common fixed subring A is `commonFixedSubring σ`, defined as
  `⨅ i, (σ i).eqLocus (RingHom.id R)`. Mathlib's `Subring.mem_iInf` and
  `RingHom.mem_eqLocus` identify membership with `∀ i, σ i r = r`.
- The actual inclusion is `(commonFixedSubring σ).subtype`. The map p is
  `commonFixedSpecMap σ`, namely `Spec.map` of this inclusion, without auxiliary
  maps or choices.
- For every `f : commonFixedSubring σ`, `commonFixedLocalizedInclusion σ f` is
  Mathlib's canonical localization map with source powers of f in A and target
  powers of the same element in R. The first conjunct of the theorem says
  `Function.Injective ...` and that its ring-hom image equals
  `commonFixedSubring (commonFixedLocalizedEndomorphism σ f)`.
- The induced localized endomorphisms are built with `IsLocalization.map` and
  the membership proof that `σ i f = f`. This is the usual fraction map
  `r/f^n ↦ σ i r/f^n`; the two submonoids are powers of the same fixed element.
- For every open T and every i, `commonFixedEndomorphism_preimage` says
  `(Spec.map σ_i) ⁻¹ᵁ (p ⁻¹ᵁ T) = p ⁻¹ᵁ T`, including both directions of
  preservation. `commonFixedSectionEndomorphism` is the actual `.app` of this
  scheme map followed by the structure-presheaf transport along that equality.
  Its type is the required endomorphism of the sections over `p ⁻¹ᵁ T`.
- The theorem provides a genuine `TopCat.Sheaf CommRingCat.{u}` F on Spec A,
  a natural inclusion `ι : F.obj ⟶ p.base _* (Spec R).presheaf`, and a sheaf
  isomorphism `θ : (Spec A).sheaf ≅ F`. For every open, the inclusion is injective
  and its image is precisely the equalizer intersection of the above section
  endomorphisms. This characterizes the literal subring of common fixed sections,
  including its ring operations; naturality of ι gives exactly its inherited
  restriction maps. It is a subobject specification, not an arbitrary sheaf
  without a fixed-sections characterization.
- `θ.hom.hom ≫ ι = p.c` pins the isomorphism to the canonical structure map.
  Since ι is injective on each open and has the stated image, this is precisely
  its corestriction to the fixed sections; there is no unspecified comparison map.
- For each f and each z in A_f, the next conjunct identifies
  `ι_D(θ_D(e_A(z)))` with `e_R(commonFixedLocalizedInclusion σ f z)`.
  Here e_A and e_R are Mathlib `IsLocalization.algEquiv` from the quotient
  localization to affine sections, using the canonical affine section algebras.
  Both are explicitly the existing `Spec.structureSheaf` section types, which
  are definitionally the scheme's section types. The inverse image of D_A(f)
  is definitionally D_R(f) along the subtype inclusion. Thus this conjunct pins
  the principal-open component to precisely the indicated localization map.
- The last conjunct similarly identifies each section endomorphism on D_A(f)
  with `commonFixedLocalizedEndomorphism σ f i` under e_R. Together with the
  range equality, this identifies the fixed-section ring with the fixed subring
  of R_f, rather than merely asserting unrelated ring equivalences.
- All-open restriction compatibility is built into the types: ι is a natural
  transformation and θ is an isomorphism in the sheaf category. Its inverse is
  also natural. This includes all opens, not only the displayed basic opens.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`; actual signatures and
  docstrings read. Also `.app`, `.c`, and the structure-presheaf restriction maps.
- `def-weil-ring-localization-away`: `Mathlib.GroupTheory.MonoidLocalization.Away`,
  `Localization.Away`, together with `IsLocalization.map` from
  `Mathlib.RingTheory.Localization.Defs` and the away interface in
  `Mathlib.RingTheory.Localization.Away.Basic`. The recorded notion is used
  directly, not replaced by a private fraction type.
- `def-weil-locally-ringed-space-morphism`:
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`,
  `LocallyRingedSpace.Hom`, together with its recorded general interfaces
  `RingedSpace` and `PresheafedSpace.Hom`. These are imported publicly; the
  actual scheme morphism's natural transformation is used for the structure map.
- Proof dependency `lem-weil-pbc-affine-open-section-vanishing-prime`:
  Mathlib's `Scheme.evaluation_eq_zero_iff_notMem_basicOpen`,
  `IsAffineOpen.fromSpec_preimage_basicOpen`, `fromSpec_primeIdealOf`,
  `PrimeSpectrum.mem_basicOpen`, `IsAffineOpen.basicOpen`, and
  `IsAffineOpen.isLocalization_basicOpen` in `ResidueField`, `AffineScheme`,
  and `Spectrum.Prime.Topology`. AffineScheme is public because its affine
  localization interfaces are used in the signature; ResidueField is proof-only.
- Proof dependency `lem-weil-pbc-spec-localization-away-basic-open`:
  `PrimeSpectrum.isTopologicalBasis_basic_opens`,
  `localization_away_isOpenEmbedding`, `localization_away_comap_range` in
  `Mathlib.RingTheory.Spectrum.Prime.Topology`, imported proof-only.
- Proof dependency `lem-weil-pbc-sheaf-morphism-on-basis`:
  `TopCat.Sheaf.restrictHomEquivHom`, `extend_hom_app`, `hom_ext`,
  `isIso_iff_isIso_basis`, in `Mathlib.Topology.Sheaves.SheafCondition.Sites`,
  imported proof-only.

The source passages were read in local `literature/stacks-project/schemes.tex`:
`lemma-spec-sheaves` (01HV), particularly sections on D(f), restrictions and
functoriality; `lemma-standard-open-affine` (01I3), including its localization
proof. The finite common-exponent calculation is explicitly the node's
agent-written argument, not attributed to a stronger Stacks statement.

Edge cases checked before writing:

- I empty: the infimum is the top subring; no nonempty instance is required;
  fixed-section and localized-fixed-ring conditions are vacuous, as intended.
- f = 0, and any nilpotent f: both quotient localizations are the zero ring;
  the basic opens are empty, and the section rings are the zero ring. No
  cancellation, domain, reducedness, or nonzero-divisor hypothesis is present.
- R the zero ring: Spec R is empty and the sheaf assertion includes this case.
- f = 1: the localization assertion specializes to the original fixed subring;
  the basic-open formula specializes to the global affine section comparison.
- Genuinely noninvertible endomorphisms: on k[x] use evaluation x ↦ 0; on
  F_2[t,x]/(tx,x²) fix t and send x ↦ 0, then localize at the zero divisor t.
  The finite common exponent removes the killed numerator discrepancy; no
  automorphism or group-action API is used.
- Arbitrary restrictions, including empty opens, are included by the natural
  transformations; independent ring/index universes have not been identified.

Searches for an existing exact statement or reusable notions:

- `msearch.py ... leanfinder`: “Common fixed subrings for finitely many ring
  endomorphisms commute with localization and affine structure sheaves”. Eight
  hits, including `StructureSheaf.normalize_finite_fraction_representation`,
  `StructureSheaf.comap_basicOpen`, affine localization preservation and
  `Γ_restrict_isLocalization`. No full fixed-ring/sheaf result.
- `msearch.py ... loogle`: `IsLocalization.Away.map, RingHom.eqLocus`.
  OK, zero hits for the combined query. Direct source search found the
  individual existing definitions, which the helpers use.
- `msearch.py ... grep` in RingTheory:
  `fixed.*localiz|localiz.*fixed|invariant.*localiz|localiz.*invariant`.
  One hit: OreLocalization/Basic, an unrelated auxiliary addition definition.
- `msearch.py ... leansearch`: “The common fixed subring of finitely many
  endomorphisms of a commutative ring commutes with localization at a fixed
  element”. Eight hits: `FixedPoints.subalgebra` (requires a monoid action),
  localization-stability predicates, `Localization.subalgebra` (requires regular
  denominators), and common-denominator lemmas. None states this node.
- `rg` of the same localization/fixed patterns in both `lean/WeilConjectures`
  and `lean/Sheaf` returned only unrelated fixed-model/derived-localization
  material. `grep -rn` of the exact node id in WeilConjectures returned none.
  Searches for `commonFixedSubring`, `commonFixedSpecMap`, and
  `commonFixedLocalized` in both source trees, Mathlib and
  `dag/lean_names_upstream.json` returned no existing declaration collisions.
- Mathlib source searches for `eqLocus`, `mem_iInf`, `IsLocalization.map`,
  `IsLocalization.Away.map`, `StructureSheaf.comap`, `openAlgebra`,
  `IsLocalization.to_basicOpen`, and `IsLocalization.algEquiv` found the
  actual constructions used. No private copies of their mathematical notions
  were introduced. Helpers here only name the node's specific canonical terms.

No new nodes, dependency repairs, statement corrections, or disputed statements.
The prescribed scompile.py check succeeded for both the sandbox and named library
module with no errors or warnings. Final delivery checks are recorded below.

## Second reading by Q24

This is a separate self-review pass by the dispatcher-started worker, not a claim
of review by another agent. The task explicitly prohibits starting other agents;
the maintainer supplies the independent review after delivery.

I reopened the original node and the complete module and checked the conjunctions.
The ring, finite index type, family without action laws, literal common fixed
subring, and inclusion spectrum map agree. I found that the initial draft exposed
the localization result only as a separate theorem: I moved both its clauses into
the main theorem so the recorded main signature now says the complete node.
I checked that the invariant-open equality is two-sided, that the section map uses
the correct direction of equality transport, and that its proof is a named theorem.
I checked each open's injectivity and fixed-image equality, the sheaf structure,
and the equation forcing θ to be the canonical structure map. I checked the
principal-open formula on every fraction, as well as the localized action formula;
these rule out choosing an unrelated comparison isomorphism. The restriction
clauses follow from the actual natural-transformation and sheaf-isomorphism
types, rather than an assertion for basis members alone. No extra hypotheses were
added. All definitions have real data; both postponed theorems are clauses of
this node and have complete natural-language proof docstrings.
