## Worker report

The theorem `AlgebraicGeometry.adicFormalAffine_principal_refinement` in
`Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement` states the entire item as a
conjunction. Its only proof is `sorry`. The helper definition node has real data throughout;
there are no additional postponed theorems. Both delivered files compile with scompile.py
against the live published build, with no errors or warnings apart from permitted sorry warnings.
`set_option autoImplicit false` is enabled in both files.

The source read is formal-spaces.tex, section-formal-schemes-EGA (Tag 0AHY), from the
pseudo-discrete sheaf discussion through the displayed principal-section formula and
 equation-morphisms-affine-formal-schemes (0AHZ). The node's eight proof steps are reproduced
in the theorem docstring, including the completed version of the 01IW argument. The source
explicitly takes the limit in topological rings; the helper therefore supplies the actual
inverse-limit section topology, rather than discarding continuity.

Clause-by-clause translation:

- A commutative Noetherian chart ring is `R : CommRingCat.{u}` with `[IsNoetherianRing R]`.
  Its ideal of definition is `K : Ideal R`, and complete separated means `[IsAdicComplete K R]`.
  Finite generation of K follows from Noetherianity; it is not an extra restriction or omitted
  assumption. The recorded `adicFormalSpec R K` is used, not a replacement formal spectrum.
- The description as a ringed space with inverse-limit structure sheaf is the definition of
  `adicFormalSpec` through `adicFormalCompletion` and `adicThickeningDiagram` in the landed
  module `AdicFormalGeometry`. Mathlib ringed-space colimits take the colimit topology and
  the inverse limit of pushed-forward structure sheaves. The zeroth term is the empty
  scheme and does not affect this colimit; positive powers give the same formal spectrum.
- The points and topology are asserted by `e : adicFormalSpec R K ≃ₜ
  {p : PrimeSpectrum R // K ≤ p.asIdeal}` together with the equality to the canonical
  `adicFormalSpecToSpec` on points. The subtype has exactly the subspace topology.
- `adicCompletedAway R K s` is exactly `AdicCompletion (K.map (algebraMap R
  (Localization.Away s))) (Localization.Away s)`. The equivalence to the inverse limit
  uses `adicLocalizedQuotientTower` with positive levels `(R/K^(n+1))_s`, a ring equivalence,
  the homeomorphism to the initial topology of the discrete quotient-localization rings,
  and the formula for every n and every original ring element r. Thus it is the specified
  quotient-localization comparison, not an arbitrary abstract isomorphism.
- The Noetherian and complete conclusions for this ring are the first two conjuncts
  under `∀ s : R`; the extended ideal is `K.map (adicCompletedAwayMap R K s)`.
- The section formula is `∃! e, IsAdicPrincipalSectionComparison R K s e`. The predicate
  requires a homeomorphism and the equation `e.toRingHom.comp
  (adicFormalPrincipalSection R K s) = adicCompletedAwayMap R K s`.
  The map on the right is literally completion composed with ordinary localization.
  Existence and uniqueness express the canonical comparison, without choosing arbitrary data.
- The ringed-space principal-chart assertion is an isomorphism from `adicFormalSpec C (KC)`
  onto the actual restriction to `adicFormalPrincipalOpen R K s`. Its composite with the
  open inclusion satisfies `IsAdicFormalSpectrumMap` for the canonical ring map, including
  continuity of its section maps, its underlying map on prime spectra, and its global map.
- Compatibility with restriction is quantified over every inclusion between two principal
  opens and every pair of the characterized comparison isomorphisms. The unique continuous
  homomorphism ψ extends the original R-map and satisfies the actual restriction square
  `et.toRingHom.comp res = ψ.comp es.toRingHom`.
- Compatibility with continuous ring maps is the last conjunct: all complete Noetherian
  pairs R,K and S,L and every ring map φ continuous for `K.adicTopology`, `L.adicTopology`
  have a unique morphism `F` satisfying `IsAdicFormalSpectrumMap K L φ F`. This condition
  imposes continuity on every section, the prime-map triangle, and the global-section
  equation extending φ. It does not require φ(K) ≤ L. The last conjunct also explicitly supplies the equality identifying the inverse image
  of D(s) with D(φ(s)), and a unique continuous completed-localization map ψ extending φ
  with the square `eS.comp (cast.comp F.app) = ψ.comp eR`. Thus compatibility of the
  principal comparisons with continuous ring maps is stated directly, including the
  necessary open-set transport. Uniqueness expresses identities and composition.
- The locally Noetherian condition is the pointwise cover condition
  `∀ x, ∃ U, x ∈ U ∧ IsAdicFormalAffineOpen X U`, using the recorded affine-open predicate.
  There is no finite-cover restriction on X. Arbitrary affine opens U,V are quantified with
  `IsAdicFormalAffineOpen X U` and `IsAdicFormalAffineOpen X V`. A point neighbourhood is
  `x ∈ N` and `N ≤ U ⊓ V`. The conclusion supplies sections s,t with
  `x ∈ X.basicOpen s`, `X.basicOpen s ≤ N`, and `X.basicOpen s = X.basicOpen t`.
  Mathlib's `RingedSpace.basicOpen` is the invertible-germ locus, the intrinsic principal
  open explained in node proof Step 5. This avoids an arbitrary choice of affine chart.
- For every ideal m with `[m.IsMaximal]`, the first conclusion is `K ≤ m`. For every s
  avoiding m, the theorem gives a maximal n in the actual completed localization, with
  `K.map (adicCompletedAwayMap R K s) ≤ n` (openness), and an equality h saying its
  contraction is m. The induced map is Mathlib's `Localization.localRingHom m n ... h`;
  its `FaithfullyFlat` is the recorded notion. Mathlib
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` gives exactly flatness plus
  surjectivity on prime spectra. There is no excellence, regularity, field or
  characteristic hypothesis anywhere in the statement.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (every ideal finitely generated).
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, the ring structure, and `algebraMap` into the completion.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.Away`,
  `IsLocalization.Away.map` for the quotient tower.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom` with its exact contraction equality.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` and
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `Module.FaithfullyFlat`,
  `RingHom.FaithfullyFlat`, and the equivalence with flatness and surjective Spec map.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `Sheaf.AlgebraicGeometry.AdicFormalGeometry` (def-per-adic-formal-geometry):
  `adicFormalSpec`, `adicFormalCompletion`, `adicThickeningDiagram`,
  `IsAdicFormalAffineOpen`. The full module was read; its canonical thickenings supply
  the actual map to Spec and the inverse-limit projections used by our helper.
- All stated proof-dependency modules are imported: Sites.Limits, ResidueField,
  AffineScheme, Localization.Ideal, AdicCompletion.Completeness, Localization.Submodule,
  WeilConjectures.RingTheory.AdicCompletionNoetherian, Flat.Localization,
  AdicCompletion.AsTensorProduct, Flat.FaithfullyFlat.Algebra, and the flat ring-map
  API through RingHom.FaithfullyFlat. These are proof imports, not new definitions.

Edge cases checked mathematically before writing: K = 0 gives the ordinary affine spectrum
with discrete rings on quasi-compact opens. K = 1 with completeness forces the zero ring,
so the formal spectrum is empty. The zero ring and s = 0 give empty principal opens and
zero section/completion rings; s = 1 gives the entire chart. Nilpotent s and nilpotent K
behave as the quotient formulas prescribe. An empty ambient formal scheme satisfies the
pointwise cover condition vacuously; there is no point in an empty intersection or empty N.
If s belongs to m the local existence assertion is not imposed. No nontriviality, nonempty
cover, finite cover, positive-dimensionality, quasi-excellence or characteristic is assumed.
All ring and site data share the unrestricted universe u; the tower index ℕ is small in it.

Searches performed: msearch leanfinder on formal principal completed localizations returned
ordinary affine basic-open isomorphisms and adic algebra results, no formal statement;
Loogle `"AdicCompletion", "IsLocalization"` returned zero hits. msearch grep for
FormalScheme/formal principal/completed localization in AlgebraicGeometry returned zero.
LeanSearch on formal spectra and quotient-sheaf limits returned Spec and generic limits;
the later section-topology query returned profinite limits and a spectrum localization
lemma, not the needed definition. The exact response records are in the new node's
mathlib_searches. Direct rg in both Lean roots and the upstream name index found no
principal formal-section topology or comparison. The broader DAG definition search found
`def-per-adic-formal-geometry`, so the preliminary duplicate formal-spectrum construction
was removed and its recorded declaration is used. `blueprint_refs.py search 'formal spectrum'`
and `search 'principal formal'` each returned zero blueprint matches; DAG text was searched
separately and read, including def-per-adic-formal-completion and
 def-per-noetherian-adic-formal-system. These concern existing formal spectra and finite
formal schemes, not the missing principal-section/topological comparison data.

There is no statement correction and no STATEMENT-DISPUTED flag. The original item's
natural-language statement is unchanged. Only its lean record and added definition
statement dependencies are delivered. No dependency record is changed.

## New nodes

`def-per-adic-principal-chart-data` defines only the missing canonical map from the recorded
formal spectrum to Spec, principal opens, completed localization and its ring map, the
quotient-localization tower, the inverse-limit topologies, and the two characterization
predicates for the canonical comparisons. Source: Stacks 0AHY and 0AHZ. It reuses
`adicFormalSpec` from the already landed `def-per-adic-formal-geometry`, Mathlib localization,
completion, spectra and ringed-space colimits. Searches in Mathlib, both Lean roots, DAG
node text and the blueprint reverse search found no existing section-topology/comparison
notion. The topology on non-quasi-compact opens is pseudo-discrete before taking the
inverse limit, as the source requires. No arbitrary ring maps, existentially selected
objects, hollow data or proof placeholders are used in these definitions.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
