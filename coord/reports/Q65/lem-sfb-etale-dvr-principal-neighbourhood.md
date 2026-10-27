## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleDvrPrincipalNeighbourhood` states
`AlgebraicGeometry.exists_etale_dvr_principal_neighbourhood`, with its sole proof
`by sorry`. There are no helper definitions, new nodes, dependency repairs or
statement corrections. Only the item's `lean` field changes. The module's
source and proof docstring follow all seven accepted proof steps.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-Dedekind-etale-extension` (Tag 0AP2), and
`literature/stacks-project/models.tex`,
`lemma-etale-local-at-worst-nodal` (Tag 0CDD), especially the third proof
paragraph choosing a standard open by prime avoidance. The special-fibre
condition is essential: a generic field factor is not a DVR. We use the
closed-point stalk theorem as the node's proof prescribes, rather than the
unqualified last sentence of 0AP2 for a prime on a generic field component.
The item's statement itself needs no correction.

Clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| A discrete valuation ring R | `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`. The last class includes localness, principal ideals and nonzero maximal ideal, so fields are excluded exactly as in the node. |
| Its maximal ideal m_R | `IsLocalRing.maximalIdeal R`. |
| A commutative ring B | `(B : Type u) [CommRing B]`; there is no domain or local-ring assumption on B. |
| A homomorphism φ : R → B | `(φ : R →+* B)`. No independently chosen algebra map is substituted. |
| Spec B → Spec R is étale | `[Etale (Spec.map (CommRingCat.ofHom φ))]`, using the stated morphism itself. |
| A prime ideal q in B | `(q : Ideal B) [q.IsPrime]`. |
| φ⁻¹(q) = m_R | `(hq : q.comap φ = IsLocalRing.maximalIdeal R)`. |
| An element b outside q | `∃ (b : B), b ∉ q ∧ ...`. |
| R′ = B[1/b] is a DVR | The actual type is `Localization.Away b`; existential class witnesses `IsDomain (Localization.Away b)` and `IsDiscreteValuationRing (Localization.Away b)` supply precisely the properties to be concluded. No ring or map is chosen arbitrarily. |
| Its unique maximal ideal is qB[1/b] | `IsLocalRing.maximalIdeal (Localization.Away b) = q.map (algebraMap B (Localization.Away b))`. The DVR class gives localness, hence uniqueness; the equation identifies that unique ideal. |
| R → B → R′ is injective | `Function.Injective ((algebraMap B (Localization.Away b)).comp φ)`. |
| That composite is local, with the specified contraction | `(IsLocalRing.maximalIdeal (Localization.Away b)).comap ((algebraMap B (Localization.Away b)).comp φ) = IsLocalRing.maximalIdeal R`. This is the node's explicit parenthetical definition of localness. |
| The induced Spec R′ → Spec R is étale | `Etale (Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away b)).comp φ)))`. |
| No module-finiteness, excellence, henselianity or completeness | None appears among the binders. |

The common arbitrary universe `u` is the universe of both affine schemes in
Mathlib's scheme-morphism interface. No finite type of underlying elements,
cardinality bound, characteristic, uniformizer or residue-field choice is
imposed. The existential domain witness precedes the DVR witness because
Mathlib's DVR predicate explicitly requires a domain instance.

Statement dependency declarations, read with their signatures and docstrings:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`. Its class extends
  `IsPrincipalIdealRing R` and `IsLocalRing R` with maximal ideal nonzero,
  under `[CommRing R] [IsDomain R]`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`, publicly
  available through `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. Its affine-local ring-map
  definition is the node's recorded interface.
- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`, publicly available through
  `Mathlib.RingTheory.Localization.Away.Basic`, which supplies the ring and
  canonical `algebraMap`.

The plain proof imports cover every recorded proof dependency: `Scheme.Hom.fiber`
(Fiber), the DVR class, `Localization.AtPrime` (AtPrime.Basic), localization away,
`Scheme.etale_trait_stalk` (the upstream Morphisms.EtaleTraitStalk module), affine
stalk localization (AffineScheme), affine quasi-compactness/quasi-separatedness
(AffineScheme and Morphisms.QuasiSeparated), étale composition (Morphisms.Etale),
`Scheme.Hom.etale_fibre_discrete_separable_points` (the upstream
EtaleFibreDiscreteSeparablePoints module), `pullbackSpecIso` (Pullbacks),
`IsLocalRing.notMem_maximalIdeal` (LocalRing.MaximalIdeal.Basic),
`IsLocalization.prime_localRing_residueField_iso` (the upstream
LocalizationPrimeResidueFieldIso module), the localization-away open immersion
(OpenImmersion), and `Ideal.exists_le_maximal` (Ideal.Maximal). No dependency
interface needed replacing. Statement imports already provide some of these
proof dependencies publicly.

Edge cases checked mathematically before writing and on rereading:

- B = R, φ = identity, q = m_R: b = 1 gives the original DVR and all map clauses.
- B = R × R with q the prime on the first component: b = (1,0) selects that DVR.
  Thus the theorem must not assume B is a domain; it does not.
- B = R × Frac(R), with q on the R component: b = (1,0) discards the field factor.
  This also tests that no finiteness as an R-module has been assumed.
- B = Frac(R) and q = (0): the contraction is (0), not m_R, so the hypothesis
  excludes the false DVR conclusion on a generic field factor.
- B the zero ring: there is no prime q; no extra nontriviality assumption is needed.
- If the prime-avoidance indexing set is empty, the proof uses b = 1; the statement
  permits it. Nothing excludes characteristic zero or positive characteristic.

Searches for reuse (2026-10-24), using the prescribed `msearch.py` wrapper:

- LeanFinder: `An etale algebra over a discrete valuation ring has a principal open
  DVR neighbourhood of each prime over the maximal ideal`: eight hits, including
  `Algebra.exists_etale_of_isEtaleAt`, étale locus and localization-span theorems.
  These give an étale principal neighbourhood, not one that is a DVR.
- Loogle: `"IsDiscreteValuationRing", "Etale"`: zero hits.
- Grep, Mathlib/RingTheory:
  `Etale.*IsDiscreteValuationRing|IsDiscreteValuationRing.*Etale|etale.*dedekind`:
  zero hits.
- LeanSearch: `A special fibre prime of an etale algebra over a DVR has a principal
  localization that is a DVR`: eight hits. The Dedekind-domain hits establish that
  a specified prime localization is a DVR, not the requested principal localization;
  `Algebra.exists_etale_of_isEtaleAt` and the localization-away étale instances do
  not assert the DVR conclusion.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `principal.*[Nn]eighbour|[Dd]vr.*[Nn]eighbour|etale_dvr|lem-sfb-etale-dvr-principal-neighbourhood`:
  related local-neighbourhood lemmas and the consumer DvrNodalEtaleLocalForm's
  proof-docstring citation, no matching declaration. A separate DVR search in
  both AlgebraicGeometry directories found the existing trait-stalk declaration,
  whose conclusion is a stalk rather than a principal localization.
- The exact item ID was also searched in `dag/lean_names_upstream.json` (no hit)
  and in `lean/WeilConjectures` (no hit).

Validation: the prescribed `scompile.py Q65
lem-sfb-etale-dvr-principal-neighbourhood <module>` compiled both its sandbox
and final library module forms successfully, with no diagnostics (1.7 s and
1.5 s respectively). All variables and the universe are explicitly bound;
`autoImplicit` and `relaxedAutoImplicit` are disabled. All lines are at most
100 characters. The module has one theorem, whose only proof is `sorry`.

## Second reading by Q65

I reopened the node and the final Lean file and performed this second reading
myself; the dispatcher explicitly forbids starting other agents. This is a
separate rereading, not a claim of an independent reviewer. The maintainer's
independent delivery review remains to follow.

The input has exactly the DVR R, arbitrary commutative B, actual ring map φ,
etaleness of its spectrum map, prime q and the closed-fibre contraction equation.
In particular neither a uniformizer nor a domain structure on B was accidentally
introduced. The conclusion has b outside q, the actual principal localization,
both required DVR class witnesses, its maximal ideal identified with extension
of q, injectivity of the actual composite, contraction of the maximal ideal under
that same composite, and etaleness of the spectrum of that same composite.
The maximal-ideal equation is stated after the existential DVR witness, so it
uses the concluded local structure rather than a new assumption. Uniqueness
comes from that local structure, not an omitted extra assertion. The maps in all
three map clauses use exactly `(algebraMap B (Localization.Away b)).comp φ`.
No mismatch was found; no change to the accepted statement or dependencies was
needed. The proof docstring follows the node's finite-spectrum, explicit product,
localization correspondence, fraction isomorphism, stalk and open-immersion steps.
