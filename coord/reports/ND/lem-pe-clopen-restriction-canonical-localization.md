## Worker report

The module `Sheaf.RingTheory.ClopenRestrictionCanonicalLocalization` states
`lem-pe-clopen-restriction-canonical-localization` in two theorems:
`WContractification.ClopenRestriction.canonical_localization` and
`WContractification.ClopenRestriction.restriction_naturality`. Both proofs are `sorry`.
The helpers are the actual constructions appearing in this node, rather than
independent mathematical notions. No new nodes or dependency repairs are needed.
No statement correction or disputed statement is proposed.

Source read: `literature/stacks-project/proetale.tex`, lines 863–878, Tag 097C,
`lemma-construct`, including its proof by the colimit of idempotent localizations;
and the entire current blueprint proof
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` 
`sk-thm-pe-wc-cover/det-pe-wc-cover-second-stage.proof.md`, especially its
Preliminaries. The DAG expands this construction to arbitrary continuous maps into
a profinite space and specifies the canonical maps and local-ring identifications.
The theorem docstrings carry all nine DAG proof steps, in order (steps 1–5 in the
first docstring incorporate DAG steps 1–7, and steps 6–8 incorporate DAG steps 8–9).

Hypotheses and clauses, matched individually:

- A commutative ring is `{R : Type u} [CommRing R]`.
- The profinite space is `{P : Type u} [TopologicalSpace P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]`. The common ambient universe is the
  node's size convention, not a restriction to finite or inhabited spaces.
- The continuous map is `g : C(PrimeSpectrum R, P)`. `PrimeSpectrum R` is the
  underlying Zariski topological space of the recorded `Spec (CommRingCat.of R)`.
- The closed subset is `(Z : Set P) (hZ : IsClosed Z)`. The constructions themselves
  are defined for any subset; closedness is imposed on the assertion using them.
- `Index Z` is the opposite of the subtype of `Clopens P` containing `Z`.
  Thus its objects are exactly the prescribed neighborhoods, and `U ⟶ V` is
  precisely `V ⊆ U`. It lives in `Type u`, so is small in the chosen ambient universe.
- `preimage g U` is the continuous inverse image clopen. `idempotent g U` is the
  value of Mathlib's clopen-idempotent order equivalence on this clopen. The inverse
  equivalence supplies both idempotence and uniqueness with the prescribed basic open.
- `diagram g Z` has object `RestrictClopen (preimage g U)`, which is definitionally
  `Localization.Away (idempotent g U)`. Its arrows are the existing upstream
  `RestrictClopen.map`, given by `IsLocalization.Away.lift` of the base algebra map.
  These are the required unique R-algebra maps, with existence supplied by the
  existing `val_dvd` proof. The diagram's functor-law fields use the existing
  `IsLocalization.algHom_subsingleton`; no mathematical theorem is proved here.
- `algebra g Z` is literally `colimit (diagram g Z)` in `CommAlgCat R`, with its
  actual coprojections `colimit.ι`. No arbitrary ring or colimit witness is chosen.
- The first conjuncts of `canonical_localization` are `Nonempty (Index Z)` and
  `IsFiltered (Index Z)`. For this thin poset category filteredness is exactly
  nonempty directedness; equalization of parallel arrows is automatic.
- `denominators g Z` is constructed as the submonoid closure of the image of the
  neighborhood idempotents. The next conjunct identifies its carrier with that
  exact image. Thus the claimed set itself contains 1 and is closed under products;
  taking closure in the construction does not silently enlarge the asserted set.
- `IsLocalization (denominators g Z) (algebra g Z)` states that the structure map of
  the actual colimit is localization at exactly those denominators.
- The next conjunct supplies `E : algebra g Z ≃ₐ[R] Localization (denominators g Z)`.
  For every neighborhood and every R-algebra map `κ` from its localization to the
  fraction ring it explicitly requires
  `E.toAlgHom.comp (colimit.ι (diagram g Z) U).hom = κ`.
  This characterizes the canonical colimit identification on every leg, not just
  an abstract ring isomorphism. Such maps exist by localization; the composite with
  E also supplies one. Uniqueness follows from the localization universal property.
- `H : PrimeSpectrum (algebra g Z) ≃ₜ (g ⁻¹' Z)` is the requested homeomorphism with
  the subspace topology. Its normalization `(H q).val = PrimeSpectrum.comap ... q`
  ensures it is exactly contraction, not an unspecified homeomorphism.
- For every prime `q`, the local clause supplies the R-algebra equivalence `α`
  from the localization of R at its contraction to `Localization.AtPrime q.asIdeal`.
  The equality `α.toRingHom = Localization.localRingHom ... rfl` fixes the canonical
  map and hence its fraction formula. No assumption of a previously known local
  isomorphism is introduced.
- For `Z ⊆ Z'`, `inclusion h` sends each neighborhood of Z' to the same clopen as
  a neighborhood of Z. `restriction g h` is literally `colimit.pre` along this
  inclusion, i.e. the canonical map obtained by restricting the R_Z cocone.
- The first two conjuncts of `restriction_naturality` give its identity and
  composition laws for all closed subsets and composable inclusions.
- Its third conjunct says contraction along this map followed by contraction to R
  equals the original contraction. Under the normalized homeomorphisms H, this is
  exactly the inclusion `g ⁻¹' Z ⊆ g ⁻¹' Z'`; the smaller-subset membership follows
  from `canonical_localization` for q.
- Its fourth conjunct is the equality of ring maps
  `localRingHom(q',q,restriction) ∘ localRingHom(x,q',λ_Z') = localRingHom(x,q,λ_Z)`.
  Here q' is explicitly the contraction of q. The equality proofs `hx`, `hx'`
  merely allow one to name their common contraction x; they do not assume a local
  isomorphism or any new mathematical condition. Since both maps out of R_x are
  the canonical isomorphisms in the preceding theorem, this commuting equality is
  precisely the assertion that the localized restriction becomes identity on R_x.
  Quantifying over q covers every x with g(x) in Z via H, including arbitrary lifts.

Dependency declarations used, with full signatures and relevant docstrings read:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; underlying points and topology are
  `PrimeSpectrum`.
- `lem-weil-pbc-spec-clopen-idempotent`: the Mathlib match
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` and
  `PrimeSpectrum.isIdempotentElemEquivClopens`, plus its basic-open normalization,
  in `Mathlib.RingTheory.Spectrum.Prime.Topology`.
- `def-weil-ring-localization-away`: `Localization.Away` in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with ring structure and the lift
  in `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-weil-pbc-category-colimit`: `colimit`, `colimit.ι`, `colimit.pre` in
  `Mathlib.CategoryTheory.Limits.HasLimits`, and `IsFiltered`.
- `lem-weil-pbc-ring-localization-universal-property`: `IsLocalization.lift` and
  `IsLocalization.ringHom_ext` in `Mathlib.RingTheory.Localization.Defs`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` and the canonical
  `Localization.localRingHom` in `Mathlib.RingTheory.Localization.AtPrime.Basic`.
- The proof dependency `lem-weil-pbc-profinite-clopen-basis` is
  `isTopologicalBasis_isClopen` / `compact_exists_isClopen_in_isOpen`, in
  `Mathlib.Topology.Separation.Profinite` (plain proof import).
- The proof dependency `lem-weil-pbc-localization-spectrum-embedding` is
  `PrimeSpectrum.localization_comap_isEmbedding` / `localization_comap_range`,
  in the spectrum topology module already publicly imported for statements.
- The proof dependency `lem-weil-pbc-localization-prime-residue-field-iso` is
  `IsLocalization.prime_localRing_residueField_iso`, in
  `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso` (plain proof import).
- The size convention is metatheoretic and rendered by explicit `universe u`.
- Reused construction API: `WContractification.RestrictClopen`, its instances,
  `val_dvd`, and `map` in
  `WeilConjectures.RingTheory.ProEtale.WContractible`, lines 58–98.
  Also `IsLocalization.algHom_subsingleton` from
  `Mathlib.RingTheory.Localization.Basic`. The existing `Restriction.diag` indexes
  clopens of Spec over a connected-component subset; it is not the g-pulled-back
  neighborhood index prescribed here. The pieces and their maps are reused,
  rather than replaced with private localization definitions.

Edge cases checked mathematically before writing:

- Z empty: its empty clopen neighborhood has idempotent 0, so M contains 0 and
  R_Z is the zero ring, with empty spectrum. No nonzero-denominator assumption is made.
- Z = P: the only clopen neighborhood is P and its idempotent is 1, so R_Z is R.
- Zero ring: all spectra and their inverse-image subspaces are empty; localization
  and the homeomorphism still make sense. Local-ring assertions have no primes.
- Empty profinite space: the clopen-neighborhood index is still nonempty. A map
  from a nonempty spectrum into it cannot occur; for an empty spectrum it is covered.
- Equal inclusions and a three-term inclusion chain: the maps are the actual
  colimit-induced maps and their laws are asserted explicitly.
- Empty inverse image of a nonempty closed Z is allowed; no surjectivity of g,
  nonemptiness of P/Z, w-locality, or connected-component quotient condition is added.

Searches actually run:

1. `msearch.py ... leanfinder` with query "Canonical filtered colimit of idempotent
   localizations at clopen neighborhoods of a closed subset of a profinite space,
   with spectrum and natural local ring isomorphisms": 8 hits, on condensed
   locally-constant colimits and the clopen-idempotent equivalence; no full match.
2. `msearch.py ... loogle` with query
   `IsLocalization, Localization.localRingHom, CommAlgCat`: 0 hits.
3. `msearch.py ... grep` with query
   `clopen.*[Rr]estrict|[Rr]estrict.*clopen`: 9 hits, on clopen topological
   restrictions, none stating the required colimit theorem.
4. `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for the preceding pattern
   and the exact node id: found unrelated sheaf restriction material and the
   relevant `WContractible` constructions. Reading that module showed its spectrum
   theorem is only for its component-subset diagram and has no explicit M_Z
   localization identification or inclusion/local-ring naturality theorem.
5. `rg` over the source and DAG upstream-name index for
   `canonical_localization|ClopenRestrictionCanonicalLocalization|namespace
   WContractification.ClopenRestriction`: no collision with the new declarations.
   Direct source reads located `Localization.localRingHom` and the universal maps.

Validation: `scompile.py` compiled the module in sandbox and library module modes.
The first pass diagnosed reducibility needed at the diagram/colimit interface;
`idempotent` and `diagram` are abbreviations so their concrete types remain visible.
The next pass type-checked; unused lambda binders were then renamed `_` rather than
suppressing the linter. Final clean compile and required delivery preflight follow.
Only this sandbox was written; no direct Git operation or live build was run.

## Second reading by ND

Author's clause-by-clause rereading, not an independent worker review: the dispatcher
forbids starting other agents and assigns independent review to the maintainer.
The source and node were open while checking the concrete diagram object, its
arrow direction, the exact carrier equality for M_Z, the normalized homeomorphism,
the equality fixing the local-ring maps, and both restriction naturality formulas.
The reducibility fix changed no mathematical object. No hypothesis or conclusion
was changed. The two theorem docstrings together cover the entire DAG proof.
