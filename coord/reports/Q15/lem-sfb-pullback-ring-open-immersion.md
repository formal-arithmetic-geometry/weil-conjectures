## Worker report

States AlgebraicGeometry.pullbackRing_principalOpenUnion_isOpenImmersion in
Sheaf.AlgebraicGeometry.PullbackRingOpenImmersion, with the sole proof `sorry`.
No definitions, helper nodes, dependency repairs, or statement changes are needed.
The node's accepted stage-1 split is preserved verbatim. The earlier worker's
stage-1 unchanged-node rejection is superseded by this stage-2 assignment:
coord/brief-stage2.md §0 explicitly permits attaching a Lean statement to an
accepted split, and coord/queue.tsv lists this item at stage 2 with no Lean record.
No repair note for this item is present.

Read the complete node, each statement dependency and recorded declaration, the
three proof-dependency Mathlib declarations, Stacks limits.tex lemma-diagram
(Tag 01Z9), more-algebra.tex lemma-diagram-localize (Tag 01Z8), and the current
blueprint's direct-images proof for sk-thm-sf-ctf-stability. The node is a
supporting lemma below that unit, and its statement matches its stated sources.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings with identity B, R, R' are `{B R R' : CommRingCat.{u}}`.
  No Nontrivial instance is used. The common ambient universe is arbitrary;
  any given three rings can be placed in one such universe.
- The arbitrary ring homomorphisms s and t are `(s : B ⟶ R) (t : R' ⟶ R)`.
  There is no surjectivity hypothesis on either map.
- The coordinatewise ring B' = {(b,r) | s(b)=t(r)} is exactly the existing
  `(CommRingCat.pullbackCone s t).pt`. Read Mathlib's construction at
  Algebra/Category/Ring/Constructions.lean:450-460: it is the eqLocus subring
  of the two coordinate homomorphisms, with the coordinatewise inherited ring
  structure and canonical first and second projections. No private copy is made.
- The finite family of size m is `(m : ℕ) (f : Fin m → R') (g : Fin m → B)`.
  `Fin 0` gives the required empty family.
- Compatibility t(f_l)=s(g_l) is `hf : ∀ l : Fin m, t.hom (f l) = s.hom (g l)`.
- Isomorphism of the natural maps B_g → R_s(g) is
  `hs : ∀ l : Fin m, Function.Bijective (Localization.awayMap s.hom (g l))`.
  Bijectivity of a ring homomorphism is exactly being a ring isomorphism; this
  fixes the natural map rather than assuming arbitrary isomorphic rings.
- The element h_l is the explicit subtype element `⟨(g l, f l), (hf l).symm⟩`
  of that constructed fibre-product ring. Its second coordinate is f_l
  definitionally. The orientation reversal only matches eqLocus's convention.
- The first conjunct says `∀ l, Function.Bijective` of
  `Localization.awayMap (CommRingCat.pullbackCone s t).snd.hom h_l`.
  Its domain is Localization.Away h_l and its target is definitionally
  Localization.Away (f l). This is the specified projection-induced map.
- Q' is the scheme open `⨆ l : Fin m, PrimeSpectrum.basicOpen (f l)`.
  The second conjunct asserts `IsOpenImmersion` of its canonical inclusion
  `Scheme.Opens.ι (X := Spec R') Q'` followed by
  `Spec.map (CommRingCat.pullbackCone s t).snd`.
- The third conjunct identifies the range of that same composite with the
  carrier of `⨆ l, PrimeSpectrum.basicOpen h_l` in `Spec B'`. Together with
  IsOpenImmersion this identifies the schemes, including their structure
  sheaves, rather than merely exhibiting a topological image.
- Every identification uses the original coordinate projection. There is
  no existential arbitrary map, extra structure, or omitted conclusion.

Dependency declarations used:

- def-weil-ring-localization-away: Localization.Away in
  Mathlib.GroupTheory.MonoidLocalization.Away (lines 138-143), with the
  ring and canonical induced map supplied by public import
  Mathlib.RingTheory.Localization.Away.Basic, especially
  Localization.awayMap (lines 496-499) and IsLocalization.Away.map (203-209).
- def-weil-affine-spectrum: AlgebraicGeometry.Spec and Spec.map in
  Mathlib.AlgebraicGeometry.Scheme (470-480), publicly imported through
  Mathlib.AlgebraicGeometry.OpenImmersion.
- def-weil-open-immersion: AlgebraicGeometry.IsOpenImmersion in
  Mathlib.AlgebraicGeometry.OpenImmersion (35-39).
- lem-weil-pbc-localization-module-exact: LocalizedModule.map_exact in
  Mathlib.Algebra.Module.LocalizedModule.Exact (37-39), a plain proof import.
- lem-weil-pbc-principal-localization-open-immersion:
  AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway in
  Mathlib.AlgebraicGeometry.OpenImmersion (329-336), already publicly imported.
- lem-weil-pbc-open-immersion-injective-local-source:
  AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists in
  Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion (87-95), a plain proof import.
- The canonical open-subscheme inclusion is Scheme.Opens.ι in
  Mathlib.AlgebraicGeometry.Restrict (42-55), explicitly publicly imported.

Edge cases checked before writing: m=0 gives empty source and image, with
vacuous localization hypotheses and conclusion; zero rings have empty spectra
and are allowed; zero/nilpotent localization elements give zero localized rings
and empty principal opens; repeated family elements cause no change; s or t
need not be onto; the identity s case reduces to the ordinary projection
identification. None needs a node correction or a disputed flag.

Searches actually run in this session:

- msearch.py leanfinder: "A ring fibre product localized at compatible elements
  projects isomorphically onto the second localized ring if the first ring map
  localizes to an isomorphism; the union of principal opens is an open immersion".
  Eight hits, including RingHom.IsStandardOpenImmersion.holdsForLocalizationAway,
  AlgebraicGeometry.IsOpenImmersion.of_isLocalization,
  CommRingCat.isPushout_of_isLocalization, and localization base-change results.
  None is the ring-pullback assertion with its specified open-union image.
- msearch.py loogle: "CommRingCat, IsLocalization.Away". Nine hits concerning
  basic-open section localizations and related APIs; none states this result.
- msearch.py grep: "pullback|fiberProduct|fibreProduct" in RingTheory/Localization.
  Zero hits.
- rg in Mathlib/Algebra/Category/Ring found CommRingCat.pullbackCone and
  pullbackConeIsLimit in Constructions.lean; read their full definitions.
  They supply the canonical ring, not the localization/open-union theorem.
- rg "pullbackCone|fiberProduct|fibreProduct|pullback.*localiz|localiz.*pullback"
  across lean/WeilConjectures and lean/Sheaf found unrelated derived-pullback
  material and AffineTransitionLimit.ExtensionData.fiberProduct. Read its
  definition and adjacent lemma: it is a specialized subalgebra of sections
  attached to an ExtensionData diagram, not this general assertion.
- rg for this node ID in lean/WeilConjectures found no declarations.
  No exact existing declaration was located.

Compiled through the required scompile.py wrapper in both sandbox and library
module modes. Initial errors were the hidden Restrict import and coercion from
opens to sets; the final file explicitly imports Restrict and uses `.carrier`.
The final compilation passed cleanly in both modes (1.4 seconds each).

## Second reading by Q15

This is a separate second pass by the same dispatched worker; no other agent
was started, as the assignment prohibits it. The maintainer supplies the
independent delivery review. Re-read the node against the final compiled
signature: all three conclusion clauses are present, both homomorphisms are
unrestricted, and the localization hypothesis names the canonical s-map.
Checked the constructed pullback's carrier and second projection in the source:
`⟨(g l,f l),(hf l).symm⟩` has the required compatibility and maps to f_l.
Checked that the open immersion and range conjuncts use exactly the same
composite, whose domain is the union in Spec R' and whose target is Spec B'.
The output union is in Spec B', rather than Spec R or Spec B. Rechecked
m=0 and the absence of Nontrivial assumptions. No mathematical mismatch was
found; only the public import and explicit carrier syntax changed after the
first draft. The declaration has explicitly bound universes and variables,
one sorry, and no local notation or hidden auxiliary definitions.
