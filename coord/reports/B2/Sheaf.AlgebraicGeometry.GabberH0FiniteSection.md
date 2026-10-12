## What changed

Replaced the single `sorry` in `AlgebraicGeometry.gabber_h0_finite_section` by a
compiling reduction along the original Tag 09ZF argument. The theorem's signature
and docstring are unchanged. The proof now:

1. Uses the injective part of `hZar` to obtain a surjective étale representative
   cover and its section.
2. Applies the already proved
   `Scheme.exists_finite_surjective_refinement_of_etale` to obtain the finite
   surjective cover and its local factorization maps.
3. Applies the new Zariski gluing statement to those maps. This produces a
   Zariski sheaf, a glued section in its inverse image, and comparison equations.
4. Uses the surjective part of `hFinite` for that particular cover and sheaf,
   applies the comparison to the lifting equality, and composes the equations.

Added the two proof imports `GabberH0EtaleCoverSection` and
`GabberH0ZariskiGluing`, and the proof import of `EtaleFiniteRefinement`.
The public section-operations import is narrowed from
`FiniteSurjectiveSetDescent` to `FiniteSurjectiveSetDescentInjective`, where
`etaleSetDescentUnit` and `etaleSetDescentComparison` are defined. No declaration
signature, definition, target, unit statement, or unit realization is changed.
The import narrowing is recorded in
`coord/changes/GabberH0FiniteSection-imports.md`; the sole direct importer
imports this module privately and independently imports full descent.

The two new interfaces are strictly parts of the argument. The representative
cover is étale, not finite, and needs only Zariski injectivity. The gluing theorem
works for an arbitrary morphism with local factorizations; it assumes neither
finiteness nor either global-section hypothesis. It produces a Zariski
inverse-image section and compatible maps, not the sought global étale section.
The existing finite refinement theorem and the application of `hFinite` are
performed in the item's completed Lean proof.

All three modules compile locally without warnings. The new interfaces were
checked against the source and at the empty-scheme, identity-immersion, and
empty-open-cover cases. Local representatives restrict to the whole closed
base change after shrinking (the correction in the current Tag 09ZF proof);
merely agreeing after an arbitrary local map would not suffice. The finite
subcover in the representative-cover lemma keeps the disjoint union in the
scheme universe. The gluing statement quantifies an arbitrary `J : Type`,
matching the existing refinement theorem, and does not impose nonemptiness.

## Proved and sorry left

Decomposed, closing one original hole from two new named obligations:
`AlgebraicGeometry.gabber_h0_finite_section`
(node `lem-weil-pbc-gabber-h0-finite-section`). No `sorry` remains in the item. Holes closed: 1; holes added: 2; local net: -1.
This is a decomposition, not a completed transitive proof.

The delivery adds exactly two named public theorems with `:= by sorry`:

- `AlgebraicGeometry.gabber_h0_etale_cover_section`, in
  `Sheaf.AlgebraicGeometry.GabberH0EtaleCoverSection`, node
  `lem-weil-pbc-gabber-h0-etale-cover-section`.
- `AlgebraicGeometry.gabber_h0_zariski_gluing`, in
  `Sheaf.AlgebraicGeometry.GabberH0ZariskiGluing`, node
  `lem-weil-pbc-gabber-h0-zariski-gluing`.

Each has a complete natural-language proof, a Tag 09ZF source, its blueprint
identifier, three kinds of recorded Mathlib searches, and its own DAG node.
There are no new definitions, private sorries, or axioms. This is a reduction,
not a claim that the target's transitive axioms are already sorry-free.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent`.
Its theorem `finiteSurjectiveSetDescent` and its proof dependency module
`Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer` are not needed by
this finite-section construction. In particular,
`lem-weil-pbc-sets-finite-surjective-descent` and
`lem-weil-pbc-sets-finite-surjective-descent-equalizer` are not dependencies of
this proof; later descent arguments can still need them independently.
The smaller module defining the two section operations remains a public import.

The old low-level proof dependencies are relocated below the two new statements,
not declared unnecessary globally. Their groups are: closed-pushforward stalks,
inverse-image stalks and determination by germs; local inverse-image
representatives; étale cancellation and openness; closed-immersion base change;
Zariski-to-étale restriction injectivity; composition units and the topological
inverse-image sheaf axiom. The local sheafification, finite-limit and Kan-colimit
steps are already packaged by
`Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription` and need not be
reimplemented in this item. The root node's direct proof dependencies now name
only the two new statements and the existing finite-refinement node. No step of
the blueprint unit is bypassed.

The new modules do not import finite-refinement, finite-surjective descent, or
quasi-separatedness: none of those enters their statements. The representative
cover uses compactness, but the gluing interface uses no compactness assumption.

## Where the brief, the DAG or earlier work was wrong

The item's original imports did not include the modules of its listed proof
dependencies; they included finite-surjective descent, whose equalizer theorem
is used only after the finite-section construction. The existing dependencies
are useful general facts but do not directly state either the representative
cover construction with the required shrinking or the Zariski gluing bridge
with all section transports. These are the two interfaces split off here.

The cited Stacks TeX file is not present in this read-only clone. I read the
corresponding current primary-source Tag 09ZF page at
https://stacks.math.columbia.edu/tag/09ZF instead. The proof used is the same
fourth-paragraph route already recorded by the node. No mathematical error or
false statement was found, and no statement was weakened.

## New nodes

`lem-weil-pbc-gabber-h0-etale-cover-section` groups original steps 2–5:
closed-subset detection, local inverse-image representatives, shrinking to
surjectivity on the closed base change, and construction of a surjective étale
cover carrying a section. It is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-h0-etale-cover-section.json`
and is stated in `lean/Sheaf/AlgebraicGeometry/GabberH0EtaleCoverSection.lean`.

`lem-weil-pbc-gabber-h0-zariski-gluing` groups original steps 7–8 up to the
construction of the section of the Zariski inverse image, together with the
comparison-unit equation. It is in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-gabber-h0-zariski-gluing.json`
and is stated in `lean/Sheaf/AlgebraicGeometry/GabberH0ZariskiGluing.lean`.
The application of the finite-base-change bijectivity hypothesis stays in the
item. Both nodes inherit `sec-proper-base-change` / `sk-thm-iff`; the public import narrowing is recorded in
`coord/changes/GabberH0FiniteSection-imports.md`. No existing statement or
definition changes, and the one direct importer needs no adaptation.


## Second reading by B2

1. **Existing interface unchanged: pass.** I compared every delivered module with
   the read-only repository. Only FiniteSection exists there: its declaration
   signature and docstring are byte-for-byte unchanged. Its only changes are
   the proof and imports; the public import narrowing has the supplied change
   record. The other two declarations and their modules are new. No definition
   or target changes. FiniteLift privately imports this item and independently
   publicly imports full descent; EtaleCriterion also imports full descent.
2. **Proof and trust: pass as a decomposition.** All three modules compile cleanly
   through lcompile.py after my repairs. A scratch copy printed axioms for all
   three declarations: only propext, Classical.choice, Quot.sound, and sorryAx.
   The original theorem has no sorry; exactly the two reported new named
   theorems have sorry. There are no new definitions or forbidden trust escapes.
   The final equation reverses hsigma, applies compare to the surjective-unit
   equality, and composes with hunit, with the fibre-product transport in the
   original orientation. One hole is closed and two added, not net proof progress.
3. **New obligations: pass.** I read Stacks Tag 09ZF, especially its corrected
   shrinking argument and the construction of the Zariski inverse-image section.
   EtaleCoverSection uses only injectivity, not finite-base-change bijectivity:
   closed-complement detection makes the representative cover surjective, and
   compactness gives a finite disjoint union in universe u. Its conclusion gives
   an etale representative, strictly less than the finite-section conclusion.
   ZariskiGluing uses a closed immersion, an arbitrary h, and local factorizations;
   its comparison and unit equations are exactly what the final proof consumes.
   It assumes no finiteness or global lifting hypothesis. The comparison theorem
   supplies sectionwise injectivity and the unit equation; local sections then
   glue in the topological inverse image, before hFinite is used. Neither new
   theorem merely renames the original statement. I checked empty X (unique
   sections), empty Z (the cover lemma's hZar forces empty X), identity i, empty
   W-cover (forces empty Xprime), and non-surjective h in the gluing theorem.
   No missing nonemptiness or compactness hypothesis was found. Independent
   leanfinder search for Zariski restriction/inverse-image injectivity, loogle
   `TopCat.Sheaf, Function.Injective`, and grep for sheaf restriction and inverse
   image sections found general stalk/local-surjectivity tools, not either new
   interface. I also searched lean/Sheaf and upstream Lean modules and read
   EtaleInverseImageSectionDescription, ClosedPushforwardConstantStalks,
   EtaleSetInverseImageCompositionUnits, and GabberZariskiEtaleRestrictionInjective.
   They provide the cited ingredients, not a short complete proof of either hole.
4. **Top-down route and pruning: repaired, then pass.** The Lean proof explicitly
   uses the already proved finite refinement and hFinite, between the two strictly
   partial interfaces. The unit sk-thm-iff realized fields remain unchanged; this
   subordinate construction bypasses no realized unit step. The original direct
   dependencies other than finite refinement are moved below the new interfaces:
   composition units, closed-immersion base change, closed-pushforward constant
   stalks, inverse-image stalks, germ determination, continuous pullback adjunction,
   etale base-change finite limits, local sheafification, presheaf pullback left
   exactness, filtered colimit representatives, etale cancellation/openness,
   closed-immersion and etale-site/sheaf definitions, etale locality on source,
   Zariski-etale restriction injectivity, and topological inverse image.
   None is claimed globally unnecessary. Full finite-surjective descent and its
   equalizer are unnecessary for this construction, but remain used elsewhere;
   this delivery makes no claim of a global closure-pruning count.
5. **DAG and module agreement: repaired, then pass.** The root's three proof_deps
   are exactly the two new interfaces and finite refinement; its elementary last
   step is hFinite surjectivity plus equality composition. Each new node has its
   declaration verbatim, source, docstring proof, search records, creation data,
   chapter/unit, and blueprint ancestry. The gluing plan now explicitly cites
   ZariskiEtaleInclusionMorphismOfSites when restricting an etale sheaf to opens.

Changes made in this second reading: added plain proof imports of
ClosedPushforwardConstantStalks, EtaleInverseImageSectionDescription,
EtaleSetInverseImageCompositionUnits, and the Mathlib limits, open-map and stalk
modules to EtaleCoverSection; added plain proof imports of composition units,
GabberZariskiEtaleRestrictionInjective and ZariskiEtaleInclusionMorphismOfSites to
ZariskiGluing. The first worker's open obligation modules had omitted the
imports for their planned dependencies, risking spurious dependency pruning.
Added the inclusion-morphism node to the first gluing step and proof_deps.
Clarified the report's hole accounting. No Lean statement or proof body changed.
