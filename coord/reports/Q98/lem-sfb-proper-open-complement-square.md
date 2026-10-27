# Stage-1 delivery: lem-sfb-proper-open-complement-square

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-complement-square.json: statement, split using existing nodes; not a Mathlib leaf.
- citations.json: 14 verbatim statement quotations, one for every proof-step citation.
- report.md: this review.

No new nodes and no new Mathlib leaves. The statement, statement dependencies, source, creation record and blueprint lineage are retained. The five assembly steps have lengths 323, 453, 609, 497 and 481 characters, so none triggers the long-step review threshold.

## Attachments

None for the entire item. The source search found AlgebraicGeometry.ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint in lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenClosed.lean:68. It proves the derived vanishing clause, but does not state the geometric conclusions about U, Z, T, j, a and r_Z. Therefore it does not qualify as an attachment for this item. Its proof is useful corroboration, not evidence that the whole item is completed or has a sorry-free dependency closure. The existing module-level theorem is already recorded on lem-sfb-internal-open-extension-disjoint-vanishing; no duplicate node is introduced.

## WANTED

None. All documents needed are present.

## Corrections and limitations

No statement dispute and no hypothesis change. The item was unsplit and had no repair note; the sandbox initially contained only dispatcher markers. Its inherited Mathlib searches are retained and supplemented by the five actual logged Q98 searches. Both semantic phrasings were read. Hits give properness, closed immersions and Zariski structure-sheaf restrictions, not the complete pro-etale condensed-module assertion. The Loogle proper-monomorphism characterization was opened in Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean and proper pullback instances in Morphisms/Proper.lean; these are geometric partial results only.

The unit record sk-thm-sf-comp-composition still refers to an older smooth-purity unit file, whereas this item's current source and chapter are the main-20261015 six-functors-basics interchange proof. I kept the supplied chapter/unit/lineage and followed proof (3) of the current source: form the closed complement upstairs and show open extension vanishes there. No chapter, unit or upstream target was changed. Proper cohomological base change belongs to the parent boundary-vanishing argument and is not invoked to prove this smaller item.

## Not duplicates

No new node pairs. Whole-DAG searches for complement, scheme permanence, exact module pullback and disjoint extension, and blueprint_refs.py searches for complement, base change, disjoint, proper-open-complement, module pullback and exact pullback led to reuse of the existing nodes. In particular the underived vanishing is already lem-sfb-internal-open-extension-disjoint-vanishing, the pullback exactness is det-prop-sfb-module-pullback-exact-main, and the exact-derived comparison is def-sfb-left-derived-exact. None is recreated as a new clause of this item.

## Review by Q98

I read the current interchange proof (3), the current chapter record and the supplied composition-law unit. For geometry I opened Stacks schemes.tex, Tag 01JY (lemma-base-change-immersion), Tag 01KU (lemma-separated-permanence), Tag 01J9 (lemma-characterize-points and its preceding field-valued-point discussion), and Tag 0356 (lemma-map-into-reduction). I opened morphisms.tex Tags 01W4 (lemma-base-change-proper), 01W5 (lemma-closed-immersion-proper), 01T3 (lemma-composition-finite-type) and 01T4 (lemma-base-change-finite-type). For the sheaf assertion I read proetale.tex Tags 09BN (lemma-open-immersion) and 09AH (lemma-ses-associated-to-open), and the current blueprint documents for exact module pullback, the exact-left-derived comparison and preservation by open extension. The Stacks abelian-sheaf result is not treated as a theorem for condensed module objects: that passage is precisely the existing internal-module vanishing node used below. I also read the actual module-level and derived disjoint-image proofs in the live Lean source without invoking a compiler.

Step 1 uses lem-weil-pbc-open-immersion-base-change for the base change of i, lem-pc-quasi-compact-base-change for its quasi-compactness, and lem-weil-pbc-proper-fp-permanence (b) for the base change of c and the two base changes of r. I read all three statements: the base morphism is arbitrary, and the original i, c and r have exactly the required properties. Symmetry of the two fibre-product presentations merely exchanges their projections; no claim is made that the underlying topological square is a set-theoretic pullback.

Step 2 uses permanence (c) to make c proper, def-weil-proper-morphism to extract separatedness and finite type, permanence (e) for separated composition, and lem-sfb-finite-type-composition-base-change (1) for finite-type composition. I checked the actual structure maps: Z→Ybar→Spec k, U→Y→Spec k and T→Z→Spec k. The assumptions already give Y and Ybar separated finite type, and Step 1 gives the two proper projections. Properness of Y over k is neither asserted nor needed.

Step 3 uses lem-weil-pbc-open-preimage-fibre-product to identify the open range. I read lem-weil-pbc-morphism-from-spec-field: it explicitly supplies the canonical residue-field point with image w. I read lem-weil-pbc-field-point-factors-through-closed-immersion: a map from a field spectrum whose image lies in a closed subscheme factors through that subscheme, even if that subscheme is not reduced. Finally def-pc-fibre-product gives precisely the lifting map to T from its two compatible maps. I wrote the reverse containment of the closed range using this lift. The reduced scheme in Tag 0356 is Spec κ(w), not Z or T; this distinction is essential and is respected. Taking inverse images then distributes over the given set complement. This avoids the false assertion that an arbitrary map with set-theoretic image in a closed subscheme factors through it.

Step 4 uses sk-def-sfb-module-derived-lower-shriek only for its explicit termwise D(j_!), not as a theorem about derived pullback. I read det-prop-sfb-module-pullback-exact-main: it covers the actual scalar-extension module pullback for every commutative condensed ring, not only admissible finite or adic coefficients. I then read def-sfb-left-derived-exact: it explicitly identifies LF with D(F) for an exact functor. Here the relevant module-derived-functor existence setup is the one already fixed in the item's statement. Applying that comparison to a proves that any representative C of B can be used. Boundedness, constructibility and etale origin are never assumed.

Step 5 uses lem-sfb-internal-open-extension-disjoint-vanishing, whose statement gives a zero object for the actual coefficient module pullback of open extension along ANY morphism with disjoint image. I checked j is an open immersion from Step 1 and the disjointness comes from Step 3. I applied it to C^n, rather than claiming its statement already concerns derived complexes. The remaining degreewise unique maps to zero form an isomorphism of complexes because zero targets force every differential square to commute. Thus no derived-conservativity or left-completeness theorem is hidden in the last step.

I tested the empty open (U empty), whole open (closed complement empty), empty W, zero input complex, zero coefficient ring and arbitrary unbounded representative. For a concrete nonreduced complement, take r=id on Spec k[t], Y=D(t) and Z=Spec k[t]/(t^2); T=Z and the complement identity and vanishing remain valid. With Y empty one may take a closed nilpotent thickening/reduction with full underlying support; U is empty, so the proof still works. These cases check that no use of reducedness or density has entered. The proof is a finite assembly of existing lemmas and termwise constructions; no induction, local finiteness or unrecorded comparison is used.

The generic tools from other units are declared in split_report.tool_uses. Their only roles are geometric permanence, field-point factorization, exact pullback, the exact-derived comparison and the module vanishing interface; they implement, rather than replace, the current unit's open/closed route. No SGA source is used. No Lean file or repository file was written, and no build, compiler, local DAG checker or git command was run. The sandbox's citations.json was generated from the exact statements opened above and contains a record for every citation in every step.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes keep their own proof status and pending dependencies.
