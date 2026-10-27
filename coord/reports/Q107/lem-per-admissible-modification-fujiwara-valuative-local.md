# Q107 stage-1 delivery

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-modification-fujiwara-valuative-local.json: item, split; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-supported-ideal-principalization.json: new statement-only node, unsplit; no Mathlib match.
- citations.json: literal statement quotes for every proof-step citation.
- searches.jsonl and the named search-output text files: actual results of the required search commands. The earlier 2026-10-19 searches in the item are retained; ten new searches were run and read, five for the item and five for the new lemma. Both semantic services and Loogle responded. Loogle returned no matches; semantic hits concerned ordinary stalks, etale algebra, flatness criteria or colimit existence. None supplies either assertion. The second semantic phrasings specifically tested ordinary continuity and Raynaud–Gruson flattening.

## Attachments

None. The exact blueprint tag, Fujiwara, I-valuative, admissible modification, and henselian-colimit concepts were searched in lean/WeilConjectures. Its generic blowup and valuative-criterion declarations do not state the item or the new lemma. No Lean was written and no compiler, Lake, or build was run.

## WANTED

WANTED: Fujiwara, Theory of tubular neighborhood in etale topology, Duke Math. J. 80 (1995), 15–57, the local-ring/henselization study cited by ILO XX 4.4, for the item's original reference chain. This paper is absent from the supplied literature. I do not claim to have read it. The split instead reconstructs the reduction from the available Stacks module-flattening, strict-local and continuity interfaces and is explicitly agent-written.

## Problems and corrections

The Q112 release and coord/changes/20261024-Q112-strict-completion-inputs.md authorize this exact interface, not the discarded old graph. The item arrived unsplit, with no historical proof in the live node. I preserved its statement, statement dependencies, source, historical searches, and blueprint provenance. There was no earlier sandbox split or report to invalidate or replace.

ILO XX 4.4 is a sketch, not a proof of each assertion here. It supplies the intended local-ring reduction and refers to Fujiwara. In particular one cannot obtain the finite-ideal assertion just by blowing up ideals of A: a finitely generated ideal in the strict-local colimit may have generators only on an etale neighbourhood. The new lemma addresses this finite-stage etale issue. Nor are transition maps between modifications flat; cancellation with the common exceptional equation is used instead. The final arrow is checked by the termwise exchange formula, rather than just calling the groups naturally isomorphic.

No statement dispute or excellence hypothesis is introduced. The source's incidental SGA references are not used. The accepted conservative family and completed-system cofinality are taken from the currently admitted presentation statement, not reproved through an excluded interface. The parent is not a key statement of its unit, so no unit or chapter record is edited.

## What remains

The one new lemma is deliberately unsplit. Its proof must distinguish the extended ideal from the abstract module pullback: nonflat blowups can create a kernel. The expected argument is module flattening (Stacks 0815), identify the strict transform with the image ideal after discarding the supported kernel, use relative flatness along the etale map to get flatness as a module on the etale scheme, then finite presentation to obtain local freeness. Its rank is one on the schematically dense open, hence one everywhere. The result is an invertible ideal, including injectivity of its embedding in the structure sheaf. This comparison is a real auxiliary lemma, not a restatement of the item: it involves one finite stage, arbitrary etale V, an arbitrary supported ideal and a base modification, with no limit topos, henselian pair, completion, compatible point, or cohomology.

## Review by Q107

I read ILO XX 4.4 on printed pp.373–374, including the complete paragraph beginning “Using the study” and the final Note. I also read the nearby XX 2.4 discussion to check the role of corresponding closed fibres. The statement and proof of Stacks 0815 (flat.tex, theorem-flatten-module), 04GI (algebra.tex, lemma-colimit-henselian), 03Q9 (etale-cohomology.tex, theorem-higher-direct-images) and 03Q6 (lemma-directed-colimit-cohomology) were opened. For blowup refinements I read divisors.tex, lemma-composition-finite-type-blowups, lemma-composition-admissible-blowups, lemma-extend-admissible-blowups and lemma-dominate-admissible-blowups. The delivered proof cites the admitted project interfaces for these uses. The new lemma is sourced to 0815 together with the explicitly identified extra ideal comparison; it does not pretend that 0815 already states that comparison.

Step 1 uses the presentation statement for exactly its conservative family and common closed fibres, and the system statement for its filtered preorder. The strict-henselization local-structure statement gives strictly henselian local stages, while the functoriality statement gives structural maps. Locality of those maps is checked on their marked closed points. The two colimit statements really do allow local noninjective transition maps; the residue-field statement gives the maximal-ideal union and proves nonzeroness. This avoids treating a general colimit as a subring union.

Step 2 uses principalization only for the centre I on its own blowup. The system statement really includes schematic density, and the flat-density lemma applies to the etale neighbourhoods because flatness is included in the definition of etale. The directed-colimit elementwise statement supplies both representatives and eventual zero after specializing its initial module to the initial ring. The proof explicitly cancels only at stages where the exceptional equation is regular; it then passes cancellation to both colimits. The primed equation is the image of the same equation because the corresponding chart is its inverse image under the blowup comparison. Marked points on the closed fibre make both equations nonunits.

Step 3 applies the finite-representative statement twice: first to strict-local stages and then to pointed etale neighbourhoods. The finite equation witnessing containment of a power is descended as well as the generators. The neighbourhood can be affine, separated, and of finite presentation over the qcqs blowup; shrinking does not remove its marked point. Blowup properness supplies qcqs over the affine base. The chart/density argument covers every chart, so the Cartier-complement hypothesis of the new lemma holds globally. That lemma states invertibility of the extended ideal on the whole pulled-back neighbourhood, exactly what the step uses.

Step 4 uses clause (1) of the module admissible-blowup calculus only for its composition and centre-support assertions, not for a module-flatness conclusion. The first centre has full support, so adjoining the second centre preserves full support. The compatible geometric point and its etale lift select the local generator; after passage to B the surviving equation phi^n=ab proves the generator regular. Step 5 repeats this for all A'-modifications and uses precisely the cofinality clause of the presentation to return to the primed system named in the item. It never asserts that a nonflat completion is flat.

Step 6 is marked elementary because it is the universal-property calculation for a left adjoint at an already supplied point. The geometric-morphism definition actually contains the adjunction, and the presentation actually gives the projections and compatible points. No separate theorem about arbitrary limit topoi is smuggled into this step.

Step 7 applies the torsion strict-local stalk formula only to qcqs open immersions. Finite generation of I gives quasi-compactness, and separation of each blowup over the affine base gives quasi-separatedness. On the tail the punctured strict-local schemes are affine, so the continuity statement's affine-transition hypothesis holds. All coefficients are restrictions of one F, and the cited inverse-image torsion statement supplies the torsion hypothesis. Localization commutes with this ring colimit by its elementary map universal property.

Step 8 uses the underived-exchange definition's actual section-restriction formula, the termwise derived-exchange theorem's actual resolution comparison, and clause (2) of pullback functoriality for the canonical cohomology map. Thus the source and target of each map and the comparison complex agree. Equality is checked on representative neighbourhood legs before either colimit; clause (4) then identifies the resulting composite with the single localized-ring pullback. This also addresses all degrees simultaneously without a degree-dependent choice of family.

I tested the boundary cases: if I=0, I is nilpotent, or the closed-fibre limit has no points, its conservative family may be empty and no nonzero local ring is demanded at a nonexistent point. In a nonempty family the residue-field argument forbids zero rings. For a principal regular ideal over a henselian valuation ring the construction recovers the expected punctured localization. In a ring with zero divisors, the cancellation argument uses regularity of phi rather than assuming the ring is a domain. The new lemma allows the unit ideal (its extension is already invertible) and the empty etale scheme; the zero ideal can satisfy the unit-on-open assumption only on components with empty open, excluded on nonempty components by flatness and density. The statement does not require an ideal to be finitely presented: the source flattening theorem assumes finite type and obtains finite presentation after modification.

I checked delivery-errors B–E against the files: the new node is self-contained, defines schematic density inline, cites the actual notions, contains no proof or proof dependencies, and records only executed searches. DAG/blueprint/concept searches found no matching blueprint statement. It is neither an elementary step nor a clause of the item, for the finite-stage comparison reason above. Every proof-step dependency has been opened and its entire literal statement is copied into citations.json, with the use checked as described above. Every step is below 2000 characters. Off-unit results are proposed as generic tool uses in split_report.tool_uses; no accepted maintainer tool_uses field is written. The route remains the specifically re-admitted ILO no-excellence route.

## Not duplicates

lem-per-etale-supported-ideal-principalization vs lem-coef-sorted-simplicial-algebra-model: the existing statement concerns simplicial algebraic theories or categories; its 0815 occurrence is unrelated to ideal principalization in flat.tex.

lem-per-etale-supported-ideal-principalization vs lem-coef-fixed-object-free-arrow-adjunction: the existing statement concerns simplicial algebraic theories or categories; its 0815 occurrence is unrelated to ideal principalization in flat.tex.

lem-per-etale-supported-ideal-principalization vs lem-coef-cone-sorted-theory-identification: the existing statement concerns simplicial algebraic theories or categories; its 0815 occurrence is unrelated to ideal principalization in flat.tex.

lem-per-etale-supported-ideal-principalization vs lem-trf-flattening-module-by-admissible-blowup: the existing theorem supplies a flat finitely presented MODULE STRICT TRANSFORM; the new lemma asserts invertibility of the EXTENDED IDEAL on an etale base change, requiring the supported-kernel identification and rank-one argument.

lem-per-etale-supported-ideal-principalization vs lem-trf-smooth-generic-rank-reduction: the existing statement is a module-flattening intermediate result for smooth presentations or devissage; it does not identify a supported etale ideal with an invertible extended ideal after modifying the base.

lem-per-etale-supported-ideal-principalization vs lem-trf-smooth-free-sequence-transform-flatness: the existing statement is a module-flattening intermediate result for smooth presentations or devissage; it does not identify a supported etale ideal with an invertible extended ideal after modifying the base.

lem-per-etale-supported-ideal-principalization vs lem-trf-devissage-flattening-transfer: the existing statement is a module-flattening intermediate result for smooth presentations or devissage; it does not identify a supported etale ideal with an invertible extended ideal after modifying the base.

lem-per-etale-supported-ideal-principalization vs lem-trf-flat-module-presentation-after-boundary-blowup: the existing statement starts with an already relatively flat module and concludes finite presentation of its strict transform; the new lemma principalizes a possibly nonflat ideal and identifies its actual extended image.

lem-per-etale-supported-ideal-principalization vs lem-weil-pbc-mittag-leffler-limit-exact: the existing statement is an exactness assertion for inverse systems of abelian groups, not supported ideals on etale schemes.

