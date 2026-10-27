# Repair report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometrically-integral-fibre-neighbourhood.json: statement unchanged; split, three assembly steps.
- dag/nodes/sec-trace-formula/lem-trf-smooth-connected-open-spreading.json: statement; unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-smooth-connected-fibre-normal-integrality.json: statement; unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for every dependency of each assembly step.

## Attachments

None for the item or the complete new statements. The project's exists_geometricallyIntegral_fibre_neighbourhood in Sheaf/AlgebraicGeometry/Morphisms/GeometricallyIntegralFibreNeighbourhood.lean ends in sorry. No declaration under WeilConjectures states the whole neighbourhood result. AlgebraicGeometry.GeometricallyIntegral.of_smooth_of_geometricallyConnected (WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1732) proves the integrality part of the second new statement, but does not include its normal-local-ring conclusion. It is already recorded as a partial attachment of prop-pc-xk-integral. No new attachment of a partial statement is claimed.

## WANTED

None. All sources used are present. No SGA source is used.

## What was wrong and what was repaired

The released 2026-10-22 stage-1 repair requires at least two independently assignable statement-only nodes and an assembly proof of at most 3000 characters. The starting sandbox contained only dispatcher markers, no delivered node or report; I compared with the current repository and took its five-step 3375-character proof as the returned baseline. The item statement, statement dependencies and existing route are retained. There is no statement dispute. Existing reviewed/Lean records are retained as historical metadata; the released repair note explicitly reopens stage 1.

The two extracted arguments are comparable in size: old steps 1-3 have 1542 characters (with the elementary irreducible-implies-connected check also retained explicitly in assembly); old steps 4-5 have 1833. The first node takes geometrically connected T, not the item's geometrically irreducible T, and supplies a smooth connected family, with no integral-fibre assertion. The second node is a universal field-test lemma for an arbitrary smooth connected family, with normal stalks as well as integrality, and constructs no neighbourhood or open. Neither new node states the item. Their statements have no embedded proof, and proof/proof_deps are empty. The explicit human extraction order is the reason these intermediate arguments are separately queued rather than kept as short specializations of the already available inputs.

## Landing-return repair and current-DAG comparison (2026-10-22)

The return has one point: the reader approved the delivery but landing found a side-project completion that had not been promoted into the live queue DAG. I continued the delivered sandbox (the previous durable receipt named head 4ccb5433acd), rather than regenerating its two new nodes or their logged searches. The first required dry run on these retained files completed successfully at 7ca79c19c9a, with `OK (not pushed)`; the delivery tool built that candidate against the current server DAG.

I compared every field of the retained item against the current read clone. Before this repair, only proof, proof_deps, mathlib_searches and split_report differed: the current DAG still held the original five-step proof, while the sandbox held the ordered three-step assembly. The statement, statement dependencies, ancestry, source, Lean audit, existing review and approved tool uses agreed. Neither proposed new id exists in the current DAG. The live repair note remains released for stage 1, with keep_plan true and a requirement of at least two new statement-only nodes. Thus the old review does not supersede this explicit repair order.

I reconstructed the item from the current node and overlaid only worker-owned split fields, preserving the current maintainer fields. I also changed assembly steps 2 and 3 to state the hypothesis checks explicitly: step 2 matches smoothness and all three finite-presentation conditions and supplies geometric connectedness from step 1; step 3 takes smoothness and nonempty geometric connectedness from step 2, for an arbitrary point and arbitrary residue-field extension. This is a revised split, not a byte-identical re-push. The two independent pending statements, all old argument allocations, source citations, searches and duplicate comparisons are retained.

I re-read all three existing assembly definition statements: def-pc-geometrically-irreducible quantifies over every field extension and includes geometric integrality; def-weil-irreducible-components includes nonemptiness and the two-closed-subsets test; def-weil-connected-scheme includes nonemptiness and the clopen partition test. I re-read both retained new statements, which supply exactly the objects used in steps 2 and 3, and regenerated all six verbatim citation entries from current statements. No citation has become stale or requires substitution.

I also re-read every theorem input of the five-step current proof: lem-pc-smooth-flat; sbc-lem-smooth-geometrically-reduced; lem-trf-geometrically-connected-fibre-open-spreading; lem-pc-proper-base-change clause (2); lem-pc-open-immersion-smooth-composition; lem-weil-pbc-spec-domain-stalks-function-field; and lem-sbc-smooth-connected-generic-geometry-core. They still give, respectively, flatness, geometrically reduced fibres, the exact connected-open neighbourhood, smooth base change, smooth open restriction, the field-base local/function-field description, and normal integral generic geometry. In particular the last input is used over Spec K, whose integral normal base and nonempty total-space hypotheses are explicitly verified in the preserved old argument. It is not applied over the arbitrary original base.

I re-opened Stacks 055W and 057J in more-morphisms.tex, 056W there, 056T in varieties.tex and 033M in properties.tex. They continue to support the two extracted arguments. The unrestricted-base claim in the second new statement uses the existing generic-geometry tool over a field, not an unsupported application of the Noetherian-only 033M statement to an arbitrary base. I checked the empty-base vacuous case, exclusion of empty fibres by the connectedness convention, and arbitrary field extensions again. The current Sheaf neighbourhood declaration still ends in sorry; the WeilConjectures smooth-integrality declaration covers only part of the second new statement. Neither justifies ATTACH for the item.

The new statements and search questions have not changed. I read searches.jsonl and reused its recorded results, including smooth charts, generic integral morphisms, normalization base change and geometric-property definitions, which do not give either complete statement. Blueprint tag and keyword searches again returned no equivalent blueprint statement; the nearest blueprint ancestor remains lem-trf-local-term-locality. No new search is claimed.

## Preservation of every old argument

The first node carries smooth-flatness, smooth geometric reducedness, applying the existing 055W spreading theorem, preserving its exact open-fibre equality, and smoothness of the retained entire open by smooth base change and open-immersion composition. Its proof worker can apply lem-pc-smooth-flat and sbc-lem-smooth-geometrically-reduced, then lem-trf-geometrically-connected-fibre-open-spreading, then clause (2) of lem-pc-proper-base-change and lem-pc-open-immersion-smooth-composition. The input geometric-connectedness test is written out in the assembly.

The second node carries the arbitrary point t and arbitrary extension K, identification of C as the base change to Spec K, smoothness of C by smooth base change, identification of C_L with (V_t)_L for every further extension L/K, and hence geometric connectedness and nonemptiness of C. Spec K is integral with function field K and unique local ring K_(0)=K by lem-weil-pbc-spec-domain-stalks-function-field and def-weil-affine-spectrum; a field is integrally closed in its own fraction field because every fraction already belongs to the field. The generic fibre for the application of lem-sbc-smooth-connected-generic-geometry-core is the identity cartesian fibre C times_(Spec K) Spec K = C. Its full conclusion supplies integrality and integrally closed stalks. Quantification over t,K is explicit in the new statement and the final assembly. No normality/Noetherian assumption on the original base has been inserted. This preserves the original route rather than replacing it by the shorter upstream integral-fibre lemma.

For audit, the old proof is retained verbatim below; it is source material for the next workers, not proof steps in the new unsplit JSON files.

### Original step 1

By [lem-pc-smooth-flat], $h$ is flat, and by [sbc-lem-smooth-geometrically-reduced] all its fibres are geometrically reduced. Its finite presentation is a hypothesis. Moreover $T$ is geometrically connected: for every field extension $L/\kappa(s)$, $T_L$ is nonempty and irreducible by [def-pc-geometrically-irreducible, def-weil-irreducible-components]. If $T_L$ were partitioned into two nonempty clopen subsets, these would be two proper closed subsets covering it, contradicting irreducibility. This is exactly connectedness in [def-weil-connected-scheme]. Thus the flatness, finite-presentation, geometric-reducedness and geometric-connectedness hypotheses needed for the next step all hold.

Uses: lem-pc-smooth-flat, sbc-lem-smooth-geometrically-reduced, def-pc-geometrically-irreducible, def-weil-irreducible-components, def-weil-connected-scheme.

### Original step 2

Apply [lem-trf-geometrically-connected-fibre-open-spreading] to $h,s,T$. It supplies an affine elementary etale neighbourhood $(S_1,s_1)\to(S,s)$ and a quasi-compact open $V\subseteq Y\times_S S_1$ whose fibres are geometrically connected, with $V_{s_1}=T\times_{\operatorname{Spec}\kappa(s)}\operatorname{Spec}\kappa(s_1)$ as open subschemes of the designated fibre. In particular the residue-field map at $s_1$ is an isomorphism. Retain this neighbourhood and this entire open; it remains to prove geometric integrality of its fibres.

Uses: lem-trf-geometrically-connected-fibre-open-spreading.

### Original step 3

The projection $Y\times_S S_1\to S_1$ is smooth by clause (2) of [lem-pc-proper-base-change], applied to $h$ and $a$. The inclusion of $V$ is an open immersion, so [lem-pc-open-immersion-smooth-composition] shows that $v:V\to S_1$ is smooth. This uses no separatedness or Noetherian hypothesis on $S$ or $S_1$.

Uses: lem-pc-proper-base-change, lem-pc-open-immersion-smooth-composition.

### Original step 4

Fix $t\in S_1$ and an arbitrary field extension $K/\kappa(t)$. Put $C=V_t\times_{\operatorname{Spec}\kappa(t)}\operatorname{Spec}K$. By [def-pc-base-change] this is the base change of $v$ to $\operatorname{Spec}K$, so its structure map $c:C\to\operatorname{Spec}K$ is smooth by clause (2) of [lem-pc-proper-base-change]. For every further extension $L/K$, the iterated-base-change identification of [def-pc-base-change] identifies $C_L$ with $(V_t)_L$. The latter is connected by step 2 and [def-pc-geometrically-irreducible]. Hence $c$ has geometrically connected fibres (the base has just one point) and $C$ is nonempty, using [def-weil-connected-scheme]. To check the base hypotheses of the next step, [lem-weil-pbc-spec-domain-stalks-function-field] applied to the domain $K$ shows that $\operatorname{Spec}K$ is integral, its function field is $K$, and its only local ring is $K_{(0)}=K$. A field is integrally closed in its own fraction field, since every element of that fraction field already lies in the field. The one-point and residue-field description is also explicit in [def-weil-affine-spectrum].

Uses: def-pc-base-change, lem-pc-proper-base-change, def-pc-geometrically-irreducible, def-weil-connected-scheme, lem-weil-pbc-spec-domain-stalks-function-field, def-weil-affine-spectrum.

### Original step 5

Apply [lem-sbc-smooth-connected-generic-geometry-core] with base $\operatorname{Spec}K$ and structure map $c$. For its generic-fibre datum use the cartesian identity base change $C\times_{\operatorname{Spec}K}\operatorname{Spec}K\cong C$, as in [def-pc-base-change]; the base function field and all remaining hypotheses were checked in step 4. Its conclusion that $C$ is integral is exactly what is needed. Because $t$ and $K/\kappa(t)$ were arbitrary, [def-pc-geometrically-irreducible] says that every fibre $V_t$ is geometrically integral. The affine etale neighbourhood, residue-field isomorphism, quasi-compactness and exact equality of the prescribed open fibre remain those supplied in step 2, proving every clause.

Uses: lem-sbc-smooth-connected-generic-geometry-core, def-pc-base-change, def-pc-geometrically-irreducible.

## Not duplicates

lem-trf-smooth-connected-open-spreading vs lem-trf-cm-closed-point-flat-quasifinite-slice: the existing statement concerns A flat quasi-finite slice through a closed Cohen–Macaulay fibre point, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-open-spreading vs lem-trf-etale-finite-smooth-local-structure: the existing statement concerns Affine elementary etale finite-over-smooth local structure, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-open-spreading vs lem-trf-fibre-regular-element-flat-hypersurface: the existing statement concerns A fibre nonzerodivisor cuts a flat hypersurface near the point, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-open-spreading vs lem-trf-finite-locally-free-multisection-connected-open: the existing statement concerns Descent of a connected open using a finite locally free multisection, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-open-spreading vs lem-trf-flat-lfp-cm-locus-fibre-dense: the existing statement concerns The fibrewise Cohen–Macaulay locus is dense in every fibre, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-open-spreading vs lem-trf-generic-cm-locus-field: the existing statement concerns Dense Cohen–Macaulay locus in a finite type algebra over a field, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-open-spreading vs lem-trf-geometrically-connected-fibre-open-spreading: 055W assumes a flat finitely presented geometrically reduced family and concludes connected fibres; the new smooth specialization additionally proves that the retained open structure morphism is smooth. It is an input, not an identical full statement.

lem-trf-smooth-connected-open-spreading vs lem-trf-geometrically-integral-fibre-neighbourhood: the parent concludes integral fibres from a geometrically irreducible prescribed open; this extracted lemma is only one intermediate argument, with a different input and output.

lem-trf-smooth-connected-open-spreading vs lem-trf-minimal-primes-dense-spectrum: the existing statement concerns Minimal primes are dense in the spectrum, not the new lemma's smooth prescribed-open connected spreading data with its smoothness conclusion.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-a1-lisse-middle-extension: the existing statement concerns Recovery from a dense lisse open, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-a1-middle-extension-section-restriction: the existing statement concerns Unique continuation of ordinary adic middle-extension sections, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-a1-normal-completed-integral-model: the existing statement concerns Abstract completed integral models on normal Noetherian schemes, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-a1-normal-etale-components-clopen: the existing statement concerns Clopen irreducible components of an etale scheme over a normal base, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-a1-smooth-lisse-integral-lattice: the existing statement concerns Global integral lattices for lisse sheaves on smooth geometric fibres, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-pc-genus-well-defined: the existing statement concerns Well-definedness of the genus, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-per-alteration-cover-closed-fibre-shrink: the existing statement concerns Dimension-inductive gluing of local regular alteration covers, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sbc-finite-etale-generic-fibre-cover-density: the existing statement concerns Reducedness and dominance for generic restrictions of smooth covers, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sbc-finite-etale-generic-fibre-hom-extension-existence: the existing statement concerns Existence of morphism extensions from the generic fibre, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sbc-smooth-connected-generic-geometry: the existing statement assumes the base integral with integrally closed stalks and is about its total space and generic fibre; the new statement has arbitrary base and quantifies over all residue-field extensions. Its application must verify the field-base and identity generic-fibre hypotheses.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sbc-smooth-connected-generic-geometry-core: the existing statement assumes the base integral with integrally closed stalks and is about its total space and generic fibre; the new statement has arbitrary base and quantifies over all residue-field extensions. Its application must verify the field-base and identity generic-fibre hypotheses.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sc-hilb-geometrically-integral: the existing statement concerns The Hilbert scheme of degree-$d$ divisors on a curve is geometrically integral, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sc-picg-geometrically-integral: the existing statement concerns The degree-$g$ part of the Picard scheme is geometrically integral, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sc-smooth-algebra-reduced-field: the existing statement concerns A smooth algebra over a field is reduced, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sc-smooth-connected-curve-local-rings: the existing statement concerns Smooth connected curves: integral, local rings at closed points are DVRs, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-clopen-generic-projective-cover: the existing statement concerns Selected generic components form a projective cover, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-dm-finite-normalization-charts: the existing statement concerns Finite normalization of smooth Deligne--Mumford stacks and its charts, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-finite-quotient-generic-fields: the existing statement concerns Generic fields and component orbits in a finite quotient of a normal scheme, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-nodal-trait-regularization: the existing statement concerns Regularization of smooth-generic nodal families, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-normal-alteration-constant-regularization: the existing statement concerns Equivariant regularization of the constants of a normal alteration, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-regular-trait-curve-surface-components: the existing statement concerns Components and vertical DVR stalks of a regular proper flat trait scheme, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-semilinear-sylow-good-components: the existing statement concerns Good components of a semilinear Sylow quotient, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-sfb-tame-radical-curve-normalization: the existing statement concerns Smooth normalization of a tame radical cover of a marked curve, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-cm-closed-point-flat-quasifinite-slice: the existing statement concerns A flat quasi-finite slice through a closed Cohen–Macaulay fibre point, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-dnc-principal-generic-smooth-reduction: the existing statement concerns Generic smooth coordinate reduction for a principal divisor, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-etale-finite-smooth-local-structure: the existing statement concerns Affine elementary etale finite-over-smooth local structure, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-fibre-regular-element-flat-hypersurface: the existing statement concerns A fibre nonzerodivisor cuts a flat hypersurface near the point, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-geometrically-connected-fibre-open-spreading: 055W assumes a flat finitely presented geometrically reduced family and concludes connected fibres; the new smooth specialization additionally proves that the retained open structure morphism is smooth. It is an input, not an identical full statement.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-geometrically-integral-fibre-neighbourhood: the parent concludes integral fibres from a geometrically irreducible prescribed open; this extracted lemma is only one intermediate argument, with a different input and output.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-nodal-points-reduced-algebraically-closed: the existing statement concerns A curve with only smooth points and nodes over an algebraically closed field is reduced, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-normal-topologically-noetherian-components: the existing statement decomposes a normal topologically Noetherian scheme into finitely many components; it does not assert smooth connected-fibre normal integrality or construct a prescribed smooth open neighbourhood.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-smooth-component-pure-transcendental: the existing statement concerns Geometrically integral component of a smooth fibre at a purely transcendental point, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-smooth-geometrically-normal: the existing statement gives normality/regularity/reducedness for a smooth scheme over a field, without connectedness or integrality; the new field-test statement adds connectedness and integrality and quantifies over residue fibres.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-stable-curve-diagram-noetherian-model: the existing statement concerns Normal finite-type models of finite semistable modification diagrams, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-trf-stein-smooth-generic-curve: the existing statement concerns Finite Stein base of a proper smooth generic curve, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-weil-pbc-geonormal-dim-one-smooth: the existing statement concerns Geonormal dim one smooth, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-weil-pbc-good-curves-boundary-quasifinite: the existing statement concerns Quasi-finite boundary of fibrewise nonempty opens in good curve compactifications, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-weil-pbc-normalization-projective-components: the existing statement concerns Normalization projective components, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-weil-pbc-proper-flat-geometric-components-locally-constant: the existing statement concerns Geometric component count is locally constant in a proper smooth family, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs lem-wf-dense-open-pi1-surjective: the existing statement concerns Fundamental groups of a dense open surject, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs rem-pc-regular-normal: the existing statement concerns Regular schemes are normal; the normal decomposition, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-fibre-normal-integrality vs sbc-lem-smooth-geometrically-reduced: the existing statement concerns Smooth morphisms have geometrically reduced fibres, not the new lemma's normal integral geometry of every residue-field extension of an arbitrary-base smooth connected family.

lem-trf-smooth-connected-open-spreading vs lem-pc-clopen-smooth-proper-curve: restricts an already smooth proper scheme over a field to a clopen subscheme; it constructs no elementary etale neighbourhood and prescribes no fibre open.

lem-trf-smooth-connected-open-spreading vs lem-pc-open-immersion-smooth-composition: only proves smoothness of a given open restriction. It is an input to the extracted argument, not the connected spreading construction.

lem-trf-smooth-connected-open-spreading vs lem-weil-pbc-smooth-restrict-open-subschemes: gives permanence under given open restrictions and isomorphisms, not existence of a prescribed-fibre smooth connected open family after etale base change.

lem-trf-smooth-connected-open-spreading vs lem-sbc-smooth-relative-dimension-permanence: gives base change and composition with relative-dimension control, not a prescribed-open connected-fibre neighbourhood.

lem-trf-smooth-connected-open-spreading vs lem-trf-smooth-composition: only proves smoothness of the composite of two given smooth morphisms, not connected-open spreading.

lem-trf-smooth-connected-open-spreading vs lem-zl-affine-geometric-components-finite-extension: decomposes an affine finite-field scheme after a finite constant-field extension; the new node treats arbitrary bases and a given open in one fibre, with an elementary etale residue-field isomorphism.

lem-trf-smooth-connected-open-spreading vs lem-pc-proper-base-change: only preserves properness or smoothness under a given base change. Its smooth clause is an input, not the existence of the neighbourhood and open.

lem-trf-smooth-connected-open-spreading vs lem-sc-curve-base-change-relative-dimension-one: preserves smooth relative dimension one for a given curve base change, whereas the new node allows arbitrary smooth dimension and constructs a prescribed connected open family.

lem-trf-smooth-connected-open-spreading vs lem-a1-normal-completed-integral-model: constructs locally free integral coefficient models on a fixed normal scheme, not a scheme neighbourhood or connected-fibre open.

lem-trf-smooth-connected-open-spreading vs lem-a1-smooth-lisse-integral-lattice: constructs integral lattices in pro-etale coefficient sheaves, not a prescribed-fibre scheme neighbourhood.

lem-trf-smooth-connected-open-spreading vs sbc-lem-smooth-criterion: characterizes when a given morphism is smooth by flatness and smooth fibres, but constructs no elementary etale neighbourhood or open with geometrically connected fibres.

lem-trf-smooth-connected-open-spreading vs sbc-lem-smooth-geometrically-reduced: the existing statement gives only geometric reducedness of smooth fibres; it constructs no elementary etale neighbourhood or prescribed-fibre open. It is an input to the preserved first extracted argument.

lem-trf-smooth-connected-open-spreading vs lem-trf-smooth-geometric-stalk-algebra: the existing statement concerns strict-henselian stalk maps, quotient flatness and regular closed fibres over locally Noetherian schemes; it supplies no neighbourhood or smooth connected open with a prescribed embedded fibre over an arbitrary base.

lem-trf-smooth-connected-open-spreading vs lem-weil-pbc-open-relative-line-principal-geometry: the existing statement describes finite principal-open covers and finite-etale charts of the relative affine line over a Noetherian affine base. It does not spread a prescribed open in an arbitrary smooth fibre through an elementary etale neighbourhood.

## Review by Q14

I read more-morphisms.tex at Tags 055W (lemma-fibre-geometrically-connected-reduced), 057J (lemma-normal-morphism-irreducible) and 056W (lemma-smooth-normal), and the smooth application at 057K. For the second extracted argument I also read varieties.tex Tag 056T (lemma-smooth-geometrically-normal), properties.tex Tag 033M (lemma-normal-Noetherian), and the existing normal integral generic-geometry node and its Lean docstring. The first new lemma is precisely the connected-open stage of 057J in the smooth case, including smoothness of the restricted base change; the second is its geometric-fibre normal/integral stage, with the field-base proof retained as described above.

Assembly step 1 uses only the exact geometric-property definition, the nonempty irreducibility definition and the connected-space definition: I checked that the contradiction by two proper closed subsets proves the connectedness convention actually used by 055W. It is elementary. Step 2 cites the first new node, whose statement supplies every chosen object, smoothness, connected fibres, quasi-compactness, residue-field isomorphism and equality of embedded opens. Its input is geometric connectedness from step 1 and exactly the parent's finite-presentation hypotheses. Step 3 cites the second new node, whose statement supplies integrality for every extension of every residue field, and the geometric-property definition, which says precisely that this is geometric integrality. The additional normal-stalk conclusion of the new lemma is unused by the parent but records the old normal-geometry argument in full. Every cited statement is quoted verbatim in citations.json.

I opened all old cited node statements as well as the new ones. In particular the core geometry node requires integral normal base, nonempty total space, smoothness, geometric connectedness and a cartesian generic fibre; these are verified over Spec K in the retained argument, not silently assumed for the original base. Clause (2) of the proper-base-change node really supplies smooth base change, and the open-composition node really supplies smoothness of the composite. Neither is merely a definition used as a theorem. The 055W node really preserves equality as open subschemes and gives the residue-field isomorphism.

Small cases: T cannot be empty under the parent's geometric irreducibility convention; in the first new lemma it cannot be empty under geometric connectedness. A disjoint union of two smooth nonempty fibres fails that connectedness hypothesis; the empty family over nonempty base also fails it. The second new statement over an empty base is vacuous; over Spec K with identity extension its conclusion is nonempty smooth geometrically connected implies integral normal. Extensions need not be algebraic, separable or finite. No quasi-compactness or separatedness of the base is used to prove normal integral field tests. The affine-base quasi-compact open supplied by 055W is kept unchanged, so no unsupported shrinking changes the prescribed open.

I searched the whole DAG and blueprint by the Stacks tags and by smooth/connected/geometrically-integral/fibre-open phrases, and read the close candidate statements listed above. I ran and read two semantic phrasings and the required Mathlib source and Loogle/LeanSearch searches for each new node; their exact queries/results are recorded from searches.jsonl. Mathlib's geometric-property definitions, normalization base change, integral morphisms and smooth charts do not state either complete new lemma. The upstream smooth-geometric-integrality theorem gives only part of the second statement and is reported, not misrepresented as an attachment.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files: self-contained statements with definition citations and Stacks labels, no proof in new nodes, no unrun searches, no source-route change or SGA citation, no cyclic dependence on the parent, and all non-elementary assembly inputs are cited statements. There is no step longer than 2000 characters; the three-step assembly is below 3000. No Lean was written and no compiler was run.

## Renewed landing-return audit (2026-10-22)

I resumed the retained delivered files and ran the required initial dry run before changing them. It exited successfully with `OK (not pushed)` at `39d82f4c5fe`, confirming admission and preflight against the current server DAG. The earlier receipt and comparison above describe the preceding attempt; this audit continues those files without discarding either extracted argument or any search log.

The current read clone again differs from the retained item only in proof, proof_deps, mathlib_searches and split_report. Its statement, all statement dependencies, source, ancestry, Lean record, audit, old review and maintainer tool-use record agree. I reconstructed the delivery item from that current record and overlaid its worker-owned split fields. Neither extracted-node id is present in the current DAG. The released stage-1 keep_plan repair still requires at least two statement-only nodes. The current five-step proof's original argument is still preserved verbatim above.

I re-read every assembly citation and all ten existing theorem/definition inputs printed in the previous comparison, including the exact smooth base-change clause and the integral-normal generic-geometry conclusion. No changed cited statement requires replacing a dependency. The point equation a(s_1)=s and equality of opens in the designated fibre are now explicit in step 2. Step 3 now explicitly substitutes B=S_1 and uses the same v and V; its arbitrary-point/arbitrary-extension conclusion is exactly the definition of geometric integrality. I regenerated all six quotations from the current node statements. The item statement and both new statements are unchanged.

I reopened Stacks 055W and 057J (more-morphisms.tex, labels lemma-fibre-geometrically-connected-reduced and lemma-normal-morphism-irreducible), 056W there, 056T in varieties.tex, and 033M in properties.tex. The first extracted statement preserves the full prescribed open while proving the restriction smooth. The second retains the original field-base argument, whose normal integral base is Spec K, not the arbitrary base of the family. I checked again that nonemptiness is present, that field extensions are unrestricted, and that an empty base makes the second statement vacuous. The current Sheaf neighbourhood theorem still contains sorry; the WeilConjectures smooth-geometric-integrality theorem covers only integrality and not the second node's normal-stalk clause. Its current source line is 1732, corrected in this report.

I read every saved search result and reused the unchanged queries. The connectedness definitions, smooth charts, integral morphisms and normalization base changes found there still do not state either complete new lemma. Blueprint ancestor/tag/keyword checks retain lem-trf-local-term-locality as ancestor and no equivalent imported blueprint statement. The updated assembly remains below the 3000-character repair limit with no step over 2000. This repairs the return by an actual current-base delivery with clarified assembly, not an unchanged re-push. No repository file, launcher script or Lean file was written, and no compiler was invoked.

## Current-base repair by Q14 (2026-10-23)

The sole return point is the failed promotion of a side-project completion into the live DAG. I continued the exact retained delivery, rather than starting another split. All three node files, report.md, citations.json and searches.jsonl matched the saved fingerprints of head aa70bc0439f. The mandatory initial dry run on those untouched inputs exited 0 at d9f8fb22964, printing OK (not pushed). It used the delivery tool's current origin/sheaf-dag base, so the next delivery is rebuilt against the current DAG rather than rebased by writing in the shared repository.

The retained item and current read-clone node differed in exactly four fields: proof, proof_deps, mathlib_searches and split_report. Their statement, statement dependencies, source, blueprint ancestry, existing review, Lean record/audit, import fields and approved tool-use records agreed. The current node still contains the original five-step argument quoted above; neither extracted id exists in the current DAG. The released stage-1 repair note still says keep_plan and requires two new statement-only nodes. I rebuilt the item from that current record, retaining every maintainer-owned field, and overlaid the worker's split fields. The proof now checks universal quantification and nonemptiness explicitly in step 1, matches the embedded input open in step 2, and spells out preservation of every chosen datum after the field-test application in step 3. This changes the split itself as well as its base and report.

I re-read the current statements of every assembly citation: def-pc-geometrically-irreducible gives the universal extension test for both geometric connectedness and integrality; def-weil-irreducible-components requires nonemptiness and excludes two proper closed subsets covering the space; def-weil-connected-scheme is the nonempty clopen-partition convention. Step 1 is their elementary implication. Step 2's extracted statement supplies exactly the smooth morphism v, connected fibres, affine elementary etale data, quasi-compact open and equality in the ambient fibre that it uses. Step 3's extracted statement applies with B=S_1 to that same v and gives integrality for each residue-field extension. Its normal-stalk clause remains part of the retained argument, although the parent uses its integrality clause. All six saved citation quotations are still verbatim in the current statements; I regenerated them after the edit. Thus no changed cited statement requires replacing a citation.

I also re-read every existing input of the current five-step proof, including lem-pc-smooth-flat, sbc-lem-smooth-geometrically-reduced, the full 055W spreading statement, clause (2) of lem-pc-proper-base-change, lem-pc-open-immersion-smooth-composition, def-pc-base-change, the affine-spectrum and Spec-domain stalk/function-field statements, and lem-sbc-smooth-connected-generic-geometry-core. Smoothness supplies flatness and reduced fibres for 055W; the open restriction is smooth after base change. Over Spec K the generic-geometry lemma has integral normal base, nonempty total space and the identity generic fibre, as the retained argument verifies. I did not apply it over the arbitrary base B. I read all definition statements used by the three nodes, including finite presentation as lfp+qc+qs and a normal domain as a domain integrally closed in its fraction field.

For sources I reopened more-morphisms.tex at 055W, 057J and 056W; varieties.tex at 056T; and properties.tex at 033M. The Noetherian hypothesis of 033M is not asserted for the arbitrary original base. The second extracted argument keeps its prior field-base route through the generic-geometry lemma. I checked the empty-base vacuous case, exclusion of empty T and empty fibres, disjoint smooth components as a failed connectedness hypothesis, and arbitrary nonalgebraic residue-field extensions. No statement dispute or route change was found. The project's Sheaf neighbourhood theorem still ends in sorry; no WeilConjectures declaration supplies the full item. The upstream smooth-integrality theorem remains only a partial match for the second extracted statement.

I read and reused every entry of searches.jsonl, without repeating unchanged search questions. I read the saved Mathlib candidates and the geometric-property definition sources: smooth charts, integral morphisms, normalization and stalk-map spreading do not supply either complete new statement. Neither new statement or source was changed. Blueprint and DAG keyword/tag searches still give no identical imported statement; the ancestor remains lem-trf-local-term-locality. The current source-tag comparison found three previously undocumented pairs for the first new node; I read their statements and added the precise distinctions under Not duplicates. All 16 first-node and 17 second-node source-tag collisions now have comparisons. I checked delivery-errors B1-B10, C1-C8, D1-D5 and E1-E7 against these files; both new nodes remain self-contained and statement-only, every non-elementary assembly fact is a cited statement, and no new node restates the parent or introduces a cycle. All original argument allocations and historical report text remain. No Lean, repository or launcher file was written and no compiler was invoked.

The final dry run and direct delivery below are the remaining operational steps. The two unsplit proof tasks are intentionally left for their own workers as required by the human's extraction order.

## Unfinished work

The two statement-only nodes intentionally await their own proof workers as ordered. The initial current-DAG dry run passed; the revised split is submitted to the required final dry run and direct delivery next.
