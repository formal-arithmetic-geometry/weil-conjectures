# Stage-1 worker report: Q57

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-picard-multiplicative-torsor.json`: item split into seven explicit steps; statement and all inherited citations/searches preserved.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-picard-square-triviality.json`: new statement, unsplit; no Mathlib match. Only an isomorphism of square-defect lines over the original field, with no normalization or coherent multiplication.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-geometric-power-integrality.json`: new statement, unsplit; no Mathlib match. Integrality of finite powers from a geometric torus-extension presentation.
- `citations.json`: verbatim statement quotes for every node in every step's uses.

## Attachments

None. Searched the live `lean/WeilConjectures` tree for the blueprint tag, semiabelian/semi-abelian terminology, multiplicative torsors, Barsotti and theorem-of-square names. The only multiplicative-torsor textual hit was an unrelated etale-torsor construction. Existing ring Picard declarations in Mathlib are not scheme Picard-zero results. No Lean was written or compiled.

## Wanted literature

WANTED: Raynaud, *Faisceaux amples sur les schemas en groupes et les espaces homogenes*, LNM 119 (1970), IV, semiabelian Picard/theorem-of-square calculus, for `lem-sfb-semiabelian-picard-square-triviality` and the item. The original is absent locally. Its broad IV attribution is inherited; I do not claim a numbered verbatim theorem without reading it. Milne AV I 8.4 proves the abelian comparison, and I 9.2 gives the abelian extension construction. These were read locally. The new semiabelian square input is explicitly agent-formulated and remains unsplit.

## Findings and changes

No mathematical statement dispute and no change of hypotheses or conclusion. The original item had no proof. I read the latest blueprint unit and direct-images proof (3), and kept the inherited alteration/Picard branch. The ancestor tool returns null, so the inherited null ancestor and complete via chain are retained. Whole-blueprint searches for semiabelian, theorem of the square, multiplicative torsor, algebraically trivial, connected extension, group extension and connected group found no statement duplicating either new input. The wider square and Picard searches found only unrelated exchanges and the curve/abelian Picard framework.

The locally available sources are Milne AV I 8.4 and 9.2 (printed pp.35--36, 41), and Milne iAG2017 12.48/12.50 (pp.246--247). The latter is already `lem-sfb-rosenlicht-product-unit-factorization`; I reused it. In particular I did not replace unit rigidity with constancy of all units, which fails on a torus.

The two new nodes are strictly smaller than the item. The square assertion provides no compatible multiplication on frames. The proof still constructs the frame scheme, normalizes on both axes, proves associativity and commutativity, constructs inversion, and checks exactness and the specified action. The integrality input has no line bundle at all. It supplies a geometric hypothesis needed for the existing product-unit theorem.

## Mathematical details reserved for the new nodes

For the geometric-power input, the sheaf exact sequence makes G a torsor over B under the split torus: on an fppf cover choose a lift of the universal point and use translation. The torsor is smooth and open over B; its geometric fibres are tori. Connectedness follows from the quotient-topology connected-fibre result, and smooth connected groups over an algebraically closed field are integral. Apply this to finite products of the exact sequence; n=0 is Spec F. I read Stacks groupoids.tex Tags 0499 (lemma-characterize-trivial-pseudo-torsors), 049B (lemma-torsor), 0B7Q (lemma-connected-group-scheme-over-field-irreducible), topology.tex 0377 (lemma-connected-fibres-quotient-topology-connected-components), and varieties.tex 056T (lemma-smooth-geometrically-normal). These are the documented ingredients of the agent-extracted statement; it is not passed off as a verbatim Stacks theorem. The later split must cite torsor smooth descent and product geometry explicitly.

The square input retains algebraic equivalence defined by chains of smooth connected parameter varieties, and asserts the square isomorphism over k. It cannot be replaced by a claim only over the algebraic closure: arbitrary-field descent, including nonsplit tori, is part of this smaller input. For a split torus all lines are trivial, and for an abelian variety the assertion is Milne 8.4 after the Picard-zero dictionary. The general semiabelian Picard calculation is the unresolved prerequisite, not silently inferred from Milne's proper case.

## Review by Q57

I checked B--E with the actual statements and local sources open. Both new nodes introduce every object, include definition dependencies, contain no proof or proof dependencies, and retain truthful search results from msearch.py. I read all ten saved search outputs. Square searches returned ring Picard tensor functoriality, square-zero rings and pullback-carrier lemmas; none states a semiabelian square theorem. The integrality searches found the definition and composition theorem for geometrically connected morphisms. Reading Mathlib/AlgebraicGeometry/Geometrically/Connected.lean shows that composition already assumes geometric connectedness of the maps; it does not derive that of an fppf extension, so it is not a one-line specialization. Unknown identifiers in Loogle were recorded as an unsuccessful query, not a service outage. All requests are in searches.jsonl.

Step 1 takes integral finite powers directly from the new geometric input, under exactly the geometric exact sequence in the item. No conclusion about properness of H is used. Step 2 uses the quotient classification and pullback naturality actually stated by projective-bundle-quotient-geometry; the locus of two isomorphisms and the frame dictionary are given explicitly in local bases. It does not cite the frame-torsor lemma in the wrong direction.

Step 3 uses precisely the ground-field square isomorphism asserted by the new square node. Automorphisms of a rank-one module are scalar units by its local basis definition. The two axis units have equal value c at (e,e); multiplying by c/(a(x)b(y)) therefore normalizes both axes. No uniqueness or coherence is taken from the new node.

Step 4 compares actual maps of line modules, giving a global unit on H cubed. The cited Rosenlicht statement gives the normalized formula for X=H squared and Y=H over the algebraic closure; Step 1 checks its integral, nonempty, finite-type hypotheses. The two restrictions are 1 by Step 3, so the ratio is 1. The affine coefficient-injection argument explicitly descends equality, even when k is nonperfect. Step 5 repeats the two-factor normalized formula for the commutator ratio, with both axis restrictions 1. Thus both uses are of the cited statement, not of an unstated theorem about characters or proper functions.

Step 6 uses the rank-one definition and the already constructed isomorphism to give the inverse locally by (f(x)t) inverse; uniqueness glues these morphisms. This is elementary and does not postpone a hidden inverse-existence theorem. Step 7 uses only bilinearity, the chosen identity frame, and Zariski local freeness. The cited Zariski-coverings-are-fppf statement says exactly that the local frame covers are permitted. The kernel is identified on arbitrary test schemes, not merely field points. The two declared off-unit tools are generic projective quotient geometry and the inclusion of Zariski covers in the fppf topology; neither replaces a unit-route argument.

I tested H=Spec k (any prescribed u rescales the usual multiplication), H a split torus (nonconstant character units must be allowed), H abelian (Milne's construction), rank r=0, and the integrality node n=0. Non-smooth groups such as alpha_p explain why smoothness cannot be omitted from the integrality statement; disconnected smooth groups explain why its connected-extension hypotheses matter. The item does not impose a perfection or split-over-k hypothesis. Every step is below 1000 characters, so no long step conceals an additional lemma.

## Not duplicates

- lem-sfb-semiabelian-geometric-power-integrality vs lem-sbc-finite-etale-generic-fibre-hom-extension-existence: extends maps between finite etale covers from a generic fibre; it gives no connectedness of a torus extension.
- lem-sfb-semiabelian-geometric-power-integrality vs sbc-lem-smooth-geometrically-reduced: gives geometric reducedness only, with no irreducibility or connectedness assertion.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sbc-smooth-connected-generic-geometry: assumes geometric connectedness of the supplied morphism; the new lemma must derive connectedness of the middle group from an exact fppf sequence.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sbc-smooth-connected-generic-geometry-core: assumes geometric connectedness of fibres, whereas the new statement derives it from the extension and also treats finite powers.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-a1-smooth-lisse-integral-lattice: constructs integral coefficient lattices in lisse sheaves, not integral schemes.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-a1-normal-completed-integral-model: constructs integral models of completed coefficient modules; no group-extension geometry is asserted.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-trf-smooth-connected-fibre-normal-integrality: needs geometrically connected fibres already; the new lemma derives connectedness from the torus-extension hypothesis.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-trf-smooth-geometrically-normal: gives geometric normality and reducedness, not connectedness or irreducibility of a group extension.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-trf-smooth-component-pure-transcendental: treats a single connected component containing a specified point, not that the full extension and all its powers are connected.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sc-smooth-algebra-reduced-field: gives reducedness of a smooth algebra, not irreducibility of a nonaffine torus extension.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sc-hilb-geometrically-integral: concerns the Hilbert scheme of points on a proper smooth curve, not semiabelian extensions.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sfb-split-torus-torsor-frame-geometry: describes a given flat torus torsor by line frames; it does not derive integrality of its total space from an exact sequence.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sfb-abelian-finite-product: handles proper abelian varieties; the middle group may contain a positive-rank torus and be nonproper.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sfb-quotient-connected-component-preimage: assumes a continuous quotient map with connected fibres, and does not establish these scheme-geometric hypotheses for a sheaf-exact group sequence.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sfb-smooth-affine-group-torsor-representability: represents a torsor and makes its projection smooth and open; it does not conclude integral total spaces or integral finite powers.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sfb-relative-snc-field-extension: concerns normal crossings divisors after scalar extension, not connectedness of group extensions.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-sc-abelian-variety-characterization: requires the group to be proper and connected; the middle semiabelian group need satisfy neither of those hypotheses as initially given.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-weil-pbc-zariski-h0-proper-henselian-pair: concerns sections over a proper henselian pair, not torus-extension integrality.
- lem-sfb-semiabelian-geometric-power-integrality vs lem-weil-pbc-connected-fibres-quotient-preimage-connected: is a topological conclusion under quotient and connected-fibre hypotheses that must first be proved for the fppf-exact group extension.

Additional concept comparisons: the square node differs from `lem-sfb-semiabelian-second-difference-diagonal`, which asserts a biextension structure for an arbitrary line and a diagonal algebraic-equivalence identity, not triviality of the square line for Picard-zero lines. `lem-sfb-semiabelian-cubical-rigidification` supplies a cubical structure, not a trivialization of the second difference. `lem-sfb-relative-picard-cube-face-detection` concerns a triple product with three trivial faces, not the two-factor square defect. `lem-sc-abelian-variety-characterization` cannot apply to the nonproper middle group. No new definition node is needed.

## Unfinished work

The two new statement-only nodes require their own later splits, as intended for a one-level stage-1 delivery. In particular the semiabelian Picard calculation and its arbitrary-field form are not claimed proved in this delivery. No attachment, compiler check, or Mathlib leaf is claimed. Server dry run and direct push follow this report.
