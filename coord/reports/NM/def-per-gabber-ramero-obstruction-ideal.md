## Files written

- `dag/nodes/sec-deligne-laumon-a1/def-per-gabber-ramero-obstruction-ideal.json`: definition, split; no Mathlib match for the whole definition. Added existing dependencies for quotient modules and polynomial partial derivatives; made the quotient action, finite free module, and set of presentations explicit.
- `citations.json`: empty list, because a definition has no proof steps or proof citations.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, Gabber–Ramero, and obstruction-ideal terminology found no declaration stating this definition. The sole generic obstruction-ideal phrase found in `RegularLocalOfFormallySmoothAdic.lean` concerns a square-zero obstruction and does not define this object.

## WANTED

WANTED: Michael Temkin, *Functorial desingularization of quasi-excellent schemes in characteristic zero: the non-embedded case*, arXiv:0904.1592v2, section 3.2.2, printed page 19, archival copy for def-per-gabber-ramero-obstruction-ideal. Read the PDF at the exact URL already recorded in the node. It is absent from the named local literature files; nothing was downloaded or written outside this sandbox.

## Corrections and scope

The original statement is a usable explicit definition, not a statement dispute. Its dependency list omitted the formal derivative and quotient-module notions. Those now cite existing Mathlib leaves. No Noetherian, smoothness, injectivity of the differential, or regular-sequence hypothesis is added. The polynomial presentation is explicitly the surjection, not just its polynomial domain, so two maps with the same domain remain different index entries. The changes expand notation and specify constructions without changing the defined subset of B.

Temkin 3.2.2 describes the intrinsic ideal as the common annihilator of first cotangent deformation obstruction modules. The imported item uses a presentation-based construction; it does not assert a presentation-independence theorem. The existing sibling `lem-per-gabber-ramero-ideal-calculus` is precisely where equality of H_P with H_{B/R} for each presentation and its geometric properties are stated. I have neither used that sibling to define H_{B/R} nor silently imported its unproved statement. There is no assertion here that the naive conormal complex is the entire cotangent complex, nor that its degree-one homology vanishes. This matters for non-smooth and non-flat algebras.

The current latest blueprint ancestor, `lem-per-artin-gabber-affine-curve.proof.md`, has a Step 3 about Verdier duality. It has no formal-resolution sentence. The existing `blueprint.from` creation chain records the auxiliary route inherited from the item's creator; it has been preserved rather than represented as a new sentence of the latest blueprint. The current unit section and chapter record were read. This is not the unit's key node and does not change either record or the unit route.

## Construction checks

These are elementary well-definedness checks of the explicit definition, not hidden new theorem nodes.

1. For b in B choose a polynomial p lifting b. Changing p by l in L changes pf by lf in L^2. Changing f by an element of L^2 changes pf by an element of L^2. Thus b[f]=[pf] is independent of both representatives. Addition, unit and multiplication laws follow by applying the corresponding polynomial identities to representatives. No arbitrary choice of a lift becomes part of the module data.
2. Every element of L^2 is a finite sum of products uv with u,v in L. The derivative of uv is u times the derivative of v plus v times the derivative of u, which maps to zero in B. Hence every component of delta kills L^2. For p in P and f in L, the derivative of pf reduces to pi(p) times the derivative of f, since pi(f)=0. This proves B-linearity of delta and independence of the quotient representative. The existing derivative node states exactly the needed additive and Leibniz rules, not merely existence of an unspecified differential.
3. The witnesses proving H_P an ideal are explicit. Zero has h=0. If b,c have witnesses h,k then h+k witnesses b+c, and -h witnesses -b. For a in B, the map ah is additive and B-linear by commutativity of B, and (ah)delta=ab id. Thus multiplication by arbitrary ring elements stays inside H_P. The arbitrary intersection is an ideal by these same membership rules, applied separately in each presentation. This uses no theorem about smoothness or deformation obstructions.
4. The presentations are indexed by the subset of the disjoint union of B^n over natural n consisting of generating tuples. Evaluation at each tuple gives the actual surjection; conversely its images of the variables recover the tuple. Finite presentation supplies at least one such tuple. This avoids a quantification over arbitrary ring types or an intersection over a proper class. The empty tuple is allowed.

## Edge cases

For n=0, the coordinate module is zero, delta is zero, and H_P is the annihilator of L/L^2, exactly as the displayed witness condition says. For a polynomial algebra with its identity presentation, L=0, so M=0 and H_P=B. For a surjective base map R to R/L one may use the empty tuple, giving the annihilator just described; it is not automatically the unit ideal. In the dual-numbers presentation k[x] to k[x]/(x^2), in characteristic two delta=0 while M is a nonzero free B-module of rank one, so H_P=0; in characteristic different from two the same presentation gives H_P=(x). These checks guard against treating the conormal differential as injective, or accidentally defining the Jacobian radical instead of the obstruction ideal. The zero algebra is also allowed: all sets and ideals have their unique zero element, and no nontriviality assumption is used.

## Mathlib and duplicate review

The original item's recorded searches were retained. All additional searches were run through the mandated msearch.py command and read. Both semantic phrasings returned conormal and Kaehler APIs, not a definition of the ideal of scalars whose endomorphisms factor through delta. Loogle returned Ideal.Cotangent and its quotient-module action. The source grep for Gabber, Ramero and obstruction-ideal names found only unrelated bibliography; the smooth-ring grep found cotangent-complex and formal-smoothness results. Ideal.Cotangent (Ideal/Cotangent.lean), the quotient APIs, and MvPolynomial.pderiv (PDeriv.lean) were read. These are ingredients, not one-line specializations of a declaration giving the whole item.

Whole-DAG searches by conormal/cotangent and by Gabber–Ramero/obstruction-ideal terms found the item and its existing calculus and lifting siblings. The completed-polynomial-conormal definition concerns adic completions and requires a Noetherian base; it is not this ordinary polynomial construction and is not cited. The smooth-ring-map definition uses the universal polynomial presentation and defines smoothness, not H_P. Whole-blueprint searches via blueprint_refs.py for conormal, Gabber, Gabber.Ramero and obstruction ideal found no equivalent blueprint definition. No new node was needed; in particular the elementary ideal-closure and derivative calculations were not promoted to nodes.

## Review by NM

I read Temkin section 3.2.2 at the node's recorded PDF URL, including its distinction between the intrinsic obstruction ideal and a Jacobian ideal. I read the local Stacks algebra.tex conormal-map construction in lemma-differential-seq and the polynomial differentiation discussion, and checked the actual statements of all four dependencies: finite-presentation supplies a finite generating tuple, polynomial-ring supplies the evaluation maps, quotient-module supplies L/L^2 and its representatives, and polynomial-partial-derivative supplies the additive Leibniz derivations. None is cited for a stronger deformation or presentation-invariance theorem. The quotient B-action and the differential formula were checked on representatives as above; this also verifies every hypothesis used, including f in L in the Leibniz computation and commutativity when multiplying a linear map by a scalar.

There are no proof steps to audit for C4 or C1 because this item is a definition; the only obligations are its constituent notions and elementary construction laws, all accounted for above. I checked B1–B10 against the resulting file (no new nodes, no invented searches, no leaf overclaim, and the inherited blueprint fields retained), C1–C8 for dependency meaning and cycles (no sibling calculus citation), D1–D5 for artificial splitting (none), and E1–E7 by the explicit small cases and type checks. No proof step exceeds 2000 characters; the proof list remains empty as required for a definition. The report does not stand in for a non-elementary proof: none is claimed by the definition, and the sibling calculus remains a separate item.

## Unfinished work

None for this one-level definition split. The separately existing ideal-calculus and section-lifting items remain responsible for their own theorems.
