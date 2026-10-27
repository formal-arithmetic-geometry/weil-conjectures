# Stage-1 repair: lem-sfb-ample-curve-two-section-pencil

NR, 2026-10-22. This replaces the superseded stage-2 rebind with the substantive
stage-1 re-split explicitly ordered in the released stage-1 repair note dated
2026-10-22 (human decision of 2026-10-21). That note is the express exception to
live-wins in brief-stage1 §1; the previous BLOCKED disposition missed this exception.
The item's statement is unchanged. The owning Q16 Lean record remains existing=false
with file lean/Sheaf/AlgebraicGeometry/AmpleCurveTwoSectionPencil.lean. No Lean file
was written and no compile/build/Lake tool was run.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ample-curve-two-section-pencil.json:
  three-step assembly, two new proof dependencies, updated stage-1 split report.
- dag/nodes/sec-six-functors-basics/lem-sfb-ample-orbit-affine-pair.json:
  statement, unsplit; no Mathlib match. Noetherian dimension-at-most-one preparation,
  without a field or properness hypothesis (old steps 1-4).
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-orbit-pair-finite-norm.json:
  statement, unsplit; no Mathlib match. Proper-scheme criterion for a supplied affine,
  orbit-separated pair in any invertible module, without an ample or dimension
  hypothesis (old steps 7-10).
- citations.json: full verbatim cited statements for every step/node pair.
- report.md: this report, the complete original arguments, and retained earlier reports.
- searches.jsonl: append-only authentic searches from msearch.py. Retained prior log entries.

## Attachments

None. The exact theorem in Sheaf/AlgebraicGeometry/AmpleCurveTwoSectionPencil.lean:185
ends in sorry. Searches for the item tag and pencil/norm/orbit notions in
lean/WeilConjectures found no exact proved attachment. Its constructed helpers alone
do not supply every conclusion of the item.

## Wanted literature

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, §3.4(b), printed p.606,
for the item and both new auxiliary nodes. This local PDF is absent; the retained
prior worker report records a publisher reading. The strengthened orbit-separation
argument is explicitly agent-written. I read its actual local Stacks inputs below;
no SGA source is used.

## What was wrong and what changed

The returned packet was stage 2 and would have erased Q16's module ownership. The
previous retry restored ownership but proposed an unchanged item and treated the
live review as prohibiting the ordered re-split. The released S1 repair note now
explicitly requires two new nodes and an assembly of at most 3000 characters.
Both pieces of mathematics are strictly smaller independent tasks: the first
constructs two different-degree sections with a finite orbit boundary under weaker
hypotheses; it does not assert any norm-pencil map. The second assumes the pair
already supplied and proves the norm and finiteness criterion for arbitrary proper
schemes and arbitrary invertible modules. It does not produce sections or use ample
curve avoidance. Old common-power and separation arguments remain in the assembly.
This is the particular repartition the human requested, not a new claim that the
live ten-step proof was mathematically wrong. No statement correction was needed.

## What remains

Both new nodes are statement-only unsplit tasks. Their full proof work is preserved
below for the workers who take them. No assertion of a finished Lean proof is made.

## Review by NR

I read the released repair note, the chapter and unit records, GOAL.md, and both
copies of delivery-errors B-E. The unit is the existing constructible finite-Tor
stability route, and this is the same auxiliary local-pencil input below it; no
unit or chapter edit is proposed. Reading the actual note resolves the old apparent
conflict with the live review. I compared item fields with current live before
writing: all fields initially agreed. I retained the NH mathematics as source
material, and preserved every maintainer/Lean ownership field when repartitioning.

For the first new node I read Stacks properties.tex Tag 09NV
(lemma-ample-finite-set-in-principal-affine), Tag 0BA8
(lemma-Noetherian-irreducible-components), Tag 01OZ
(lemma-Noetherian-topology), Tag 0AAX (lemma-locally-Noetherian-dimension-0),
and schemes.tex Tag 01IS (lemma-scheme-sober). I also opened the existing
lem-sc-zero-dim-noetherian-closed-finite statement, which explicitly gives finiteness
and closedness for a closed dimension-zero subset of a Noetherian T0 space. The
chain argument below proves its dimension hypothesis; sobriety gives T0. No
rationality or infinitude of a field is needed by 09NV: E is a finite set of
scheme points, so the new lemma is valid even without a base field.

For the second new node I read modules.tex 01CD (lemma-tensor-product-pullback),
0B8L (lemma-pullback-invertible), 01CT (lemma-constructions-invertible), 01CB
(lemma-stalk-tensor-product), and 01CY (lemma-s-open); constructions.tex 01NE
(lemma-projective-space) and 01NG (lemma-standard-covering-projective-space);
schemes.tex 01KP (lemma-characterize-separated); morphisms.tex 01S8
(lemma-characterize-affine), 01W6 (lemma-image-proper-scheme-closed) and 01WN
(lemma-finite-proper). The local projective functor-of-points node states both
equivalence of pairs and pullback naturality; the invariance argument uses those
clauses, not mere equality of point maps. The separatedness needed for intersections
comes from properness. No dimension restriction is needed once the two affine
charts and orbit separation have been supplied.

Assembly step 1 cites exactly the finite-type-over-Noetherian theorem and the new
ample preparation. The former allows a Noetherian base, and a field has just the
two ideals, so its affine spectrum is Noetherian; finite type is an item hypothesis.
The latter assumes precisely the resulting Noetherian Y, its given dimension bound,
ample invertible L and finite action. Its conclusion supplies every datum extracted.
Step 2 cites the invertible-pullback-tensor statement for associativity and fibre
formulas, and the fibre-generation criterion for the final covering implication.
I read the entire statements: neither is a mere definition. The remaining positive
scalar-power and group reindexing checks are written out. Step 3 cites projective
implies proper, the supplied-pair criterion, the tensor comparison, and projective
functor-of-points. The first supplies properness over exactly F; step 2 supplies
all the criterion's input opens and orbit separation. Applying the criterion to
M=L^d gives C=bigotimes_g g*(L^d), canonically B^d; tensor distribution sends the
actual sections to the norms, and pair equivalence identifies scheme morphisms.
All eight citation pairs have full verbatim statement quotes in citations.json.

Small cases: dimension zero makes Z empty after the first open contains every
generic point; the second application of 09NV remains allowed. The empty boundary
T is harmless. The group always has an identity, including the trivial group;
no faithful action is needed. Reducible or nonreduced Y is allowed because the
finite-boundary argument is topological, residue nonvanishing gives stalk
generation, and invariance uses isomorphisms of sheaves and scheme morphisms.
Finite fields pose no parameter-point choice. The supplied-pair criterion even
allows empty Y, with empty affine charts and vacuous residue conditions. In
positive dimension a constant coordinate map with affine chart preimage Y would
force Y affine and proper, consistent with finiteness; no surjectivity is asserted.

The report below retains every old proof paragraph unchanged, assigned by old step
number to the new work or the assembly. New JSON nodes have empty proof and
proof_deps; none hides a proof sketch in its statement. No new statement is an
elementary two-line fact or an exact duplicate of its parent: their independent
input/output boundaries are explained above and in the duplicate comparisons.
No assembly step exceeds 2000 characters. Search queries are copied literally
from the wrapper log; returned declarations were read as described below and none
specializes in one line to either node.

## Mathlib and blueprint searches

The previous authentic searches are preserved. Fresh wrapper queries for each new
node include LeanFinder, LeanSearch, Loogle, source grep, and a second semantic
phrasing. Both Loogle queries returned unknown-identifier diagnostics (IsAmple or
ProjectiveSpace), not evidence by themselves. The semantic results for preparation
were affine open covers, structure-sheaf localization and Proj affine covers;
those do not select ample line-bundle sections or avoid translated zero sets.
For the supplied-pair criterion they were linear Projectivization actions, Proj
properness, finite global sections on an integral proper scheme, and limit or
normalization maps; none constructs the norm-pair map or proves its conclusions.
I read the Proj affine-cover/from-global-sections signatures in
Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:321,443 and properness in
ProjectiveSpectrum/Proper.lean:372; these concern graded rings or structure-sheaf
maps, not the pair of arbitrary invertible-module sections here. The source grep
returned no matching norm/orbit-pencil API. No Mathlib leaf is claimed.

Whole-DAG keyword and source-tag searches were performed before creating either
id. Blueprint searches for orbit, pencil, 09NV, ample and norm found no blueprint
node stating either result. blueprint_refs.py ancestor prints a null blueprint
ancestor for this created item; each new node retains that null and prepends the
item to the inherited via list, with the exact old steps in from.place. Candidate
nearby norm nodes impose smooth geometrically integral curves, algebraically closed
fields, free orbits or faithful generic actions: their statements do not cover the
arbitrary/nonreduced/finite-field case here. The existing norm definition supplies
constructions but not this theorem; its presence does not close either proof task.

## Retained arguments and allocation

The following is the complete old ten-step proof, not a shortened replacement.
The new nodes are deliberately statement-only. These paragraphs are their work
briefs and preserve every existing subargument and citation.

### Original step 1 — lem-sfb-ample-orbit-affine-pair

The field $F$ is Noetherian: its only ideals are $(0)$ and $(1)$. Hence $Y$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Applying [lem-sc-noetherian-closed-subset-finite-components] to the closed subset $Y$ gives a finite covering $Y=C_1\cup\cdots\cup C_r$ by irreducible components. Each $C_i$ has a generic point $\eta_i$ by [lem-weil-pbc-scheme-sober]. Put $E=\{\eta_1,\ldots,\eta_r\}$. This is a finite nonempty set; its points need not be $F$-rational or closed.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-sc-noetherian-closed-subset-finite-components, lem-weil-pbc-scheme-sober

Source: literature/stacks-project/properties.tex, Tags 01T6 (morphisms-lemma-finite-type-noetherian), 0BA8 (lemma-Noetherian-irreducible-components); schemes.tex Tag 01IS (lemma-scheme-sober).

### Original step 2 — lem-sfb-ample-orbit-affine-pair

Apply [lem-sc-ample-finite-principal-affine] to $(Y,L,E,W=Y)$. Obtain $p>0$ and $u\in\Gamma(Y,L^{\otimes p})$ such that $U=Y_u$ is affine and contains $E$. This application allows arbitrary finite sets of scheme points and arbitrary fields; it does not choose a rational point in a parameter open.

Uses: lem-sc-ample-finite-principal-affine

Source: literature/stacks-project/properties.tex, Tag 09NV (lemma-ample-finite-set-in-principal-affine).

### Original step 3 — lem-sfb-ample-orbit-affine-pair

Put $Z=Y\setminus U=Z(u)$, a closed subset. It contains no $\eta_i$. We check $\dim Z\leq0$ directly from [def-kun-topological-krull-dimension]. If $A\subsetneq D$ were a chain of nonempty irreducible closed subsets of $Z$, both would be closed in $Y$. Since $D\subseteq\bigcup_i C_i$, irreducibility and the finite covering imply $D\subseteq C_i$ for some $i$: otherwise the finite collection $D\cap C_i$ would cover $D$ by proper closed subsets. Because $\eta_i\notin Z$, $D\neq C_i$. The chain $A\subsetneq D\subsetneq C_i$ contradicts $\dim Y\leq1$. Now [lem-sc-zero-dim-noetherian-closed-finite] shows that $Z$ is a finite set of closed points. Its Noetherian hypothesis holds because the Noetherian scheme $Y$ of step 1 has a Noetherian underlying space [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal]; the $T_0$ property follows from the uniqueness of generic points in [lem-weil-pbc-scheme-sober], since distinct points with equal closures would be two generic points of one irreducible closed subset. The case $Z=\varnothing$ is included.

Uses: def-kun-topological-krull-dimension, lem-sc-zero-dim-noetherian-closed-finite, lem-weil-pbc-scheme-sober, lem-weil-pbc-noetherian-scheme-closed-subsets-minimal

Source: literature/stacks-project/properties.tex, Tag 0AAX (lemma-locally-Noetherian-dimension-0), combined with the chain definition of dimension (Topology Tag 0055); the displayed dimension argument is agent-written.

### Original step 4 — lem-sfb-ample-orbit-affine-pair

Let $T=\bigcup_{g\in G}g^{-1}Z$. It is finite because $G$ and $Z$ are finite and every $g$ is a bijection on points. For $h\in G$, $h^{-1}T=\bigcup_{g\in G}(g\circ h)^{-1}Z=T$, since $g\mapsto gh$ permutes $G$; in particular $h(T)=T$. Apply [lem-sc-ample-finite-principal-affine] with the finite set $E\cup T$ and $W=Y$. Obtain $q>0$ and $v\in\Gamma(Y,L^{\otimes q})$ with $V=Y_v$ affine and containing $E\cup T$. Thus $v$ is nonzero at every point of the entire orbit union $T$.

Uses: lem-sc-ample-finite-principal-affine

Source: literature/stacks-project/properties.tex, Tag 09NV (lemma-ample-finite-set-in-principal-affine), followed by finite-group reindexing.

### Original step 5 — assembly step 2

Set $d=pq$, $a=u^{\otimes q}$ and $b=v^{\otimes p}$, identifying $(L^{\otimes p})^{\otimes q}$ and $(L^{\otimes q})^{\otimes p}$ with $L^{\otimes d}$ by associativity of the tensor product. The tensor and residue-fibre formulas of [lem-weil-pbc-invertible-pullback-tensor] justify these sections and show $Y_a=Y_u=U$ and $Y_b=Y_v=V$: in a one-dimensional vector space over a field, the positive tensor power of a vector is nonzero exactly when the vector is nonzero (choose a basis and take a positive power of its scalar coefficient). In particular $Z(a)=Z$, $b$ is nonzero on $T$, and both nonvanishing opens are affine.

Uses: lem-weil-pbc-invertible-pullback-tensor

Source: literature/stacks-project/modules.tex, Tags 01CA (tensor associativity) and 01CB (lemma-stalk-tensor-product), applied repeatedly; the scalar positive-power check is elementary.

### Original step 6 — assembly step 2

We have $\bigcup_g g^{-1}Z(a)=T$. If $y\in T$ and $b(hy)=0$ for some $h\in G$, then $hy\in T$ by step 4, contradicting nonvanishing of $b$ on $T$. Thus $T\cap\bigcup_hh^{-1}Z(b)=\varnothing$, the required orbit separation. Taking the identity element in each union gives $Z(a)\cap Z(b)=\varnothing$. Equivalently $Y_a\cup Y_b=Y$, so $a,b$ generate $L^{\otimes d}$ by [lem-weil-pbc-invertible-generating-sections-fibre].

Uses: lem-weil-pbc-invertible-generating-sections-fibre

Source: literature/stacks-project/modules.tex, Tags 01AM (generated by global sections) and 01CY (lemma-s-open); finite-group argument written here.

### Original step 7 — lem-sfb-proper-orbit-pair-finite-norm

By [lem-weil-pbc-invertible-pullback-tensor], all $g^*L$, their finite tensor product $B$, and $B^{\otimes d}$ are invertible. The tensor symmetry and associativity identify $\bigotimes_g g^*(L^{\otimes d})$ with $B^{\otimes d}$ and give the norm sections $A=\mathcal N_G(a)$ and $D=\mathcal N_G(b)$. The same lemma's residue-fibre formulas give $Y_A=\bigcap_g g^{-1}Y_a$ and $Y_D=\bigcap_g g^{-1}Y_b$: each residue-field extension is injective and a finite tensor of vectors in one-dimensional vector spaces is nonzero exactly when every vector is nonzero. Therefore $Z(A)=\bigcup_g g^{-1}Z(a)$ and $Z(D)=\bigcup_g g^{-1}Z(b)$. These closed sets are disjoint by step 6. Hence $A,D$ generate $B^{\otimes d}$ by [lem-weil-pbc-invertible-generating-sections-fibre].

Uses: lem-weil-pbc-invertible-pullback-tensor, lem-weil-pbc-invertible-generating-sections-fibre

Source: literature/stacks-project/modules.tex, Tags 0B8L (lemma-pullback-invertible), 01CT (lemma-constructions-invertible), 01CD (lemma-tensor-product-pullback), 01CB (lemma-stalk-tensor-product); residue-value check written here.

### Original step 8 — lem-sfb-proper-orbit-pair-finite-norm

The two generating pairs define $F$-morphisms $f=[a:b]$ and $f_N=[A:D]$ by [def-weil-pbc-morphism-to-projective-space-by-sections] and [lem-weil-pbc-projective-space-functor-of-points]. Let $Q_0,Q_1$ be the two standard affine opens of $\mathbf P^1_F$. The covering, affineness and coordinate nonvanishing descriptions are [lem-weil-pbc-projective-space-standard-charts]. Since the defining pair identifies the pulled coordinate sections with its two entries, the residue pullback formula of [lem-weil-pbc-invertible-pullback-tensor] gives $f^{-1}Q_0=U$, $f^{-1}Q_1=V$, $f_N^{-1}Q_0=\bigcap_g g^{-1}U$, and $f_N^{-1}Q_1=\bigcap_g g^{-1}V$. These are equalities of open subschemes: all are the indicated opens with their restricted scheme structures.

Uses: def-weil-pbc-morphism-to-projective-space-by-sections, lem-weil-pbc-projective-space-functor-of-points, lem-weil-pbc-projective-space-standard-charts, lem-weil-pbc-invertible-pullback-tensor

Source: literature/stacks-project/constructions.tex, Tags 01NE (lemma-projective-space), 01NF (definition-projective-space), 01NG (lemma-standard-covering-projective-space), and 01MS/01MV for the twisting coordinate sections.

### Original step 9 — lem-sfb-proper-orbit-pair-finite-norm

The structure morphism $Y\to\operatorname{Spec}F$ is proper by [lem-kun-projective-implies-proper]; hence it is separated by [def-weil-proper-morphism]. Every $g^{-1}U$ and $g^{-1}V$ is affine, being isomorphic to $U$ or $V$ under the automorphism $g$. Applying [lem-weil-pbc-separated-affine-open-intersection] successively proves their finite intersections affine; $G$ is nonempty because it is a group, so the induction begins with one affine open. Thus all four inverse images in step 8 are affine, and [pqf-lem-affine-local-target] proves both $f$ and $f_N$ affine. The projection $\mathbf P^1_F\to\operatorname{Spec}F$ is proper, and therefore separated, by [lemma-nagata-projective-space-base-change-proper] and [def-weil-proper-morphism]. Both maps are morphisms over $F$, so [lem-weil-pbc-proper-over-separated] proves both proper. Finally [lem-sfb-affine-proper-finite] proves both finite.

Uses: lem-kun-projective-implies-proper, def-weil-proper-morphism, lem-weil-pbc-separated-affine-open-intersection, pqf-lem-affine-local-target, lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-proper-over-separated, lem-sfb-affine-proper-finite

Source: literature/stacks-project/morphisms.tex, Tags 01WC (projective implies proper), 01W6 (lemma-image-proper-scheme-closed), 01S8 (lemma-characterize-affine), 01WN (lemma-finite-proper); schemes.tex Tag 01KP (lemma-characterize-separated).

### Original step 10 — lem-sfb-proper-orbit-pair-finite-norm

For each $h\in G$, the pullback, composition and permutation isomorphisms of [lem-weil-pbc-invertible-pullback-tensor] identify $h^*(B^{\otimes d})$ with $B^{\otimes d}$: on the presentation $B^{\otimes d}=\bigotimes_g g^*(L^{\otimes d})$, $h^*$ replaces the factor indexed by $g$ by $(g\circ h)^*(L^{\otimes d})$, and $g\mapsto gh$ is a permutation. This very isomorphism carries $h^*A$ to $A$ and $h^*D$ to $D$, since both are the tensor products of those same indexed sections. By pullback compatibility and equivalence of generating pairs in [lem-weil-pbc-projective-space-functor-of-points], the maps to $\mathbf P^1_{\mathbf Z}$ for $(h^*B^{\otimes d},h^*A,h^*D)$ and $(B^{\otimes d},A,D)$ are equal. Their structure maps to $\operatorname{Spec}F$ also agree, since $h$ is an $F$-automorphism. Uniqueness in [def-weil-pbc-morphism-to-projective-space-by-sections] now gives $f_N\circ h=f_N$ as scheme morphisms. This proves invariance including nilpotents, without replacing equality of morphisms by equality on points.

Uses: lem-weil-pbc-invertible-pullback-tensor, lem-weil-pbc-projective-space-functor-of-points, def-weil-pbc-morphism-to-projective-space-by-sections

Source: literature/stacks-project/constructions.tex, Tag 01NE (lemma-projective-space), functoriality and equivalence of pairs; modules.tex Tags 01CD and 01CA for pullback and tensor permutations.

## Not duplicates

- lem-sfb-ample-orbit-affine-pair vs lem-sfb-ample-curve-two-section-pencil: the new theorem works without a base field or properness and returns different-degree sections and a finite stable boundary; it asserts no finite coordinate or norm map. The parent still constructs the common degree and proves orbit separation before using the second criterion.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sfb-ample-curve-two-section-pencil: the new theorem assumes a specified orbit-separated affine pair on an arbitrary proper scheme with any invertible module; it produces no sections or common ample power and needs no curve dimension bound. The parent supplies those hypotheses using the preparation and common-power argument.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sfb-effective-action-norm-pencil: the existing lemma assumes an integral source dominant over an integral base and proves faithful generic restriction and base-change compatibilities; it neither covers nonreduced Y nor gives the supplied affine-chart finiteness criterion.
- lem-sfb-ample-orbit-affine-pair vs lem-sfb-norm-pair-geometric-witness: the existing lemma starts with a simple-zero section on a smooth proper integral curve over an algebraically closed field with a free rational orbit. The new theorem has none of these hypotheses and uses powers of an ample module to avoid finite closed orbit sets, including over finite fields.

- lem-sfb-ample-orbit-affine-pair vs lem-sc-glued-component-affine-section: the existing theorem glues componentwise line bundles on a reduced closed cover and gives one affine section open; it has no finite orbit-boundary pair conclusion.
- lem-sfb-ample-orbit-affine-pair vs lem-sc-reduced-dim-le-one-ample: the existing theorem constructs an ample module on a reduced separated scheme; the new result starts from a given ample module on any Noetherian scheme and constructs the orbit-boundary pair.
- lem-sfb-ample-orbit-affine-pair vs lem-sc-ample-finite-principal-affine: the existing lemma chooses one principal open through a supplied finite set; the new result constructs the finite boundary on a dimension-one Noetherian scheme and a second open containing its entire group orbit.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-trf-finite-locally-free-composition: the existing theorem composes finite locally free morphisms; the new criterion has no flatness input or composition conclusion.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-pc-projective-pair-linear-mono: the existing theorem transfers monomorphy between coordinate pairs related by linear combinations; the new criterion concerns tensor norms, finiteness and group invariance.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sfb-universal-norm-generation-open: the existing parameter-space result requires a smooth projective geometrically integral curve and gives universal generation/invariance; the new criterion allows arbitrary proper schemes and derives finiteness from supplied affine charts.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sfb-plucker-chart-classifying-bijection: the existing theorem classifies Grassmannian quotients via Plucker equations; it does not state a finite norm-pencil criterion.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sfb-affine-proper-finite: the existing criterion is a generic equivalence for a supplied morphism; the new result constructs the ordinary/norm coordinate morphisms from supplied sections and proves the affine/proper hypotheses and invariance.
- lem-sfb-proper-orbit-pair-finite-norm vs def-sfb-projective-coordinate-section: the existing definition defines homogeneous coordinate sections; it asserts no finiteness or orbit-norm property.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sfb-finite-etale-clopen-restriction: the existing lemma restricts a finite etale map to a clopen subset; the new criterion has no etale hypothesis and constructs maps from sections.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-sc-proper-affine-finite-general: the existing assertion concerns the structure morphism to Spec of a field; the new maps have projective-line target and require a norm-pair construction.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-per-affine-proper-finite: the existing finite iff affine and proper statement supplies no section or norm construction; the new criterion proves its hypotheses for two concrete maps and proves invariance.
- lem-sfb-proper-orbit-pair-finite-norm vs def-weil-pbc-morphism-to-projective-space-by-sections: the existing definition constructs the coordinate morphism from a generating pair; the new criterion proves tensor-norm generation, finiteness and invariance from orbit separation and affineness.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-projective-morphism-chart-preimage: the existing theorem identifies individual chart preimages for an already generating pair; it has no norm, invariance or finite morphism conclusion.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-finite-morphism-permanence: the existing theorem starts from a finite morphism and records permanence; the new criterion proves two section morphisms finite and norm-invariant.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-projective-space-functor-of-points: the existing representability theorem identifies generating pairs with morphisms; it has no affine/proper finiteness or orbit-norm criterion.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-projective-space-finite-index-iso: the existing theorem reindexes finite projective coordinates by an isomorphism; it does not construct finite pencils on a proper source.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-finite-closed-map-finite-fibres: the existing theorem deduces closedness and finite fibres from an already finite map; the new criterion constructs maps and proves finiteness.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-etale-splits-off-isolated-points-technical: the existing theorem splits isolated fibre points after an etale neighbourhood; the new result has no such local splitting or etale conclusion.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-projective-space-reindex-is-iso: the existing theorem proves a coordinate reindexing morphism invertible; the new result uses a finite group on the source and tensor products of its section pullbacks.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-sections-morphism-to-proj-polynomial-ring: the existing theorem constructs a map from supplied generating sections and computes chart coordinates; it does not prove finite norm morphisms or their invariance.
- lem-sfb-proper-orbit-pair-finite-norm vs lem-weil-pbc-invertible-generating-sections-fibre: the existing fibre criterion detects generation; the new criterion also proves finite coordinate maps and invariance using orbit separation and affine charts.

## Validation

The first substantive dry run passed preflight and exited 0 at 068b3c8a4ed.
A subsequent manual statement-dependency audit found that the local JSON helper
had missed comma-separated definition citations: two for the preparation and four
for the proper-pair criterion. I added all six directly to the new nodes' stmt_deps.
No statement or proof changed; a fresh final dry run validates the corrected packet.

Initial required dry run exited 1: unchanged item, old 6791-character proof, zero
new nodes. The substantive re-split above repairs all three; final results follow.

## Repair of L's promotion return — 2026-10-22

The returned delivery had passed its mathematical reading, but landing refused
its side-project completion because that completion had not been promoted to the
live DAG used by the queue. This repair is the stage-1 delivery on the current
live base; it does not claim that a side completion is already live. Promotion
and the final independent review remain the maintainer's action.

I compared the retained packet (whose earlier durable receipt named
5b6ad80fa36) with the current read-only live node. Only proof, proof_deps and
split_report differed: the statement, statement dependencies, sources, blueprint
ancestry, reviewed records and Q16's owning Lean record all agreed. The current
released stage-1 repair note still explicitly requires at least two new nodes
and an assembly of at most 3000 characters, so the old ten-step live proof is
material to retain, rather than a reason to discard this ordered re-split. Both
new node ids are absent from the current live DAG. The first fresh delivery-tool
dry run rebuilt this retained payload against origin/sheaf-dag and passed server
preflight at 2de289f3e86, exiting 0 before any further invocation.

I re-read every currently cited statement, comparing it to the retained full
statement quotes in citations.json. All eight citation pairs, covering the two
new nodes and five existing nodes, remain verbatim matches; there is no changed
cited statement requiring a replacement. Specifically, the finite-type theorem
requires a Noetherian base; step 1 now names Spec F as that base. The first new
node supplies the finite stable orbit boundary and both affine opens without
properness or a base-field assumption. In step 2 the tensor-fibre statement and
fibre-generation criterion supply precisely the scalar nonvanishing and covering
clauses used. In step 3 projective-implies-proper supplies the proper F-scheme
hypothesis for the second new node, whose other hypotheses are the affine opens
and orbit separation established in step 2. The pullback-tensor statement gives
section-compatible tensor comparisons, and the projective functor-of-points
statement explicitly gives equivalence of generating pairs and pullback
naturality. I expanded step 3 to specify the same isomorphism beta on both norm
sections, preservation of invertibility and generation, and equality of the
coordinate maps over F by their projective map and fixed structural map. This
makes the transport of finiteness and scheme-level invariance explicit.

I also re-opened the current statements supporting the retained long arguments:
09NV affine avoidance, finite irreducible components, sobriety, Noetherian
underlying topology, zero-dimensional closed-subset finiteness, separated affine
intersections, affine-local-on-target, proper-over-separated, proper projective
space and the general affine-plus-proper finite criterion. None forces a change
to the retained work briefs. I re-read local properties.tex at the 09NV, 0BA8,
01OZ and 0AAX labels and constructions.tex at 01NE and 01NG; the preparation
allows arbitrary finite point sets, and pair equivalence concerns scheme
morphisms, including on nonreduced schemes. Fresh whole-blueprint searches for
norm pencil and 09NV found no additional blueprint node. The old authentic
Mathlib search log and its actual hit lists were read and retained; neither the
new statements nor the search questions changed, so no searches were invented
or needlessly rerun. The two unknown-identifier Loogle replies are retained as
diagnostics; the independent semantic searches and source greps support the
no-match verdicts.

The checks against delivery-errors B-E still hold: the new nodes introduce their
objects and have empty proofs, there is no self-citation or new circular
hypothesis, their independent input/output boundaries differ from the parent,
and the small cases in Review by NR remain valid. In particular an empty orbit
boundary and dimension zero are permitted; a group is nonempty, no action is
assumed faithful, and no finite-field rational-point choice enters. The assembly
has no step longer than 2000 characters. Every original argument remains in the
retained ten-step text below. No statement correction or change of route was
needed for this promotion return.

## Retained previous reports (superseded)

The following history is preserved for sources and searches. Its old dispositions
and stage-2 proposal are superseded by this stage-1 re-split.

# Stage-1 return repair: lem-sfb-ample-curve-two-section-pencil

Group NR, 2026-10-22. This item is already split and independently reviewed live.
NH's stage-1 FIX 4ac7306e2 and Q16's stage-2 PASS 646b69305 supersede the returned
NR stage-2 rebind. This repair withdraws that rebind. It claims neither a new split
nor a finished Lean proof. The exact existing theorem ends in `sorry`, and is under
Sheaf/, not a sorry-free project declaration under WeilConjectures/; ATTACH is inapplicable.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ample-curve-two-section-pencil.json:
  restored verbatim field values from the current live DAG; no statement, proof,
  dependency, blueprint, Mathlib-search, review or ownership change is proposed.
- citations.json: verbatim statement quotes for all 27 step/citation pairs of the
  live ten-step proof. Full statements are quoted so no required clause is elided.
- report.md: this stage-1 repair and Review by NR; the earlier report is retained
  below as historical evidence, and its proposed rebind and validation do not apply
  to this repair.

New nodes: 0. Mathlib leaves: 0. No new search record is asserted. The inherited
node searches are retained. No unit or chapter record is changed.

## Attachments

None. `AlgebraicGeometry.Scheme.Modules.exists_ample_curve_two_section_pencil`
in lean/Sheaf/AlgebraicGeometry/AmpleCurveTwoSectionPencil.lean:185 is Q16's
already-owned statement with a sorry proof, not a finished proof or a new attachment.

## Wanted literature

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, section 3.4(b),
printed p.606, for lem-sfb-ample-curve-two-section-pencil. This repair does not
claim a fresh reading of that unavailable local PDF. The node explicitly marks
the strengthened orbit construction as agent-written; its concrete Stacks inputs
were read locally, as detailed below. The earlier worker's publisher reading is
retained in the historical report.

## Return addressed

1. Wrong lane and report form (A2/A7): the proposed stage-2 binding is withdrawn.
   This report is a stage-1 repair with the required Review by NR. The historical
   Second reading section below is not offered as stage-1 independent review.
2. Ownership overwrite (H1/H2): restored the complete live lean record, including
   by=Q16, existing=false and the owning file path. Also restored the live lean_audit;
   the sandbox had drifted in this maintainer-owned field since the returned packet.
   No Lean source is supplied or changed, and no compiler was invoked.
3. Supersession: compared every top-level field of the sandbox item with the live
   item. Initially only lean and lean_audit differed. The statement, ten proof steps,
   proof_deps, split_report and NH/Q16 reviews were already identical. After repair
   every item field agrees with live. There is no mathematical defect reported by
   the return and no remaining authorized stage-1 split delta. The delivery tool's
   result below determines whether it can represent that supersession without
   inventing a node change.

## Historical Review by NR

I read the current item's full statement, ten proof steps and the statements of
all cited nodes, plus its chapter and sk-thm-sf-ctf-stability unit. The statement
allows finite fields, dimension zero, nonreduced/reducible schemes, and nonfaithful
actions; it requires projectivity, finite type, ampleness and nonemptiness. The
argument stays below the existing local-pencil input and changes no unit route.
There is no new statement to test, new node to search, or new dependency to accept.

Step 1 uses lem-weil-pbc-finite-type-over-noetherian to get a Noetherian scheme,
lem-sc-noetherian-closed-subset-finite-components for a finite covering, and
lem-weil-pbc-scheme-sober for unique generic points. Their statements explicitly
supply these facts. A field is Noetherian by its two ideals. Finite type is an
item hypothesis, so the Noetherian-base requirement holds.

Steps 2 and 4 use lem-sc-ample-finite-principal-affine. I read properties.tex,
lemma-ample-finite-set-in-principal-affine (09NV), lines 5291 onward: its finite
set may consist of arbitrary points, and W can be Y. Thus both E and E union T
qualify; no rational-point or infinite-field hypothesis is smuggled in. The finite
group reindexing proves that T is stable, directly in step 4.

Step 3 uses def-kun-topological-krull-dimension's chain definition and proves the
length-two contradiction explicitly. lem-sc-zero-dim-noetherian-closed-finite
requires a Noetherian T0 topological space, not merely a Noetherian scheme.
The live FIX correctly cites lem-weil-pbc-noetherian-scheme-closed-subsets-minimal
for precisely that topological hypothesis, and scheme sobriety gives T0.
I read properties.tex, lemma-Noetherian-topology (01OZ), lines 494 onward, and
lemma-locally-Noetherian-dimension-0 (0AAX), lines 1285 onward. The cited finite
closed-set lemma states the required topological conclusion explicitly. The empty
Z case is allowed, and no dimension-exactly-one hypothesis is used.

Step 5 uses clauses (2) and (3) of lem-weil-pbc-invertible-pullback-tensor to
construct the positive powers and compare residue values. The one-dimensional
vector-space scalar check is written out; p,q>0 imply pq>0. I read modules.tex,
lemma-tensor-product-pullback (01CD), lemma-stalk-tensor-product (01CB), and
lemma-constructions-invertible (01CT). These support the cited tensor statements.

Step 6 uses lem-weil-pbc-invertible-generating-sections-fibre, whose statement
says exactly that the union of the nonvanishing opens gives generation. The
orbit-disjointness argument is in the step itself, using stability of T and the
identity group element. Step 7 uses clauses (1)-(3) of the tensor lemma and the
same fibre-generation criterion. Each residue field extension is injective;
a finite tensor of nonzero vectors in one-dimensional spaces is nonzero. Thus
the norm zero sets really are the orbit unions; nilpotents are not discarded
from the asserted generation of the invertible sheaf.

Step 8 uses def-weil-pbc-morphism-to-projective-space-by-sections for the
structure map and uniqueness over Spec F, lem-weil-pbc-projective-space-functor-of-points
for the coordinate pair, lem-weil-pbc-projective-space-standard-charts for the
affine covering and nonvanishing interpretation, and the tensor lemma's fibre
formula for pullbacks. I read constructions.tex lemma-projective-space (01NE),
lines 2783 onward, and lemma-standard-covering-projective-space (01NG), lines
2858 onward. All four chart preimages in the step follow from those statements.

Step 9 uses lem-kun-projective-implies-proper and def-weil-proper-morphism to
obtain separatedness of Y over the affine Spec F. The statement of
lem-weil-pbc-separated-affine-open-intersection therefore applies successively;
G is nonempty, so no empty-intersection-affineness assumption occurs. I read
schemes.tex lemma-characterize-separated (01KP), lines 4155 onward, which
requires a common affine open in the base, supplied here by Spec F.
pqf-lem-affine-local-target then gives affineness from the two chart preimages;
I read morphisms.tex lemma-characterize-affine (01S8), lines 1734 onward.
lemma-nagata-projective-space-base-change-proper and the proper definition give
a separated target over F. The over-F identity from step 8 satisfies the exact
hypothesis of lem-weil-pbc-proper-over-separated; morphisms.tex
lemma-image-proper-scheme-closed (01W6), lines 9947 onward, gives properness.
Finally lem-sfb-affine-proper-finite states the general-morphism equivalence,
matching morphisms.tex lemma-finite-proper (01WN), lines 11161-11168. The live
FIX's replacement of the dropped citation is essential: the field-structure-map
special case would not suffice for a target P1. I retained this live replacement.

Step 10 uses the tensor lemma's pullback-composition and permutation clauses
and the functor-of-points lemma's pullback compatibility and equivalence of
pairs. Reindexing by g to gh carries BOTH norm sections through the SAME
isomorphism. Uniqueness in the coordinate-morphism definition then proves equality
over F, since the action is by F-automorphisms. This is equality of scheme
morphisms, not just equality on points, including for nonreduced Y.

The small cases remain valid: Spec F admits a finite constant-image map;
trivial G gives the ordinary pencil; repeated automorphisms in nonfaithful
G still contribute tensor factors; empty zero sets are allowed; positive
exponents preserve nonvanishing in every characteristic. No step exceeds 2000
characters. I checked B-E against this existing split: no new nodes, hollow
statement, moved clause or new uncited claim has been introduced by this repair.
The concrete corrections concern lane, report and ownership only. NH's split
and Q16's owner must remain in force. The dispatcher forbids further agents,
so this is the author's self-audit; independent review remains the maintainer's.

## Validation for this repair

The first required deliver.py --no-push invocation exited 1: report.md lacked
'## Historical Review by NR'. The repaired deliver.py --no-push invocation completed with exit 1 and printed:

PREFLIGHT FAILED, nothing pushed. Three reasons:
1. the item's node file is unchanged;
2. the human 2026-10-21 re-split gate counts 6791 proof characters and requires at
   most 3000;
3. that gate requires at least 2 new nodes; this packet adds 0, with 1 cited new
   node already landed for the note.

BLOCKED: The returned assignment is explicitly superseded by NH's reviewed live
split and Q16's module ownership. Preserving that live state leaves no authorized
stage-1 node delta; the preflight refuses that safe repair and applies a prior
re-split requirement to the already reviewed node. The brief says live
split-and-reviewed nodes win and are never split, and forbids patching a gate or
working around it. No artificial node change or cosmetic re-push was made. The
maintainer/dispatcher must retire the superseded return or explicitly assign a
fresh re-split under the current gate. No push was attempted. The original
stage-2 report remains below only as historical evidence.

## Historical returned stage-2 report (withdrawn proposal)

Everything below is retained from the prior attempt. Its proposed existing=true
record and its stage-2 validation are superseded and are not current claims.

## Worker report

Item: lem-sfb-ample-curve-two-section-pencil. Group: NR. Stage: 2.

The live project already contains the exact declaration
`AlgebraicGeometry.Scheme.Modules.exists_ample_curve_two_section_pencil` in
`Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`, at
`lean/Sheaf/AlgebraicGeometry/AmpleCurveTwoSectionPencil.lean:185`.
Its node has an independently reviewed Q16 statement record dated 2026-10-22.
Following brief-stage2 sections 1 and 5, this delivery records that declaration with
`existing: true`; it supplies no duplicate module. Only the item's `lean` field changes.
The statement signature is copied verbatim from the source, with all binders explicit.
All nine auxiliary definitions and the full theorem docstring were read.

Every hypothesis and clause matches as follows. Names in the table belong to
`AlgebraicGeometry.Scheme.Modules` unless qualified otherwise.

| Node hypothesis or clause | Existing Lean rendering |
| --- | --- |
| Any field F, including finite fields | `(F : Type u) [Field F]`; no infinitude or characteristic restriction |
| Nonempty scheme Y over F | `(Y : Scheme.{u}) [Nonempty Y] (f : Y ⟶ Spec (CommRingCat.of F))` |
| Projective over F | `[IsHProjective f]`, the recorded finite-projective-space embedding convention |
| Finite type over F | `[LocallyOfFiniteType f] [QuasiCompact f]`, the recorded conjunction |
| Topological dimension at most one | `(hdim : topologicalKrullDim Y ≤ 1)` |
| Ample invertible L | `(L : Y.Modules) [L.IsInvertible] (hL : IsAmple Y L)` |
| Finite group of F-automorphisms | `(G : Type v) [Group G] [Finite G] (ρ : G →* Aut Y)` with `(hρ : ∀ g, (ρ g).hom ≫ f = f)` |
| Faithfulness unnecessary | There is no injectivity assumption on ρ |
| B is the tensor product of g*L | `pencilOrbitBundle (fun g ↦ ρ g) L` enumerates G once and recursively tensors actual `tensorPullback` modules |
| Norm section in B tensor power d | `pencilNormSection (fun g ↦ ρ g) L d s` tensors the pullbacks of s, then transports by `pencilTranslatePowerIso` |
| Canonical permutation of tensor factors | `pencilTranslatePowerIso` uses `boundaryPullbackPowIso`, `tensorPowTensorObjIso`, and recursive unitors; it introduces no arbitrary isomorphism |
| Positive exponent and sections a,b | `∃ d : ℕ, 0 < d ∧ ∃ a b : (L.tensorPow d).sections` |
| Z(s) is the residue-value zero locus | Complement of `nonvanishingLocus (L.tensorPow d) (s.val (op ⊤))`; the recorded nonvanishing definition is the germ outside maximal ideal times stalk |
| Disjoint orbit zero unions | `Disjoint (⋃ g, (ρ g).hom ⁻¹' (...)ᶜ) (⋃ g, (ρ g).hom ⁻¹' (...)ᶜ)` with a and b respectively |
| a,b generate L tensor power d | Existential `ha : Epi ((L.tensorPow d).freeHomEquiv.symm (pencilSectionPair ... a b))` |
| The two norm sections generate B tensor power d | Existential `hN : Epi (...freeHomEquiv.symm (pencilSectionPair ... (pencilNormSection ... a) (pencilNormSection ... b)))` |
| Ordinary map to the projective line is finite | First `IsFinite (pencilCoordinateMorphism f (L.tensorPow d) inferInstance a b ha)` |
| Norm map to the projective line is finite | Second `IsFinite (pencilCoordinateMorphism f _ hB (pencilNormSection ... a) (pencilNormSection ... b) hN)` |
| Both maps are the specified maps over F | `pencilCoordinateMorphism` is the existing `ProjectiveSpace.homOfGeneratingSections (ULift (Fin 2)) f ...`; its projection is f |
| Norm map is G-invariant | `∀ g : G, (ρ g).hom ≫ pencilCoordinateMorphism ... = pencilCoordinateMorphism ...`, equality of scheme morphisms |
| No smoothness, reducedness or irreducibility assumption | None occurs among the binders |

The additional existential `hB` is a proof of invertibility of the constructed norm
bundle power, needed to type the existing coordinate API. It is a conclusion, not an
extra input hypothesis. The pair is indexed by `ULift.{u} (Fin 2)` to meet Mathlib's
coefficient-universe free-sheaf API, with exactly the two entries a and b. Global sections
as compatible families and sections on the top open are converted by existing canonical
section/Hom equivalences. The explicit f is also the structure map used in hρ, so it
represents the same scheme over F, not a second arbitrary morphism.

Dependency declarations read, including signatures and docstrings:

- def-weil-field: `Field` in `Mathlib.Algebra.Field.Defs`.
- def-kun-projective: `AlgebraicGeometry.IsHProjective` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- def-kun-topological-krull-dimension: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, taking values in `WithBot ℕ∞`.
- def-sc-invertible-module: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.
- def-weil-pbc-ample-invertible-module: `AlgebraicGeometry.Scheme.Modules.IsAmple`
  and `nonvanishingLocus` in `WeilConjectures.AlgebraicGeometry.Ample`.
- def-pur-sheaf-tensor-product: `SheafOfModules.cochainModulesMonoidal` in
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`; the existing module
  publicly imports this recorded interface and uses the established scheme tensor.
- def-pc-module-pullback: `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  `tensorPullbackSection` and `tensorPullbackSectionAdjunction`, publicly exposed by
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`.
- def-weil-pbc-generating-sections: `SheafOfModules.GeneratingSections` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`; its exact generation predicate
  is `Epi (M.freeHomEquiv.symm s)`.
- def-weil-pbc-morphism-to-projective-space-by-sections:
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections` in
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`.
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.

The existing helper `boundaryPullbackPowIso` from
`WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons` has no immersion
or square-zero hypothesis; its actual recursive definition was read. The existing
`tmulSection` and `unitSectionsEquiv` construct the tensor section and its unit tail.
No new notion, dependency repair or theorem is needed. The existing theorem has the
expected single `sorry` proof and the complete ten-step proof plan in its docstring.

Edge cases checked against the statement and construction:

- Dimension zero, including Spec F: a map with constant image can be finite; no
  surjectivity onto the projective line or dimension exactly one is asserted.
- Finite F and all characteristics: no infinite-field parameter argument is used.
- Trivial G and nonfaithful actions: every group element contributes a factor, even
  when automorphisms repeat; no quotient or faithfulness witness is required.
- Reducible, disconnected and nonreduced schemes remain allowed. Generation uses sheaf
  epimorphisms and invariance uses scheme-morphism equality, so nilpotents are retained.
- Empty zero loci are allowed. Y itself is excluded from being empty exactly by Nonempty.
- Degree zero is excluded by `0 < d`; the helper constructors still have real data at zero.
- The independent group universe v does not restrict which finite group can act.

Searches performed with the prescribed msearch.py wrapper:

1. LeanFinder query: "A power of an ample invertible sheaf on a projective curve has two
   generating global sections defining a finite map to the projective line, with disjoint
   finite group orbit zero loci". Eight results: `Proj.fromOfGlobalSections` and unrelated
   Weierstrass-curve declarations; none states this theorem.
2. Loogle query: `tensorPow, tmulSection, IsAmple`. Zero results; the service reports
   unknown identifier tensorPow. This limited result was supplemented by source search.
3. Mathlib grep query: `normSection|twoSection|IsAmple`, subdirectory AlgebraicGeometry.
   Zero results.
4. Source rg searches in lean/WeilConjectures and lean/Sheaf for
   `normSection|orbitTensor|two_section_pencil|ample_curve|twoSectionPencil` found the
   exact existing theorem at AmpleCurveTwoSectionPencil.lean:185. Its full module was read.
5. Source search for the item id in lean/WeilConjectures returned no hits. A DAG search
   found the Q16 record of the same theorem, with reviewed_lean pass. The upstream name
   index contains no alternative exact match.
6. Broader tensor/section searches located the existing pullback-power comparison,
   `tmulSection` and `unitSectionsEquiv`. A broader norm search found
   FiniteNormInvertibleSections, which concerns finite-morphism norms and is not this
   finite-group orbit-pencil statement.

Source check: read the special-fibre finite-pencil input in
[de Jong, §3.4(b), printed p.606](https://www.numdam.org/item/10.5802/aif.1575.pdf), and the local Stacks coherent.tex
lemma-kill-by-twisting, Tag 02O1. The node explicitly supplies its own strengthened
orbit-separation argument; the existing declaration matches that strengthened node.
No STATEMENT-DISPUTED issue or node statement correction was found.

Validation: the prescribed deliver2.py --no-push dry run passed preflight and the
module-mode server #check of the existing declaration and all nine recorded auxiliary
declarations through scompile.py. It printed OK with no compile errors or unexpected
warnings. No new Lean module is delivered.

## Second reading by NR

The dispatcher explicitly prohibits starting other agents. This section records a
separate self-audit with the full node and existing module open; it does not claim a
second worker's reading. The maintainer independently reviews the delivery. The earlier
Q16 binding also has a recorded independent reviewed_lean pass.

The audit rechecked every table entry, especially the actual tensor-power target of the
norm, the two Epi generation witnesses, both finite maps, and invariance as equality of
scheme morphisms. All nine helpers contain real constructions; the tensor comparison
uses canonical unitors and symmetric distribution, not a selected arbitrary isomorphism.
No mathematical mismatch was found. The only record changes are existing=true, removal
of file, NR/date attribution, a verbatim signature and an explanatory lean.note.


## Dispatcher repair retry, 2026-10-22

Re-read the actual open return in coord/returns/NR.md, head 768365a5410,
and compared the retained sandbox with the current live DAG without running
git in the shared repository. The only sandbox node is the item; every parsed
field equals live, including the NH reviewed split and the Q16 owning lean record
(existing=false, file=lean/Sheaf/AlgebraicGeometry/AmpleCurveTwoSectionPencil.lean).
The return's ownership overwrite is withdrawn and the required Review by NR
section is present. Retained the earlier report, source discussion and searches.
No new search is claimed and no node or Lean source was changed in this retry.

Re-read the item, chapter, unit, all 19 proof-dependency statements and the B-E
return checklist. All 27 citations cover exactly the step/node uses, and each
quote remains a verbatim substring of the current cited statement. No individual
non-elementary step exceeds 2000 characters. The existing Lean theorem at line
185 still ends in sorry, so it cannot justify ATTACH.

Ran the required single deliver.py NR lem-sfb-ample-curve-two-section-pencil
--no-push invocation, waited through shared fetch and server preflight, and polled
that same process until it exited 1. Its final output again states:

1. the item's node file is unchanged;
2. the proof has 6791 characters and must be at most 3000;
3. at least two new nodes are required, but this packet adds zero (one cited
   new node had already landed for the note).

PREFLIGHT FAILED, nothing pushed. This reproduces the previous blocker rather
than identifying an unrepaired mathematical defect. The open return explicitly
calls the delivery superseded, while brief-stage1's isolated-run rule says live
split-and-reviewed nodes win and must never be split. No cosmetic node mutation,
duplicate lemma creation, gate patch or prohibited push was attempted. Resolving
the superseded return versus the re-split gate requires the maintainer/dispatcher;
all retained sandbox work is preserved. Outcome: BLOCKED by contradictory
preflight requirements on a superseded, already-reviewed item.


## Current promotion-return repair and review by NR — 2026-10-23

The returned head is 2f5f7219da4, identified by L's open return in
coord/returns/NR.md. Its reported fault was failure to promote a side completion,
not rejection of the mathematical split. I continued the retained repair, including
its expanded tensor comparison, complete old proof, citations and search log.
The required first dry run exited 0 at bab06a3baf2 on this retry; deliver.py fetches
origin/sheaf-dag and constructs the delivery on that base. I ran no git command in
the read-only repository. This receipt validates the retained repair before the
additional hypothesis clarification made here; a fresh final dry run follows.

Comparing all parsed item fields against the current read clone again finds only
proof, proof_deps and split_report different. In particular the statement and its
notions, source, chapter/unit, blueprint, Q16 module ownership and both review
records agree. The current released S1 repair order still requires two independent
nodes. Neither new id is present in the current DAG. Thus the short assembly and
two unsplit nodes remain the substantive delta that must be promoted; merely
re-pushing the old ten-step node would lose the human's ordered distribution.

I re-read the seven distinct statements giving all eight step/citation pairs.
Step 1 uses the finite-type theorem with the Noetherian base Spec F and the first
new node with nonempty Noetherian Y, dimension at most one, ample invertible L,
and the given finite action. Step 2 uses the tensor-fibre formulas and the exact
fibre-generation equivalence. Its positive-power scalar argument and stable-orbit
argument are explicit. Step 3 uses projective-implies-proper and the second new
node with M=L^d. I added an explicit check that M is invertible by tensor closure
before applying that criterion. The tensor lemma's section-compatible pullback
isomorphism and factor permutation give one isomorphism carrying both norm
sections; the functor-of-points statement says equivalent generating pairs have
the same morphism. The fixed map to Spec F then identifies the F-morphisms,
so both finiteness and invariance transport to the exact pair in the statement.
Every quote remains verbatim in the currently cited statement; there is no
changed cited assertion that requires replacing a dependency.

I opened properties.tex at lemma-ample-finite-set-in-principal-affine (09NV)
and lemma-locally-Noetherian-dimension-0 (0AAX), constructions.tex at
lemma-projective-space (01NE), and morphisms.tex at
lemma-image-proper-scheme-closed (01W6) and lemma-finite-proper (01WN).
09NV accepts arbitrary finite scheme-point sets, including component generic
points and finite closed orbit sets over finite fields. The dimension-chain
argument in the retained proof supplies the zero-dimensional boundary; the
current sobriety, finite-component and Noetherian-topology statements supply its
other hypotheses. 01NE classifies pairs up to a section-preserving isomorphism,
not just pointwise values. 01W6 applies since P1_F is separated and Y is proper;
01WN is the general morphism criterion needed by the supplied-pair lemma.
The de Jong PDF is still wanted locally; no new publisher reading is claimed.

I also re-opened the separated-affine-intersection, affine-local-on-target,
proper-over-separated, proper-projective-space and affine-proper-finite
statements supporting the preserved arguments for the new statement-only tasks.
They still give precisely the hypotheses/conclusions described in the earlier
review. The finite group is nonempty, so finite intersections of translates
begin with an affine open rather than an unsupported empty intersection.
Dimension zero and empty boundary require no changes; a trivial or nonfaithful
action is allowed. Nonreduced schemes are handled by residue generation and
scheme-morphism equality, with no reducedness inference. The proper-pair lemma
allows the empty scheme as well.

The whole-blueprint ancestor and searches for 'orbit pencil' and '09NV' were
rerun on this current DAG: the ancestor remains null and both blueprint searches
return zero matches. Current whole-DAG keyword/tag searches were inspected;
the retained Not duplicates distinctions remain applicable. The authentic
Mathlib log was read and reused because the two new statements and search
questions are unchanged; no new Mathlib searches are recorded. The existing
project theorem at AmpleCurveTwoSectionPencil.lean:185 still ends in sorry and
WeilConjectures contains no exact proved attachment.

All B-E checks remain satisfied: the two new nodes have self-contained statements,
empty proof/proof_deps and explicit notion dependencies; no parent clause is
moved into a duplicate of the parent; no proof cycle or new source/hypothesis
change was introduced. All assembly steps are below 2000 characters and the
assembly stays below 3000. The only new edits this retry are the explicit
invertibility check, refreshed split report and this signed current review.
The independent landing review and promotion remain L's responsibility.
