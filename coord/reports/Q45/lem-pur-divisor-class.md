# Stage-1 delivery report: lem-pur-divisor-class

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-divisor-class.json`: repaired item split; statement and Lean audit records unchanged.
- `dag/nodes/sec-smooth-purity/lem-pur-divisor-relative-cone.json`: new statement node, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-divisor-torsor-boundary-signs.json`: new statement node, no Mathlib match.
- `citations.json`: verbatim statement quotes for every proof-step citation.

## Attachments

None. The item and both new nodes have no finished declaration in the read-only source checkout.

## WANTED:

None.

## Not duplicates

- `lem-pur-divisor-relative-cone` vs `lem-pur-support-localization-triangle`: the existing node states an open-closed derived triangle for pro-etale sheaves; the new node identifies the explicit relative section cone with the kernel-of-restriction support complex, fixes the signed representative and localization boundary, and includes etale/pro-etale cone comparison and coefficient naturality.
- `lem-pur-divisor-relative-cone` vs `lem-pur-support-restriction-triangle`: the existing node is a triangle relating three different supports; the new node is the quasi-isomorphism from the support kernel to the relative restriction cone and its topology comparison.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-amb-relative-torsor-cohomology`: the existing node gives the abstract torsor-with-section bijection and natural connecting maps; the new node computes the signed cone representative, both localization signs, and their resolution-level Kummer compatibility.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-torsor-h1`: the existing node identifies ordinary H^1 with torsors and contracted products; the new node uses its canonical extension to compute relative representatives with a specified open section.

- `lem-pur-divisor-torsor-boundary-signs` vs `lem-weil-pbc-gabber-h1-absolutely-algebraically-closed`: vanishing of ordinary constant finite-sheaf H^1 on a closed subscheme of a normal affine with separably closed fraction field, rather than relative representatives or boundary signs.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-weil-pbc-finite-etale-equivalence-h1`: ordinary constant finite-sheaf H^1 invariance under finite-etale equivalence, rather than signed relative connecting maps.
- `lem-pur-divisor-torsor-boundary-signs` vs `def-amb-relative-etale-cohomology`: defines the relative cone and its projection, but does not compute the torsor representative or the two connecting signs.
- `lem-pur-divisor-torsor-boundary-signs` vs `def-amb-torsor-with-section`: defines pairs and their isomorphism classes; no cohomology or boundary formula is asserted.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-inverse-image-lifts-fibre`: compares lifting torsors under inverse image, without a specified open section or signed relative cohomology representative.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-contracted-product-exists`: constructs a coefficient pushout torsor and its universal property, without the relative boundary calculation.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-torsor-inverse-image-extension`: compares canonical torsor extensions under inverse image, without their relative resolution cocycles and boundary signs.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-contracted-product-exists-data`: constructs the sheafified orbit quotient and its action, without a relative cohomology class or connecting-map formula.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-inverse-image-lifting-torsor`: compares a torsor of lifts and its inverse image, without the signed relative representatives.
- `lem-pur-divisor-torsor-boundary-signs` vs `def-sc-torsor-extension-presentation`: defines the canonical extension presentation and its universal property; it does not compute the relative resolution representative.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-contracted-product-exists-universal`: states the quotient universal property, without the relative localization or short-exact-sequence connecting maps.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-torsor-h1-functoriality`: ordinary H^1 functoriality for inverse image and coefficient pushout, without a specified complement section or the relative connecting sign.
- `lem-pur-divisor-torsor-boundary-signs` vs `lem-sc-etale-torsor-pushout-extension`: identifies the coefficient pushout of a canonical extension with the extension of the contracted product torsor, without the relative representative and boundary equality.

## What was wrong in the returned split

The return correctly identified that the former steps 5 (2250 characters) and 6 (2361 characters) hid non-elementary lemmas. I retained their route and all other proof steps, and extracted exactly those arguments into the two new statement-only nodes. No statement, coefficient category, or source route was changed.

## Review by Q45

I compared the retained item with the current repository item and read both the master blueprint proof and the current `main-20261015` proof. I read the statement of every dependency used by the item and both new nodes, including the support definition, relative cone definition, etale and pro-etale sites, injective resolutions, site comparison, torsor extension, torsor H^1 classification, Kummer sequence, and split injective-resolution lemma.

Step 5 now cites `lem-pur-divisor-relative-cone`, whose statement supplies the exact kernel/cone quasi-isomorphism, the support identification, the forget-support projection, the localization boundary, etale/pro-etale comparison, and naturality under coefficients, restriction, and enlargement of support. The support definition and frame coefficient map supply the remaining construction. Step 6 now cites `lem-pur-divisor-torsor-boundary-signs`, whose statement gives the canonical torsor extension, the representative `(0,g)`, the negative localization sign, and the equality between the relative Kummer connecting class and the positive localization boundary of the ordinary Kummer class. The frame definition and frame-independence node supply the final local formula and equation independence. Both new statements explicitly introduce their schemes, closed-open pairs, sheaves, resolutions, and hypotheses.

I checked the local sign on the displayed differential `D(a,b)=(da,res(a)-db)`: the trivial torsor section gives `(0,g)`, localization gives `(0,-g)`, and a split Kummer lift gives `(0,-dr)`, so the final Kummer boundary has positive sign. I checked every `uses` entry against the cited statement and every `citations.json` quote as a verbatim substring. All proof steps are below 2000 characters; the new nodes are statement-only, have blueprint ancestry and `lean_audit` records, and each has recorded LeanFinder, Loogle, grep, and LeanSearch searches with no matching Mathlib declaration. No SGA 4 source is used.

## Resumed reading and checks

I resumed the retained repair rather than regenerate it. Against the current shared item, the only changed fields are `proof`, `proof_deps`, `status`, and `split_report`; the statement, Lean record, audit, and steps 1–4 and 7–8 agree byte for byte. The two new statements express the arguments formerly in steps 5 and 6, rather than new clauses about divisors. Their recorded searches were read from `searches.jsonl` and retained. The Mathlib `PresheafOfGroups.H1` hit was checked in `CategoryTheory/Sites/NonabelianCohomology/H1.lean`: it is a fixed-family presheaf cocycle quotient, whose introduction explicitly leaves derived sheaf cohomology and connecting classes as TODOs. It does not give the relative torsor sign lemma. General mapping-cone and section-restriction declarations in the other search hits do not identify supports on these sites or supply topology comparison.

For step 1 I opened the statements of the smooth-pair coordinate lemma, finite-type Noetherian permanence, and dimension-drop lemma. The first supplies a regular sequence over an arbitrary base; the second applies because all schemes here are finite type over the field; the third applies to each successive local Noetherian quotient and a nonzerodivisor in its maximal ideal. The frame definition's dimension-difference convention then gives one equation. This uses no regularity assumption on the base. Step 2 uses the divisor definition's dual ideal and the line-bundle/torsor statement's frame construction. The displayed dual-basis transition verifies that its specified complement section glues. Step 3 uses exactly the relative torsor statement's canonical bijection, forgotten ordinary class, and pullback naturality. Step 4 uses the arbitrary-base Kummer statement with the invertible integer $m=\ell^n$ and the relative statement's connecting map and forget-support compatibility; the frame definition supplies $mA=0$ and the roots coefficient morphism.

For steps 5 and 6 I reread the original resolution arguments as well as the new statements. The cone statement is the general sheaf-theoretic comparison extracted from step 5, including its topology-change square; it is not asserted to occur verbatim in the short blueprint proof. Its argument remains available here: restriction along the open monomorphism is surjective for injectives, slice restriction preserves injectives, and the quotient of the inclusion of the support kernel in the signed cone is the contractible complex with differential $(x,y)\mapsto(dx,x-dy)$ and homotopy $(x,y)\mapsto(y,0)$. Apply the existing absolute etale/pro-etale comparison to both terms and compare the restriction cones. The existing comparison node allows every abelian etale sheaf, so no torsion or finite-ring hypothesis is being silently imposed on that intermediate comparison. At the final application the support definition permits the finite-torsion pro-etale coefficient $A(1)$.

The sign statement uses Stacks 03AJ (`sites-cohomology.tex`, `lemma-torsors-h1`) for its canonical extension presentation, which I read in full through the two constructions. The relative refinement is the extracted argument of step 6, not a claim that 03AJ already states relative cohomology. Factoring the differential of the extension into the injective resolution gives $(a,b)$; changing its extension changes this by a relative boundary. The specified trivial-torsor section gives $(0,g)$. The split-resolution assertion names precisely the existing injective-resolution short-exact-sequence statement, including its degreewise split option. Thus applying the signed differential to a lift $(0,r)$ gives $(0,-dr)$ and proves the boundary formula with the required sign. There is no assumption that any fixed Cech cover computes higher cohomology.

Step 7 uses the divisor definition to multiply the ideals and the line-bundle/torsor statement to identify tensor and contracted products. The relative torsor statement explicitly supplies naturality under coefficient maps: the two projections and multiplication on $\mathbf G_m\times\mathbf G_m$ give the addition assertion. Finite products commute with the two-term section cone by its componentwise differential; this is the elementary calculation used there. Step 8 uses the relative statement's explicit forget-support compatibility and the frame definition's same roots coefficient morphism; its remaining equality is the definition of $c_1$ in the unchanged item statement.

Small cases for the new cone statement: if $Z$ is empty, $r$ is the identity and the relative cone is contractible; if $Z=T$, $B=0$ and both complexes are $A$; the zero sheaf gives zero groups on both sites. No quasi-compactness of the open complement is used in its section-kernel argument. Small cases for the sign statement: $g=0$ gives the zero class, a section extending globally gives a relative boundary, and a split coefficient sequence has zero ordinary and relative connecting maps. For a unit equation the divisor support is empty and the class vanishes. The source's repeated-divisor test $V(t)+V(t)=V(t^2)$ still belongs to the item's Cartier-divisor clause even though the sum need not be smooth. These checks require no change to the already corrected statement.

The duplicate search was repeated across the current DAG and whole blueprint for relative cohomology, torsors, restriction cones, and Tag 03AJ. I opened the four close statements listed under `Not duplicates`. None states either new comparison with its signed representatives. The new nodes have empty proof lists and proof dependencies and explicit blueprint ancestry; they do not replace the global construction or additivity argument. Every item citation is still a verbatim quote of the cited statement. The longest remaining non-elementary step has 1474 characters, and the returned steps have 748 and 857 characters. This repairs both specifically numbered long-step faults while retaining the requested route.

The first resumed server dry run found missing `chapter` and `unit` fields on both new nodes. I added `sec-smooth-purity` and the inherited `sk-prop-a1-kummer` binding, matching the item; no statement or proof text changed.

## What remains

No unresolved repair point remains.
