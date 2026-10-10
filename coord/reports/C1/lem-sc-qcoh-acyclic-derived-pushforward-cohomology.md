Files written:
- dag/nodes/sec-picard-framework/lem-sc-qcoh-acyclic-derived-pushforward-cohomology.json (split item)
- dag/nodes/sec-picard-framework/lem-sc-qcoh-acyclic-derived-sections-comparison.json (new unsplit statement node; Mathlib no match)
- citations.json

Attachments:
- None. No sorry-free declaration with the exact item statement was found in WeilConjectures.

WANTED:
- None.

What was wrong or incomplete in the imported item:
- The imported item had no proof and its unbounded comparison was only described by reference to the “small detail omitted” in Tag 0AVW. I made the Tag 08D4 application explicit through affine-open sections and added the missing local statement node.

What could not be finished:
- The new local comparison node is intentionally unsplit because it is the Stacks Tag 08D4 foundational result and no smaller existing DAG node states it.

## Not duplicates
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-sc-qcoh-acyclic-derived-pushforward-cohomology: the new node is the affine-open section-level comparison and restriction compatibility; the existing item is the resulting global sheaf isomorphism for Rf_*.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-pc-derived-direct-image-preserves-qcoh: the new node compares cohomology of derived sections with sections of cohomology under acyclicity; the existing node only states preservation of quasi-coherence by Rf_* for qcqs morphisms.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-pc-derived-direct-image-uniform-truncation-bound: the new node gives an unbounded cohomology comparison on affine opens; the existing node gives a uniform positive-degree truncation bound for qcqs morphisms.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-sc-affine-derived-pushforward-t-exact: the new node is for arbitrary morphisms satisfying acyclicity and local sections; the existing node is t-exactness and conservativity specifically for affine morphisms.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-sc-finite-affine-derived-equivalence: the new node is a local cohomology comparison; the existing node is an equivalence of bounded-below derived categories for finite affine morphisms.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-sc-affine-derived-concentration: the new node compares all cohomological degrees on affine opens; the existing node characterizes complexes concentrated in degree zero for affine morphisms.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-sc-affine-derived-cohomology: the new node is the local Tag 08D4 input; the existing node is the global affine derived-pushforward theorem that applies it.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-pc-unbounded-derived-functor-cohomological-bound: the existing node gives only the upper cohomological vanishing bound for a general additive functor, while the new node gives the acyclic comparison isomorphism and restriction/sheafification data for sections.
lem-sc-qcoh-acyclic-derived-sections-comparison vs lem-pc-derived-sections-pushforward-comparison: the existing node compares derived global sections of $Rf_*$ with source sections, while the new node compares those derived sections with ordinary sections under acyclicity and records restriction and sheafification.

## Review by C1
I reread the item and the new section-comparison node, the blueprint ancestor `lem-sc-finite-duality`, and the existing affine derived-cohomology node. I corrected the item and new node to assume that f is quasi-compact and quasi-separated. This is used in Step 1 through Tags 01XJ and 01XB to make f_*F quasi-coherent; Leray then identifies H^p(f^{-1}(V),F) with H^p(V,f_*F), which vanishes on affine V. I also recorded the countable-product condition required by Tag 08D4. The new node states exactly the resulting affine-open comparison and restriction compatibility, so the Step 1 citation supplies its full conclusion.

Step 2 now explicitly constructs an isomorphism of presheaves on the affine basis: the derived-direct-image definition identifies the left presheaf with V ↦ H^i(Rf_*E) on that basis, while Step 1 identifies it with V ↦ Gamma(f^{-1}(V),H^i(E)), the affine restriction of f_*H^i(E). It does not identify sections of the sheaf H^i(Rf_*E) with cohomology of a section. Step 3 uses the cited restriction compatibility and the fact that f_*H^i(E) is a sheaf to sheafify this affine-basis presheaf isomorphism; naturality follows from the cited functorial comparisons. The citation quotes were updated verbatim after these statement changes. I checked the edge cases f=id, an affine morphism of affines, the zero complex, and arbitrary cohomological degree, and reran the DAG and delivery preflight checks.

## Repair
The maintainer's two return points are repaired: qcqs is present in both dependent statements and Step 1 derives acyclicity via Leray, quasi-coherence, affine vanishing, and the product hypothesis; Steps 1--2 now compare presheaves on the affine basis, and Step 3 invokes sheafification rather than a false sectionwise equality.

The second return point is repaired precisely: the local comparison node now states `H^i(RGamma(f^{-1}(V),E)) = Gamma(f^{-1}(V),H^i(E))`. Step 1 uses that isomorphism, and Step 2 uses the comparison presheaf `V -> Gamma(f^{-1}(V),H^i(E)) = Gamma(V,f_*H^i(E))`; no occurrence remains of `H^i(Gamma(f^{-1}(V),E))`.

## Second reading by C1

- Item statement: checked against Stacks Tag 0AVW (perfect.tex) and the qcqs hypotheses; agrees, including unbounded $D_{\\mathrm{QCoh}}$ objects, all integers $i$, and naturality.
- Step 1: checked against Tags 01XJ, 01XB, 08D4, 08D5 and affine vanishing; the acyclicity and countable-product hypotheses are explicitly in force and the local comparison citation supplies restriction compatibility.
- Step 2: checked against Tag 0AVW and the derived-direct-image definition; repaired to use the presheaf $V\\mapsto H^i(R\\Gamma(f^{-1}V,E))$ and its sheafification, avoiding a false sectionwise identification.
- Step 3: checked against Tag 0AVW and the restriction clause of the section-comparison node; sheafification and naturality are the stated elementary gluing argument.
- New node `lem-sc-qcoh-acyclic-derived-sections-comparison`: checked against Tag 08D4 (parts (1),(2), $N=1$), Tag 08D5, and the Tag 0AVW construction; statement is self-contained with scheme, qcqs, acyclicity, derived-category, restriction, and sheafification notions cited.

Changes made: added the canonical sheafification clause and its sheafification definition dependency to the new node; rewrote Step 2 and its verbatim citations to use that clause; removed the duplicate citation entry.  Edge cases checked were $f=\mathrm{id}$, an affine morphism of affines, the zero complex, the empty scheme, and arbitrary degree $i$; all are consistent.  Blueprint references, recorded Mathlib searches, and the no-duplicate search were rechecked; the new node has no Mathlib declaration or existing DAG duplicate.
