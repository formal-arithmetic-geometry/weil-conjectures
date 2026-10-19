# Worker report: lem-trf-proj-qc-open-twist-ample

## Files written

- `lem-trf-proj-qc-open-twist-ample.json`: split target with four proof steps.
- `lem-trf-proj-common-degree-twist-invertible.json`: statement-only node; Mathlib searches found no matching Proj twisting theorem.
- `lem-trf-proj-twist-section-basic-open.json`: statement-only node; Mathlib searches found no matching twisting-section nonvanishing theorem.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

No completed sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this target exactly. The source declarations `AlgebraicGeometry.Proj.isInvertible_twist` and `AlgebraicGeometry.Proj.nonempty_tensorObj_twist_iso` concern degree-one homogeneous covers of the whole Proj and do not state the target's arbitrary graded ring, quasi-compact open, or common-degree restriction result, so they are not attachments.

## WANTED:

None. The Stacks source is available locally.

## Review by Q11

I read the imported target and the relevant source passages in `literature/stacks-project/constructions.tex`: Tag 01MW (the finite homogeneous cover, common degree, invertibility, multiplication, section loci and basis clauses), Tag 01MV (principal-open/nonvanishing identification), and `properties.tex` Tag 01Q2 (open subscheme of Proj has an ample twist). I also read the existing DAG statements `lem-weil-pbc-proj-standard-open-inclusion`, `lem-weil-pbc-proj-graded-module-sheaf-exists`, `def-weil-pbc-proj-twisting-sheaf`, and `def-weil-pbc-ample-invertible-module` before citing them.

Step 1 uses the existing standard-open statement for the basis and finite refinement and the quasi-compactness hypothesis to obtain a finite cover; the degrees remain positive after taking powers to a common multiple. Step 2 uses the new common-degree node, whose hypotheses match those finite homogeneous cover data and whose statement supplies exactly invertibility of every `O_U(ek)` and the tensor multiplication isomorphism. Step 3 uses the new section-locus node for `U_{s_f}=U∩D_+(f)`, and the existing standard-open statement for the basis and affineness of `D_+(f)`; powers put all section degrees in the common-degree progression. Step 4 checks the hypotheses of the ample-module definition: `O_U(e)` is invertible and its positive-power nonvanishing loci contain an affine basis, while Step 2 supplies the requested multiplication maps.

I checked edge cases while auditing the statement: if `U` is empty, the finite cover is empty and the ample condition is vacuous; for `A` concentrated in degree zero, `Proj(A)` is empty; for `A=R[T]` with `U=Proj(A)`, degree `e=1` gives the usual standard affine cover. I searched the whole DAG and blueprint for the two child statements and found no duplicates. The target's imported Mathlib searches were retained; I reran searches for each new node with LeanFinder, Loogle, LeanSearch and Mathlib grep, recording the actual results in their `mathlib_searches` fields. No SGA source was used.


## Repair of returned review

The returned E2/E1/B5 finding is correct. The former child statement claimed that the section of $\mathcal O_U(d)$ attached to every positive-degree homogeneous element cuts out $U\cap D_+(f)$; for $A=k[x,y]$ with degrees $(1,2)$, $U=D_+(y)$ and $f=x$, this is false because $x$ trivializes $\mathcal O_U(1)$ while $U\cap D_+(x)=D(x^2/y)$. I replaced that child by the precise Tag 01MV statement: $U\subseteq W_d$ and $f\in A_{nd}$, with $W_d$ defined by Tag 01MS. Step 1 now uses the finite cover and the Tag 01MS characterization to obtain $U\subseteq W_e$. Step 3 applies the corrected child only to degrees divisible by $e$. Step 4 now checks ampleness separately for every $k\geq1$: taking the $k$-th power of a defining homogeneous element preserves its standard open and makes its degree divisible by $ek$, so the affine section loci required by the ample definition are supplied for $\mathcal O_U(ek)$. I also recorded the off-unit standard-open and ampleness-definition tools in `split_report.tool_uses`, and corrected each child blueprint `via` chain to include the complete item ancestry.

## Not duplicates

- `lem-trf-proj-common-degree-twist-invertible` vs `lem-weil-pbc-projective-ample-invertible`: the existing node concerns the standard twist on a polynomial projective space and a closed subscheme; the new node concerns arbitrary graded Proj and a quasi-compact open with a common-degree cover.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-proj-standard-open-inclusion`: the existing node states topology, inclusions, and affine standard charts; the new node relates those opens to sections of the graded twisting sheaf and their nonvanishing loci.
- `lem-trf-proj-common-degree-twist-invertible` vs `def-weil-pbc-proj-twisting-sheaf`: the existing node defines twists and their local sections; the new node proves common-degree invertibility and tensor compatibility on a quasi-compact open.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-sc-p1-homogeneous-section-tensor-powers-data`: the existing node is only for a field and `Proj k[x_0,x_1]`; the new node is for arbitrary graded rings and opens.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-sc-p1-homogeneous-section-tensor-powers-locus`: the existing node is a P1 nonvanishing-locus statement; the new node is common-degree invertibility and multiplication for arbitrary Proj opens.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-sc-p1-homogeneous-section-tensor-powers`: the existing node is the P1 polynomial special case and includes a specific section; the new node has arbitrary graded-ring cover hypotheses.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-sc-p1-twist-coherent-powers`: the existing node concerns coherence of powers on P1; the new node concerns arbitrary Proj and restriction to a quasi-compact open.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-sc-p1-twist-multiplication`: the existing node is only `Proj k[x_0,x_1]` with degree-one coordinates; the new node allows arbitrary positive degrees and common multiples.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-sc-p1-twist-product-morphism`: the existing node concerns a P1 multiplication morphism; the new node asserts invertibility and all common-degree powers on arbitrary Proj opens.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-weil-pbc-proj-polynomial-twist-chart`: the existing node computes polynomial projective charts; the new node is the common-degree line-bundle consequence on arbitrary graded Proj.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-weil-pbc-projective-space-standard-charts-part1`: the existing node treats standard charts of projective space over a base; the new node treats arbitrary graded rings and an open cover.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-weil-pbc-projective-space-standard-charts-part2`: the existing node treats standard charts of projective space over a base; the new node treats arbitrary graded rings and an open cover.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-weil-pbc-projective-space-standard-charts-part3`: the existing node treats standard charts of projective space over a base; the new node treats arbitrary graded rings and an open cover.
- `lem-trf-proj-twist-section-basic-open` vs `lem-sc-p1-homogeneous-section-tensor-powers-data`: the existing node is the P1 field special case and focuses on tensor-power data; the new node is the arbitrary-Proj section-locus and basis statement.
- `lem-trf-proj-twist-section-basic-open` vs `lem-sc-p1-homogeneous-section-tensor-powers-locus`: the existing node is only `Proj k[x_0,x_1]`; the new node is for arbitrary graded rings and arbitrary opens.
- `lem-trf-proj-twist-section-basic-open` vs `lem-sc-p1-homogeneous-section-tensor-powers`: the existing node is the P1 special case with additional tensor isomorphisms; the new node gives the general section-locus/basis result.
- `lem-trf-proj-twist-section-basic-open` vs `lem-sc-p1-twist-multiplication`: the existing node treats coordinate sections on P1; the new node treats every positive-degree homogeneous section on arbitrary Proj.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-proj-basic-open-intersection`: the existing node identifies intersections with principal opens in the structure sheaf; the new node identifies nonvanishing loci of twisting-sheaf sections and derives a basis.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-projective-space-twisting-sheaf-charts`: the existing node is projective space over Z and coordinate sections; the new node is arbitrary graded Proj and all homogeneous sections.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-projective-ample-invertible`: the existing node concerns a closed subscheme of polynomial projective space; the new node concerns arbitrary graded Proj opens.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-projective-space-standard-charts-part1`: the existing node gives coordinate-chart nonvanishing in projective space; the new node gives the general homogeneous-section locus.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-projective-space-standard-charts-part2`: the existing node gives coordinate-chart nonvanishing in projective space; the new node gives the general homogeneous-section locus.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-projective-space-standard-charts-part3`: the existing node gives coordinate-chart nonvanishing in projective space; the new node gives the general homogeneous-section locus.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-projective-space-standard-charts`: the existing node is a projective-space chart theorem; the new node is arbitrary graded Proj and arbitrary open subschemes.
- `lem-trf-proj-common-degree-twist-invertible` vs `lem-trf-proj-qc-open-twist-ample`: the child states only invertibility and tensor multiplication under an already-given finite common-degree cover; the item additionally constructs such a degree and proves ampleness and section-locus behavior.
- `lem-trf-proj-twist-section-basic-open` vs `lem-trf-proj-qc-open-twist-ample`: the child states only the section-locus/basis identification for a fixed open and fixed homogeneous element; the item additionally constructs a common degree, proves invertibility, and concludes ampleness.
- `lem-trf-proj-twist-section-basic-open` vs `lem-sc-p1-twist-coherent-powers`: the existing node is a coherence statement for iterated twists on `Proj k[x_0,x_1]` and explicitly asserts no coordinate nonvanishing locus; the new node is the general `W_d` section-locus theorem for arbitrary graded rings.
- `lem-trf-proj-twist-section-basic-open` vs `lem-sc-p1-twist-product-morphism`: the existing node only constructs multiplication morphisms on the field `P^1` case and asserts no coordinate locus; the new node identifies section nonvanishing loci on `W_d` for arbitrary Proj.
- `lem-trf-proj-twist-section-basic-open` vs `lem-weil-pbc-proj-polynomial-twist-chart`: the existing node treats coordinate charts of polynomial projective space and their ratio functions; the new node treats every homogeneous section on an arbitrary graded Proj invertibility locus.
