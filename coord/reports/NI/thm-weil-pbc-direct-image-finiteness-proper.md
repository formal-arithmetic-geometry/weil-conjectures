# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/thm-weil-pbc-direct-image-finiteness-proper.json`: split statement.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-proper-direct-image-finiteness.json`: new unsplit statement node; Mathlib searches found no match.
- `citations.json`: verbatim dependency quotes for step 1.

## Attachments

None. I found no sorry-free declaration in the source checkouts carrying this target or the new étale statement.

## WANTED

WANTED: Deligne, SGA 4 1/2, Theoreme de finitude, Theorem 1.1, for the constructibility part of `lem-weil-pbc-etale-proper-direct-image-finiteness` (the volume is listed as unavailable in `literature/LIST.md`).

## What was wrong or incomplete

The imported item had no proof steps and its `blueprint.same_as` was null. I filled the blueprint reference and supplied one complete proof step. The item’s cited classical input was not represented by an existing node, so I created the strictly smaller étale-site statement `lem-weil-pbc-etale-proper-direct-image-finiteness`; it differs from the target by working on the étale site and is not a restatement of the pro-étale FIN conclusion. I reused the existing comparison proposition and FIN definition. The existing `thm-fin-proper-case` was checked but only covers finite-type schemes over a field, so it does not cover the item’s general Noetherian hypotheses.

## Not duplicates

lem-weil-pbc-etale-proper-direct-image-finiteness vs thm-weil-pbc-direct-image-finiteness-proper: the new node is the étale-site input for a single constructible sheaf, while the item asserts the pro-étale FIN predicate for all pro-étale constructible sheaves.
lem-weil-pbc-etale-proper-direct-image-finiteness vs def-weil-pbc-tower-preservation: the new node concerns ordinary étale higher direct images under proper maps; the existing definition concerns preservation across an adic coefficient tower.
lem-weil-pbc-etale-proper-direct-image-finiteness vs thm-weil-pbc-amplification-proper: the new node is a sheaf-level étale finiteness theorem, while that theorem concerns derived amplification for a different coefficient construction.
lem-weil-pbc-etale-proper-direct-image-finiteness vs prop-weil-pbc-preservation-constructible: the new node includes the fibre-dimension vanishing bound and is étale; the existing proposition is a pro-étale preservation statement with different hypotheses and conclusion.
lem-weil-pbc-etale-proper-direct-image-finiteness vs prop-weil-pbc-restriction-direct-image: the new node supplies the proper étale finiteness input, while the existing proposition is a conditional derived-category restriction assuming FIN.
lem-weil-pbc-etale-proper-direct-image-finiteness vs prop-weil-pbc-amplification-consequences: the new node is an étale sheaf theorem; the existing proposition derives consequences after an amplification hypothesis.
lem-weil-pbc-etale-proper-direct-image-finiteness vs def-weil-pbc-finite-level-amplification: the new node is a theorem about $R^qf_*$, while the existing node defines finite-level amplification data.
lem-weil-pbc-etale-proper-direct-image-finiteness vs prop-finite-compact-support-constructibility: the new node concerns proper ordinary direct image on arbitrary Noetherian schemes; the existing proposition concerns compact-support direct image for finite-type schemes over a field and derived complexes.
lem-weil-pbc-etale-proper-direct-image-finiteness vs lem-sf-integral-compact-support-constructible: the new node concerns étale proper direct images and the $2e$ fibre bound, while the existing lemma concerns integral compact-support constructions.

## Review by NI

I read the target blueprint source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/thm-weil-pbc-direct-image-finiteness-proper.md`, the unit and chapter records, the FIN definition, and the full statement of `prop-weil-pbc-comparison-direct-image`. Step 1 uses the new étale finiteness statement exactly for constructibility and vanishing, the comparison proposition for the isomorphism after pulling back along `nu`, and the FIN definition for identifying the two resulting clauses. The hypotheses are tracked: finiteness of `P_n` supplies torsion, properness supplies quasi-compactness and quasi-separatedness for comparison, and the fibre bound is retained as `2e`. I also read the existing `thm-fin-proper-case` and rejected it as too narrow (finite type over a field). I tested the edge case `e=0`, where the new statement gives vanishing for all positive degrees and the target asks for `FIN(f,Lambda;0)`. Mathlib searches were run twice with LeanFinder, Loogle, and Mathlib grep; they returned only unrelated constructibility or derived-category declarations. No Lean files or compilers were used.


## Second reading by NI

- Item statement: read the blueprint item, its unit `sk-thm-properbasechange` and chapter `sec-proper-base-change`, and Stacks `etale-cohomology.tex`, Tag 095U (`lemma-cohomological-dimension-proper`), and `more-etale.tex`, Tag 0GL0 (`theorem-constructible-shriek`); PASS, all imported hypotheses and the bound $2e$ are retained, and FIN means precisely the two quantified clauses in the current definition.
- Step 1: checked the full statements of `def-weil-pbc-constructible-direct-image-finiteness` and `lem-weil-pbc-etale-proper-direct-image-finiteness`; REPAIRED, the former now explicitly supplies the constructible étale witness, the finite coefficient ring, and its invertibility condition; the latter applies to exactly these Noetherian schemes, proper map and fibre bound. The elementary torsion argument is $Nm=(N1)m=0$, with $N$ the positive additive order of $1$ (also $N=1$ for the zero ring).
- Step 2: checked `def-weil-pbc-scheme-conventions`, `def-weil-closed-immersion`, `prop-weil-pbc-comparison-direct-image`, `prop-weil-pbc-site-comparison-finite-level`, and the FIN definition; REPAIRED, finite type implies quasi-compact by definition, and the diagonal is quasi-compact because its inverse image of an affine is affine. Comparison is applied to $F_{\Et}[0]\in D^+$, not asserted directly for a sheaf. The finite-level proposition states exactness for both comparison pullbacks. Kernels, images and their quotient give the displayed cohomology identification; this is the elementary calculation converting the cited derived comparison into the required higher-direct-image comparison. The resulting étale witnesses prove constructibility, and exactness sends zero to zero, proving the uniform vanishing clause for arbitrary $F$.
- New node `lem-weil-pbc-etale-proper-direct-image-finiteness`: read 095U and 0GL0 at the labels above, the compactification construction in `more-etale.tex` (`section-derived-lower-shriek-compactification`), and each of its definition nodes; REPAIRED B3/B5, now statement-only, self-contained with explicit Noetherian and finite-dimensional meanings, finite ring meaning, and definition citations, with correct source files, tags and labels. It is a classical étale input, not a pro-étale FIN restatement; neither the adic datum nor comparison morphisms occur in it. The item still proves the transfer using the independently existing comparison theorem and exactness. The étale constructibility and vanishing statements are substantial, not two-line consequences of definitions.

For the new node, the precise specialization of the sources is as follows. A finite ring is Noetherian (each ideal has finitely many elements, which generate it) and torsion (the additive order of $1$ annihilates every module). Noetherian schemes are quasi-compact and quasi-separated. A proper map is separated and finite type, and finite type over a Noetherian base is finite presentation. Thus $F[0]$ is an object of $D^+_{tors,c}$ to which 0GL0 applies. For proper $f$, choose the compactification $X\xrightarrow{\mathrm{id}}X\xrightarrow{f}Y$: the defining functor $R\bar f_*j_!$ is then $Rf_*$. This gives precisely constructibility of each $R^qf_*F$. Tag 095U gives the vanishing bound for torsion sheaves; it does not require invertibility. Its fibre bound is satisfied by the stronger geometric-fibre bound (dimension of a finite-type scheme over a field is unchanged by field extension). Invertibility is retained from the target, not added to it. These available sources supersede the first worker's WANTED entry: SGA 4 1/2 is not needed for this delivery.

Small cases: $F=0$ has all direct images zero; $X=\varnothing$ has the same outcome without needing a nonempty fibre; $Y=\varnothing$ forces $X=\varnothing$. For $f=\mathrm{id}_{\operatorname{Spec}k}$ the fibre dimension is zero and the conclusion is the identity in degree zero and zero in positive degrees. For a zero-dimensional proper map the source 095U reduces to exact finite pushforward. For a proper curve over an algebraically closed field, the $e=1$ bound allows degree two and kills degrees above two; it does not erroneously impose degree-one vanishing. The zero ring and the zero module are included. The coefficient datum indexes $n\geq1$, so $n=1$ is included and $n=0$ is not an omitted target case.

Duplicate and leaf checks: searched all DAG nodes by tags 095U/0GL0 and by proper/constructible direct images, and searched the entire imported blueprint with `blueprint_refs.py search` for `proper direct image`, `095U`, `0GL0`, and checked the ancestor. Read `thm-fin-proper-case`, `thm-fin-proper-constructibility-complete`, `lem-fin-proper-bounded-constructible`, and `prop-finite-compact-support-constructibility`; these require finite-type schemes over a field, so none supplies the general Noetherian input. Other tag matches define tower/amplitude conditions or deduce their consequences and do not state the ordinary étale input. Independent Mathlib searches with a different phrasing were run through msearch.py: LeanFinder found ordinary pushforward/adjoint declarations and Chevalley for subsets; Loogle `"constructible"` found topological subset predicates; correctly rooted grep found no étale-cohomology or constructible-sheaf declarations. No leaf is available. Read the source checkout's `SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`: its relevant results require schemes of finite type over a field and rest on named sorry inputs; they do not close this node. The upstream master checkout is reference material only. No Lean was written or compiled.

Changes made and why:

- Corrected the new node's 0GL0 source from the wrong `etale-cohomology.tex` file to `more-etale.tex`, and supplied exact labels instead of unstable section numbers.
- Replaced its unhelpful FIN citation for a finite ring with the explicit finite-set meaning, and supplied the missing Noetherian-ring and Krull-dimension definition references and inline scheme hypotheses.
- Added the missing definition citation in step 1 and wrote the torsion argument.
- Added the cited finite-level exactness input and the kernel/image/quotient calculation in step 2, plus the elementary diagonal argument checking comparison's qcqs hypotheses.
- Rebuilt citations.json with verbatim full statements for every repaired citation.
- Recorded independent searches. The first worker's two grep logs used a subdirectory beginning `Mathlib`, duplicating the script's root; marked those results unusable and superseded them with a correctly rooted search. Kept the first worker's report and `## Review by NI` unchanged.
