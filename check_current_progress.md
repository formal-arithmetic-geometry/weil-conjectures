# Generate a Pure Mathematics Lecture in English from Lean Source Files: General Prompt

## Status of the Nagata compactification source (2026-09)

The Nagata compactification theorem is **proved and `sorry`-free** on `slopmaster`. There are no
remaining gaps in it: elimination of indeterminacy (Stacks Project Tag 081S) is unconditional,
its Conrad Theorem 2.4 input `AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection`
is proved in `WeilConjectures/Blowup/PartialSectionExtension.lean`, and the three main forms of
the theorem —

* `AlgebraicGeometry.NagataCompactification`
  (`WeilConjectures/Compactification/NagataCompactification.lean`),
* `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`
  (`WeilConjectures/Compactification/FinitePresentation.lean`),
* `AlgebraicGeometry.nagataCompactification_of_isNoetherian`
  (`WeilConjectures/Compactification/Noetherian.lean`)

— each carry a `#guard_msgs` + `#print axioms` census in the build, checking that they depend on
`[propext, Classical.choice, Quot.sound]` only. So a lecture generated from this source must not
list any gap `G1`, `G2`, … in the Nagata material.

Branch `nagata-compactification-main-branch` — GitHub PR #207, still open against `master` — is
already fully contained in `slopmaster`, so there is nothing left to merge from it; read the
source at `slopmaster` rather than at the PR head.

## Fill in before use

* **Source type**: `folder` or `pull request`
* **Source URL**: `https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/207`
* **Target theorem or project goal**: `Nagata Compactification Theorem`
* **Output file name (without extension)**: `current-progress`
* **Output directory**: `blueprint/progress`
* **Access instructions (optional)**: `{{READ\_ONLY\_ACCESS\_NOTES}}`

If the target theorem is not explicitly provided by the user, it can only be determined from the folder, the Pull Request description, relevant explanatory files, or the final goal explicitly stated therein. If there remains substantial ambiguity, you should first ask a brief clarifying question and must not choose a target on your own.

\---

## Task

Please review the relevant Lean files in `{{SOURCE\_URL\_OR\_LOCAL\_PATH}}` in a read‑only manner, and organize the mathematical content already contained in them into an independent, coherent **pure mathematics lecture in English**. The ultimate goal of the lecture is to accurately present the definitions, propositions, lemmas, theorems, corollaries, constructions and their dependency relationships that appear in the source, while also explaining which mathematical steps are still missing to reach `{{TARGET\_THEOREM\_OR\_GOAL}}`.

You must generate the following two files:

1. `{{OUTPUT\_DIRECTORY}}/{{OUTPUT\_BASENAME}}.tex`
2. `{{OUTPUT\_DIRECTORY}}/{{OUTPUT\_BASENAME}}.pdf`

You must not modify the source repository, branch, Pull Request, or any files within them. You are only allowed to write files in the specified output directory and in a temporary build directory.

## 1\. Source scope

### Folder mode

* Recursively read all relevant Lean files inside the specified folder.
* Use the actual mathematical content appearing in that folder as the main body of the lecture.
* Only read files outside that folder if they are depended upon and are truly necessary for understanding the main content.

### Pull Request mode

* Read the full changes of the Pull Request, using the files from the PR head as authoritative.
* The lecture body should only summarize the mathematical content newly added or modified by the Pull Request.
* Files in the repository that are not modified by the PR but are used by these changes may be read; they can only be treated as auxiliary mathematical inputs.

### Version and access

* At the analysis stage, fix the actual commit or PR head to be read, so that the source does not change during the work.
* If the link requires an existing login session, use the existing read‑only session or read‑only interface.
* You must not write comments, reviews, commits, reviews, branches, tags, or any other state to GitHub.

## 2\. Mathematical faithfulness

1. State only the mathematical content that actually exists in the source files.
2. Do not add background knowledge, historical introduction, motivation, examples, generalizations, speculation, standard proofs, or conclusions not contained in the source.
3. A minimal number of transitional sentences that introduce no new mathematical content are allowed to make the English lecture coherent.
4. Do not guess the conclusion of a theorem from its name; you must check the full statement, assumptions, quantifiers, objects, and conclusion.
5. Do not omit important assumptions that would change the scope of the conclusion, such as finite type, quasi‑compactness, quasi‑separatedness, Noetherianness, density, invertibility, properness, or base assumptions.
6. Do not treat a statement that is only stated, has a placeholder proof, or has unfinished dependencies as a theorem already established.
7. If the source only provides a special case of a result, the lecture may only state that special case.
8. If several results are merely different local versions of the same construction, preserve their logical distinctions as they appear in the source; do not combine them into a stronger theorem on your own.
9. Proofs or arguments should only convey the mathematical steps that are actually present in the source; do not supply proofs not provided by the source.

## 3\. Pure mathematics writing requirements

The lecture must be written entirely in English and as an ordinary mathematical lecture. The visible content of the final `.tex` and `.pdf` must not contain any mention of formalization, programs, or source files, including but not limited to:

* Lean;
* formalization, formalized, formally verified;
* proof assistant;
* `.lean` file names, paths, namespaces, imports, declaration names, or code snippets;
* tactics, typeclasses, instances, compilers, implementations;
* GitHub, repository, commit, branch, or Pull Request;
* “the code proves…”, “the file contains…”, “this was formalized…”, etc.

Everything must be written directly as mathematics. For example, do not write “the file proves that the blow‑up is proper”, but write “The blow‑up morphism is proper.”

## 4\. Handling mathematical content from other folders

If the main body actually uses results provided by files outside the specified scope, you must indicate **what mathematical conclusion is used**, but without mentioning file names, paths, declaration names, or formalization sources.

At the **first place where that result is actually used**, insert a visually distinguishable but unnumbered paragraph, using a visible heading such as:

> \*\*Auxiliary mathematical input used here.\*\*

Then state the external conclusion used in precise natural mathematical language. For example:

> \*\*Auxiliary mathematical input used here.\*\* Properness is local on the target.

Requirements:

* Only list the mathematical fact actually used at that place;
* State it immediately at the place of use, not collected at the end of the lecture;
* If the same auxiliary fact is used repeatedly in several places, it may be stated in full at the first use, and only briefly reminded later when truly necessary;
* Do not mistakenly list auxiliary inputs as main conclusions already established by the current folder or PR;
* If it is merely a general notational convention rather than an external theorem, it need not be marked as auxiliary input.

## 5\. Lecture structure

Adjust the section titles according to the actual mathematical content, but at least include the following structure:

1. **Title**
2. **Abstract**: summarize only the mathematical topics and the final goal actually covered by the lecture.
3. **Table of Contents**
4. **Conventions and notation**
5. **Main mathematical sections**: organize definitions, local results, global results, and main theorems in dependency order.
6. **What remains for `{{TARGET\_THEOREM\_OR\_GOAL}}`**
7. **Main results**
8. **Dependency mind map**

Do not mechanically list content in the order of the source files. If the mathematical dependency order differs from the file order, organize by mathematical dependency, while preserving the exact scope of each conclusion.

## 6\. Theorem environments, numbering, and internal cross‑referencing

1. All important Definitions, Lemmas, Propositions, Theorems, Corollaries, and the final goal must be set in mathematical environments numbered by section.
2. Every major result should have a stable LaTeX `\\label{...}`.
3. References to these conclusions within the lecture should use `\\ref{...}`, avoiding hard‑coded manual numbers.
4. The final goal should be given a visible independent name, for example:

> \*\*Target Theorem 7.1 (…).\*\* …

5. If the final goal is not yet established by the current material, immediately after its statement clearly write that it is the final goal, not a conclusion already established above.
6. Number the uncompleted key steps as `G1`, `G2`, …, and give each a label that can be referenced.
7. Numbering must be **internal to the lecture**, not using source file line numbers, file names, or internal declaration names as retrieval methods.

## 7\. Criteria for “already established” and “still missing”

Build a dependency table during the analysis phase, recording at least:

* mathematical conclusion;
* complete assumptions;
* direct dependencies;
* whether the dependency is inside the current scope;
* whether the conclusion is available, remaining, or the ultimate target;
* its number and label in the lecture.

Only results that have a complete statement in the source and all necessary dependencies fulfilled may be marked as **Available**.

For gaps:

* Only indicate missing steps that are explicitly shown by the source itself, the PR description, the target theorem, or the dependency chain;
* Do not add additional research plans based on general mathematical knowledge;
* Precisely state whether the missing part is a local lemma, a gluing step, a descent step, a finiteness conclusion, an existence theorem, or the final assembly;
* Do not write only vague statements such as “more work is needed”;
* If you can identify direct inputs, list them with their lecture numbers;
* If you cannot determine from the source whether a step is missing, use conservative wording such as “The surveyed material does not include a theorem establishing …”.

## 8\. Main results

At the end of the lecture, provide a clear summary table. Each row at least contains:

|Node|Mathematical conclusion|Internal locator and status|
|-|-|-|
|short node name|precise conclusion in natural language|Definition/Theorem/Proposition/Corollary number; Available/Remaining/Ultimate target|

The summary must cover:

* core definitions;
* decisive local conclusions;
* key nodes that go from local to global;
* key constructions or universal properties;
* main intermediate theorems;
* the strongest conclusion obtained;
* each numbered gap `G1`, `G2`, …;
* the final target theorem.

The locators in the summary must be internal lecture references such as “Theorem 3.7”, “Corollary 4.10”, “Gap G2”, “Target Theorem 7.1”, so that the reader can look them up directly in the main text.

## 9\. Dependency mind map

After the **Main results** summary, draw a dependency mind map using TikZ. Every important node in the diagram must contain:

* a short mathematical name for the conclusion;
* its corresponding internal lecture number.

It is recommended to split the diagram into two panels; if one page is too crowded, use two landscape pages:

### A. Established dependencies

* Show only dependencies that have already been established mathematically.
* Consistently use arrow `A → B` to mean “conclusion B uses conclusion A”.
* Use green nodes for established conclusions.
* Blue nodes may be used to highlight the decisive output of a dependency branch.
* Use solid blue arrows for already established dependencies.

### B. From available ingredients to the target

* Show which existing conclusions are direct inputs for each gap.
* Use orange nodes for uncompleted steps such as `G1`, `G2`, …
* Use orange dashed arrows to indicate “input already exists, but the required assembly has not yet been performed”.
* Only use solid orange arrows to connect two gaps if the source clearly supports a dependency between them.
* Multiple independent gaps should converge into a final assembly node individually; do not force a linear chain just for graphical neatness.
* Use a red node for the final target theorem.

Graphical quality requirements:

* Do not use a root node with no mathematical dependency meaning, nor classification arrows;
* Do not let an entire section or an entire theoretical block point directly to a gap, unless they truly are all direct inputs;
* Avoid arrows crossing nodes, labels, or other arrows;
* Avoid text overflow, overlapping, too‑small fonts, or clipping;
* Include a concise legend explaining node colors and arrow meanings;
* Dependency relationships are more important than content classification;
* All numbers in the diagram must be generated automatically via `\\ref{...}`.

## 10\. TeX and PDF requirements

* Use a LaTeX document class suitable for mathematical lectures and a consistent layout.
* Use A4 paper, clear margins, page numbers, table of contents, and a unified theorem style.
* Use landscape pages for wide mind maps.
* The `.tex` file must be compilable independently to produce the delivered `.pdf`.
* Compile at least until all cross‑references are stable.
* Do not leave `??`, undefined references, missing characters, overfull boxes, clipped content, or unreadable formulas.
* Do not leave temporary files such as `.aux`, `.log`, `.out`, `.toc`, rendered images, etc., in the final output directory.

## 11\. Final checklist

Before delivery, verify each item:

* \[ ] The lecture is entirely pure mathematics in English;
* \[ ] No Lean, formalization, code, file names, paths, GitHub, or repository‑related wording appears;
* \[ ] No mathematical content not present in the source has been added;
* \[ ] Every important assumption has been preserved;
* \[ ] Auxiliary mathematical inputs from outside the scope have been stated at their actual point of use;
* \[ ] Auxiliary inputs have not been collected at the end;
* \[ ] The distinction between established content and unfinished work is clear;
* \[ ] Gaps have been numbered `G1`, `G2`, …;
* \[ ] The final goal is explicitly marked as ultimate target, not as an established conclusion;
* \[ ] The **Main results** summary contains accurate internal lecture locators;
* \[ ] The mind map shows logical dependencies, not merely a thematic classification;
* \[ ] All cross‑references are resolved;
* \[ ] The PDF has been checked page by page, with no overlaps, clipping, or unreadable elements;
* \[ ] The final `.tex` and `.pdf` are both placed in the specified output directory.

## 12\. Delivery reply

After completion, respond with a brief statement containing:

* the actual source scope covered;
* the number of pages of the lecture;
* confirmation that compilation, cross‑reference checking, and page‑by‑page visual inspection have been completed;
* a clickable path to the `.tex` file;
* a clickable path to the `.pdf` file.

Do not repeat the entire lecture in the reply.

