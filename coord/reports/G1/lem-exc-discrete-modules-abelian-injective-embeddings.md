# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-exc-discrete-modules-abelian-injective-embeddings.json`: split into the 04JF specialization and the enough-injectives consequence; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-exc-rg-discrete-modules-functorial-injective-embeddings.json`: new unsplit statement for arbitrary topological groups and rings; no Mathlib match.

2. Attachments:

None. I searched both slopmaster2 source trees by the item id, the 04JF tag, and `injective embedding`; no sorry-free declaration states the item or the new node.

3. WANTED:

- `literature/stacks-project/injectives.tex`, Tag 04JF (`lemma-G-modules`), for the full functorial construction and its open-stabilizer specialization. The local repository contains the citation metadata but not the TeX source; the proof follows the statement recorded in the DAG and the imported source description.

4. What was wrong and what changed:

The imported item had no proof split. I isolated the general 04JF statement in a strictly broader node, then made the item specialize it to a profinite group and finite ring and conclude the enough-injectives condition. The item now has complete proof and proof-dependency lists, blueprint metadata, and the required three Mathlib search records. No statement error was found.

## Review by G1

I read the item's imported source place, Etale Cohomology Tag 0A2H (the paragraph after Definition 04JP), and the cited Injectives Tag 04JF label `lemma-G-modules` as described in the repository metadata. The item statement agrees hypothesis by hypothesis: $G$ is profinite, $A$ is finite, objects are left $A$-modules with $A$-linear $G$-action and open stabilizers, and morphisms are equivariant $A$-linear maps. The new node keeps the same construction but generalizes $G$ to an arbitrary topological group and $A$ to an arbitrary ring, so it is strictly smaller as a specialization step.

Step 1 cites only `lem-exc-rg-discrete-modules-functorial-injective-embeddings`. Its statement supplies the functor, natural transformation, monomorphism, and injectivity in the open-stabilizer category. I checked the specialization on the trivial group and on a finite discrete group: every stabilizer is open, so the general category reduces to the ordinary equivariant module category. The open-stabilizer submodule in the 04JF construction is stable under the group action, which is the required closure property for the target of $J$.

Step 2 cites `def-sp-injective-resolutions`. The cited statement says exactly that a category has enough injectives when each object admits a monomorphism into an injective object, so the components supplied in step 1 give the conclusion without adding hypotheses. The zero module and a quotient by a stable submodule satisfy the same condition, checking the edge cases used by the specialization.

Before creating the new node I searched all DAG nodes and the imported blueprint for `04JF`, `lemma-G-modules`, `functorial injective`, `Mod_{R,G}`, and `open stabilizer`; no existing node or blueprint node states the general theorem. I also searched the slopmaster2 source for the item id, tag, and relevant declaration names; only generic sheaf `EnoughInjectives` declarations appeared, all unrelated. The new node has separate LeanSearch, Loogle, and Mathlib-source grep records, each finding no specialized declaration. The item has the same three searches inherited from the imported node. No proof step is marked elementary because each uses a nontrivial cited theorem or definition.

The local Stacks TeX file named by the source is absent, so the exact 04JF text is recorded under WANTED rather than silently treated as locally read. No other source, hypothesis, or blueprint error was found.

5. What I could not finish:

The general 04JF node remains an intentional unsplit queue obligation. No Lean code is written at stage 1.
