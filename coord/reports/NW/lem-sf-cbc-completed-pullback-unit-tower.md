# NW stage-1 delivery: lem-sf-cbc-completed-pullback-unit-tower

## 1. Files written

- `dag/nodes/sec-smooth-purity/lem-sf-cbc-completed-pullback-unit-tower.json`: statement node, now split into six proof steps; no Mathlib match for the whole statement.
- `citations.json`: fifteen step/node entries, each quoting the cited node's complete statement verbatim, including its hypotheses.
- No new nodes and no new Mathlib leaves. `write_split.py` is sandbox-only preparation; `searches.jsonl` records the searches actually run.

The statement, chapter, unit and historical blueprint/creation fields are retained. The proof, proof dependencies, proof origin, split report, same-as search result and additional actual Mathlib searches are supplied. Nothing outside this sandbox was written, and no Lean or compiler was run.

## 2. Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact item tag and for completed pullback, completion unit and strict reduction/quotient towers. There is no declaration stating all three clauses. The completion-diagram declarations and the completed-pullback discussion in `SixFunctors/Etale/Derived/IntegralCoefficients.lean` do not give this statement in the derived category of strict towers. Master declarations are reference material, not attachment evidence.

## 3. WANTED

None. The relevant Stacks source, current blueprint proof and existing DAG statements are available locally.

## 4. Findings and changes

The imported item has an empty proof. Its mathematical statement needs no repair. In particular, clause (i) is for every N, and clause (ii) is for every K; I have not inserted a completeness, boundedness, constructibility or finite-type hypothesis. Completeness is used only in clause (iii), to enter the coefficient equivalence on complete subcategories.

The current blueprint ancestor is `fix-lem-exchanges`; the current snapshot places its proof under `sec-six-functors-basics/sk-prop-sf-cbc/`, whereas the retained historical source field points to the older `sec-smooth-purity/` path. I read both. The ancestor's Steps 2 and 5 concern naturality and compactification/composition independence, but do not themselves prove this auxiliary strict-tower comparison. The six steps are therefore marked agent-written, with their actual sources and the ancestor places recorded. This supplies a generator needed by the existing compact-support composition refinement; it does not change the unit's route or its coefficient restrictions.

The useful existing node is `lemma-weil-pbc-adic-completion-reduction`: its statement gives the adjoint of the limit projection as an isomorphism for arbitrary K, not merely for a complete K. Step 1 uses this exact assertion. The adjunction calculation then proves it is the inverse of the reduced completion unit. Merely citing that lemma for a whole isomorphism of towers would miss the distinction between D(Tow(Mod(A))) and Tow(D(Mod(A))). Step 2 instead starts with the already defined strict derived-tower morphism R(eta) and proves its cone acyclic by levelwise cohomology. Likewise Steps 3–4 construct the pullback comparison on actual complexes with actual transitions and descend it, rather than inferring a strict lift from a family of derived maps.

The Mathlib searches used the mandated search command: LeanFinder with two phrasings, Loogle with `"completion", "tensor"`, LeanSearch, a broad grep and a focused CategoryTheory grep. I read the hits and read `AdicCompletion` at `Mathlib/RingTheory/AdicCompletion/Basic.lean:171` and `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` at `AsTensorProduct.lean:328`. These concern ordinary module completion, not unbounded module-sheaf derived categories or strict quotient towers. The broad case-insensitive grep also matched unrelated RestrictScalars/IsScalarTower names; its result is recorded as such, not as an empty search. The focused derived-completion grep returned no hits. The original searches remain in the item; new records use the exact queries from this sandbox's log. No search result was invented or silently changed.

## 5. What remains

No missing argument is left in this split. The existing dependency nodes retain their own recorded proof status; this is stage 1, not a claim that the Lean target is proved. The direct-delivery dry run and push are the remaining delivery operations.

## Not duplicates

No nodes were created, so there are no new/existing same-tag pairs. Whole-DAG and whole-blueprint searches for completion unit, strict reduction and adic-completion-reduction found existing tools, all reused. `lemma-weil-pbc-adic-completion-reduction` states the single finite-reduction projection isomorphism, whereas this item establishes the reduced unit and pullback isomorphisms in the derived category of strict towers and their identification with the completed-coefficient alpha maps. It is not a replacement statement for the whole item.

## Review by NW

I read the chapter record `sec-smooth-purity`, unit record `sk-prop-sf-cbc`, and both versions of `fix-lem-exchanges`, including the current standalone proof. I read Stacks `proetale.tex`, Tag 099M (`lemma-naive-completion`) and Tag 099N (`lemma-pushforward-Noetherian-case`), especially (2) and (5); `sites-modules.tex`, Tag 03EL (`lemma-tensor-product-pullback`); `sites-cohomology.tex`, Tags 06YS, 0G7E and 07A4 for the K-flat pullback/tensor route; and `homology.tex`, Tag 02MZ (`lemma-inverse-systems-abelian`). I also opened every cited node's statement. There are no new nodes requiring a separate source audit.

Step 1 uses the explicit completion-map definition for the equation p_n eta = quotient, the completion-adjunction statement to fix which unit is intended, and the adic-completion-reduction statement for the invertibility of the projection's scalar-extension adjoint. I checked its hypotheses: A is Noetherian, I is finitely generated, A/I is additive torsion and every P_n is perfect; no complete-input hypothesis occurs in the cited statement. The identity b_n F_n(eta) = id is written using naturality of the adjunction, not attributed to a definition that states no theorem.

Step 2 uses the exact evaluation and levelwise kernel/cokernel assertions of the existing tower-category Mathlib leaf, and the localization/cohomology/cone convention of the derived-category definition. Once all evaluations of the cone are acyclic, each cohomology tower is the zero diagram. This is the routine elementary cohomology argument, written out; it constructs no new tower map and does not assume evaluations are faithful on morphisms.

Step 3 uses the K-flat resolution theorem for existence, pullback-preserves-K-flat for admissibility of g*Q, and the canonical tensor-comparison construction together with the definition of its data for the natural tensor isomorphism. The latter definition explicitly includes natural isomorphisms mu in both module variables, and the construction theorem supplies that data. I checked the direction: beta goes from g*(Q tensor P_n) to g*Q tensor P_n, so tau is beta inverse. The transition square is exactly naturality in the map P_(n+1) to P_n. No assertion that inverse image commutes with inverse limits or products is used.

Step 4 uses the change-of-rings theorem's first clause for quasi-isomorphisms between K-flat complexes, the tower-category leaf to promote levelwise quasi-isomorphisms, and the first assertion of the tensor-descent node, W^{-1}P equivalent to D(R). I use that localization equivalence, not its later assertion about bifunctors as a substitute for a tower-valued result. The square for an inverted arrow follows by multiplying the already natural square by its two inverses. Exactness of the constant-coefficient inverse image is an explicit hypothesis of this item. Homotopies and transitions are taken termwise, as the written argument specifies.

Step 5 uses only the preceding steps. It writes the inverse naturality equation and the quotient transition equation explicitly. It does not hide a new coherence lemma or pretend compatibility of derived maps suffices to define a strict map. Each factor already belongs to the actual derived tower category.

Step 6 uses the constant/completed coefficient equivalence statement for its natural finite-reduction isomorphisms and its compatibility with completion units, the completed-pullback definition's final paragraph for the comparison to ordinary pullback followed by completion, and the completed-pullback-reduction statement for the projection normalization that defines alpha_n. I verified that K is complete exactly where this equivalence on complete subcategories is invoked. The adjoint of tau_n p_n is tau_n b_n by naturality, proving equality with the specified alpha_n rather than just an unspecified isomorphism with the same endpoints.

For B–E I checked that no elementary fact or clause of the item was promoted to a new node, every non-elementary input appears among these cited statements, and the text does not rely on their proof bodies. The external tools are declared in split_report with their individual purpose for route review, without setting maintainer-owned tool_uses. Dependency traversal found no path back to this item from the proposed tools. All six steps are shorter than 2000 characters.

I checked zero input, the empty scheme, I=0 (constant quotient tower, completion and its unit are identities), and I=A (zero quotient tower, completion zero; complete inputs in (iii) are zero). I also checked g=id, and unbounded inputs: the proof never interchanges g* with an infinite limit or imposes a uniform cohomological interval. General non-complete N is deliberately retained in Step 1. The concrete correction to the initially tempting approach was to obtain the strict inverse by conservativity of evaluations on objects via cohomology, rather than attempting to glue unrelated projection adjoints. No statement dispute or prohibited SGA source arises.

The server-side standalone review_split check passed with zero new nodes and the declared generic tool uses.
