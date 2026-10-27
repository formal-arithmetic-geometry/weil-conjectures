## Worker report

### Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-space-test-module-restriction-comparison.json`: existing definition, now with explicit based-test category, chart restriction, componentwise module functor and chart-limit mate defining the tensor comparison. Mathlib verdict: no complete match.
- `citations.json`: `[]`, because this is a definition with no theorem proof steps.
- `report.md`: this report. The search command also produced `searches.jsonl`.

### Attachments

None. Searches of the project's `lean/WeilConjectures/` and `lean/Sheaf/` for the exact blueprint tag, `spaceTestModuleRestriction`, `spaceTestModuleComparison`, and `spaceTestIdentityTwoIso` returned no declarations. Concept searches also produced no declaration stating this definition for arbitrary fibred categories and algebraic-space tests. No Lean files were written or compiled.

### WANTED

None. All construction sources are present in `literature/stacks-project/stacks-sheaves.tex`.

### Findings and changes

The assigned node was already marked `split`, but had no review record, split report or explicit chart-limit mate. There was no earlier sandbox node or report. This is a definition, so stage 1 separates its constituent notions as statement dependencies; it does not invent theorem proof steps or extract a new node for each of its own clauses. The construction is now specified as actual data: first the chart restriction, then a map into the specified chart-limit direct image, then its adjoint. It uses no existence theorem choosing an undetermined map.

The original tensor pinning is retained verbatim in meaning. The arrow formerly abbreviated `theta_T;w(r)` is now typed as `w(r) composed with theta_(T,v)`, from `z(v)` to `w(e)` over `r:T -> E`. This also specifies the direction of contravariance of K. The original phrase “a test z:V -> C” is expanded into a functor from the discrete fibred category of V. Actions and restrictions are the inherited ones over the identical base scheme, rather than transported through an unspecified ring isomorphism. The restriction on module morphisms is also given explicitly.

Removed `def-pc-module-pullback`: its statement defines Zariski pullback on schemes; the item uses small-etale tensor pullback on algebraic spaces and obtains it from `def-trf-space-etale-module-functors`. Removed `def-trf-space-quasi-coherent-module`: no quasi-coherence predicate or QCoh category occurs in this construction. Ambient module sheaves are supplied by `def-weil-sheaf-of-modules-category` with the size convention. The existing tensor-composition definition is retained to fix the normalization used downstream.

Source references now give precise tags and labels: 075K (`equation-restrict`), 06WC (`equation-comparison-modules`), and 076R (`equation-comparison-algebraic-spaces-modules`), especially the immediately preceding adjoint definition. 075D is the subsequent property lemma, not the definition of the scheme module comparison; its naturality and invertibility assertions are not assumed here. This is an expansion of the same construction, with unchanged hypotheses and no mathematical statement dispute.

### Blueprint and duplicate searches

Read the chapter and unit records, then the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The latest direct-image clause (3) is preserved; this is its inherited auxiliary module-descent construction, not an alternate proof of the unit. `blueprint_refs.py ancestor` reports that the existing `blueprint.from.node` is None. Retained the inherited node-null/via provenance instead of inventing a different ancestor, and documented the exact source location in `split_report.blueprint`. The inherited `from.place` already names the long support chain and the Tag 06WT restriction/comparison prerequisite.

Whole-blueprint searches for `space test module restriction comparison`, `075D`, and `076R` returned zero matches. The wider `small etale` search returned 123 records but no matching general fibred-test definition. Whole-DAG searches by the tags, chart-limit wording and based-functor wording led to the following existing nodes, whose statements were opened: `lem-sfb-fibred-fppf-space-module-comparisons` uses this definition and proves its later properties, so citing it here would be circular; `lem-sfb-stack-small-etale-comparison-calculus` assumes an algebraic stack and also proves properties; `lem-sfb-fibred-big-etale-restriction-calculus` concerns scheme-object restriction; `lem-trf-space-chart-adjunction-tensor-realization` identifies the specified chart adjunction with the ringed-topos tensor realization. None is a second owning definition of the data here. The existing `def-trf-space-etale-module-functors` already provides the general chart limit, tensor left adjoint, unit and local tensor notation; no new nodes are needed.

### Mathlib search results

Ran and read all six new queries in `searches.jsonl`: LeanFinder for the complete fibred fppf restriction/comparison; Loogle for `SheafOfModules.pullback, SheafOfModules.pushforward`; grep for `restrictScalars|pullback|pushforward` in `Algebra/Category/ModuleCat/Sheaf`; two distinct LeanSearch phrasings (restriction/cover preservation, then natural transformation/adjoint comparison); and grep for `algebraic space|fibred|fppf` in `AlgebraicGeometry`. All services answered; none is recorded as unavailable. Their exact tool and query strings and returned log records are appended to the item's pre-existing search history, which is retained.

Read the candidates in the local pinned Mathlib: `SheafOfModules.pushforward`, `PushforwardContinuous.lean:44-49`, takes an already-continuous functor and ring map; `SheafOfModules.pullback` and `pullbackPushforwardAdjunction`, `PullbackContinuous.lean:56-64`, take the already-specified ringed-site map and adjoint instance; `SheafOfModules.restrictScalars`, `ChangeOfRings.lean:36-41`, changes rings on one site. Also read the pullback/sheafification construction in `PullbackContinuous.lean:81-106`. These are useful ingredients already represented by existing definitions, but do not define the algebraic-space based-test category, its chart functor into an arbitrary fibred fppf site, or the comparison whose adjoint has the pinned projections. Scheme open-immersion restriction candidates have a different domain and hypotheses. Therefore the whole item is not a Mathlib leaf.

### Unfinished work

None for this stage-1 definition. Downstream naturality, composition, etale invertibility and quasi-coherence are intentionally the existing property theorem's work; they are not clauses dropped from this item. There are zero new nodes and zero new Mathlib leaves.

## Not duplicates

No new nodes were created; there are no new/existing pairs requiring comparison.

## Review by Q46

I read the Stacks construction in `stacks-sheaves.tex`, the module restriction preceding 06WC and the adjoint construction preceding 076R. The restriction in 075K evaluates a sheaf on an etale chart through the represented discrete fibred category, exactly the data now written for z. The 076R construction takes the adjoint of the restriction map into the direct image. The componentwise chart-limit formula is that same map, not an additional comparison whose equality has to be assumed. No SGA source is used.

There are no proof steps in the item: its kind is `definition`. I checked its construction in the following three parts, using only the statements of the existing definitions, which I opened in full. First, `def-sfb-stack-quasi-coherent-algebra` defines the arbitrary fibred fppf site and the ring value Gamma(T,O_T), while `def-trf-algebraic-space` defines the small-etale chart site and the identical structure-ring value. `def-weil-sheaf-of-modules-category` supplies precisely the semilinear restrictions and linear morphism components inherited by K_z. An etale covering of a chart is an fppf covering of its base, so the matching family and its unique glued section are the matching family and gluing for K; the based functor carries the chart overlap to the fibred overlap. This does not use stack descent or quasi-coherence. The arbitrary fibred-category notion is already supplied by the statement dependencies of the stack-ringed-site definition; the item now defines the discrete test category itself.

Second, `def-trf-space-etale-module-functors` states the chart category A(a,E), its limit projections, functorial restrictions, the tensor adjunction, its specified unit, and the unit-defined local tensor b tensor m. For h:T' -> T over V with r h=r', naturality of theta gives w(h) theta_(T',v') = theta_(T,v) z(h); composing with w(r) and applying contravariance of K gives
K(z(h)) K(w(r) theta_(T,v)) = K(w(r') theta_(T',v')).
This is exactly the compatibility required for the chart-limit family. Each projection is Gamma(E,O_E)-linear since its arrow lies over r; theta lies over the identity and therefore acts trivially on that base ring. For a target-chart arrow j:E' -> E the projection for r':T -> E' after restriction is K(w(j r') theta_T), which is also the restriction of K(w(j))m through the original formula. Thus the construction defines a module-sheaf map d, not merely unrelated section maps. These checks are direct functoriality and the already-defined limit property, not non-elementary lemmas hidden in a long step.

Third, the same functor definition explicitly supplies a^* left adjoint to the specified a_* and the local unit tensor. Define c to be the inverse image of d under this Hom bijection. The unit equation a_*c composed with eta = d gives c(1 tensor m)=K(w(r) theta_T)m after projection; module linearity gives the displayed b tensor m formula. Conversely those formulas determine the projections of a_*c composed with eta, hence d by the limit property, hence c by the adjunction bijection. This checks the original existence/uniqueness pinning without creating a restatement node. `def-sfb-space-module-tensor-composition` fixes the iterated normalization c tensor (d tensor m) -> c r^sharp(d) tensor m; the item retains that convention but takes no unproved composition assertion for its comparison from it. The module categories are ambient-sized as specified by `def-weil-size-convention`; limits are over the bounded chart categories. No assertion that every global pullback section is one pure tensor is used.

I tested the zero module (both d and c are zero), identity based test with identity theta (the chart projections are the usual restrictions and the tensor formula is b tensor m -> bm), an empty space (its module sheaf is the unique zero module, so the formula imposes no spurious section), and a nontrivial vertical automorphism theta (the formula uses K(theta), rather than discarding the two-isomorphism). For a general non-etale a the construction still exists and does not assert it is invertible. No flatness, finiteness, algebraicity of C, or quasi-coherence was used in these checks.

Against delivery-errors B through E: all objects and actions are introduced, TeX is encoded once, exact Stacks tags and labels are supplied, and no new unsplit nodes or bogus Mathlib leaves exist. C1/C4 are checked above against the actual definition statements; there are no proof-step quotations to put into citations.json. The downstream comparison theorem is not cited as a construction dependency, avoiding a cycle. There is no clause-relabeling split or moved proof: a definition is factored through existing notions, and its chart mate is written explicitly. I corrected the two unused dependencies and the vague source pinpoints described above. No reviewer record was written by the worker.
