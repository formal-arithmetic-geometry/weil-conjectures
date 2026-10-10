1. Files written:

- `lem-sc-ext-locally-free-second-naturality.json`: split statement, no new nodes, no Mathlib leaf.
- `citations.json`: verbatim statement quotes for every cited node in each proof step.

2. Attachments: none.

3. WANTED: none.

4. Problems found: the imported item was unsplit, while all required ingredients already existed in the DAG. I retained its statement and dependencies, filled its blueprint split metadata, and supplied a three-step proof. The Mathlib searches found only abstract Ext/cohomology APIs and no sheaf Ext-to-cohomology comparison theorem; LeanSearch was unavailable and recorded as such.

5. Nothing remains unfinished.

## Review by E1

I read the imported item and the source route in `thm-sc-p1-duality.md`, as well as Stacks Tags 06XR (Ext by an injective resolution), 015E (naturality of acyclic derived comparisons), and 01DZ (functoriality of sheaf cohomology). I checked the statement of `lem-weil-pbc-ext-via-injective-resolution`: it explicitly computes Ext in the second variable by the cochain complex `Hom(M,I^bullet)` and identifies it with the right derived functor. I checked `lem-sc-ext-locally-free`: it provides the canonical Ext/cohomology comparison for a finite locally free first argument, and its construction uses the Hom-to-global-sections/tensor composite. I checked `lem-sc-ext-evaluation`: its statement explicitly says the evaluation isomorphism is natural in the coefficient module, which is exactly the square used in Step 2. I checked `lem-sc-ext-derived-composite-natural`: its stated comparison equation is the commutative square needed in Step 3. Finally, `def-sc-sheaf-cohomology-functor` states that each coefficient morphism induces `H^i` and that these maps compose.

Step 1 uses only the injective-resolution Ext statement and the two existing derived-composite statements; the finite locally free and enough-injectives hypotheses are the hypotheses already carried by those nodes and the item. Step 2 uses coefficient naturality of evaluation and the Hom cochain description; no hidden quasi-coherence assumption is introduced. Step 3 instantiates the naturality theorem with `T = T' = F^vee tensor -`, `U = Gamma(X,-)`, and `alpha = 1 tensor phi`, then invokes the explicit cohomology functoriality statement. Every cited node says the fact taken from it, and the corresponding quotes are recorded verbatim in `citations.json`.

I searched the DAG and blueprint for duplicate second-variable Ext/cohomology naturality statements and found none. The small cases `i=0`, `phi = id`, and `F = O_X` reduce respectively to naturality of ordinary Hom, the identity map, and the usual identification `Ext^i(O_X,G) = H^i(X,G)`, so the statement has the expected edge behavior.

## Second reading by E1

- Item statement: checked against the locally-free Ext/cohomology statement and the coefficient-map clauses; hypotheses on scheme, finite locally free `F`, arbitrary modules, and `i >= 0` agree. Edge cases checked: zero-rank `F`, `i=0`, identity `phi`, and `F = O_X`; all give the expected zero, Hom, identity, and ordinary cohomology maps.
- Step 1: checked against `lem-weil-pbc-scheme-modules-enough-injectives`, `lem-weil-pbc-ext-via-injective-resolution`, `lem-sc-ext-locally-free`, and `lem-sc-ext-derived-composite`; the enough-injectives hypothesis and the derived-composite construction are now explicit and cited.
- Step 2: checked against `lem-sc-ext-evaluation` and `lem-weil-pbc-ext-via-injective-resolution`; the cited evaluation statement supplies naturality in the coefficient module, and the injective-resolution statement supplies the Hom complex.
- Step 3: checked against `lem-sc-ext-derived-composite-natural` and `def-sc-sheaf-cohomology-functor`; the comparison square and functorial cohomology map state exactly the claimed commutation.
- New nodes: none; therefore B1--B7 do not apply. Existing-node searches found no duplicate second-variable naturality node, and the recorded Mathlib searches found no sheaf Ext/cohomology comparison declaration.

Changes: added the existing scheme-module enough-injectives node to Step 1, `proof_deps`, and `citations.json`, because the step applies derived-functor results requiring that hypothesis. No mathematical statement was changed and no new node was created.
