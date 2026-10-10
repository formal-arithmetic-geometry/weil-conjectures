Files written:

- `dag/nodes/sec-picard-framework/cor-picard-degree-g.json` — statement, no new nodes; Mathlib searches found no match.
- `citations.json` — verbatim quotes for every cited proof step.

Attachments:

- `AlgebraicGeometry.Scheme.degree_eq_genus` is not attachable: its body is sorry-free but the transitive sorry map reaches cohomology declarations. The open flat-base-change declaration is already represented by `lem-sc-flat-base-change-coherent`.

WANTED:

- None.

What was wrong in the imported node:

- The imported proof compressed the computation into one paragraph and cited Riemann–Roch and curve connectedness without making the cohomology calculation explicit. Its Lean declaration is transitively sorried, so it cannot be attached.
- I kept the statement and replaced the proof with three steps: the assumed vanishing gives `chi(L)=1`; flat base change gives `H^0(O_{X_K})=K`, genus base change gives the dimension of `H^1`, and curve vanishing removes degrees at least two; finally the degree definition gives the result.

## Review by J1

I read the item source `literature/blueprint/master/blueprint/sec-picard-framework/sk-cor-picard-degree-g/cor-picard-degree-g.md`, the unit record `sk-cor-picard-degree-g`, and the Lean declaration in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean` (the declaration is at lines 1667–1700 in the slopmaster2 checkout). The Lean statement matches the mathematical item, but its transitive dependencies include the sorry-backed cohomology declarations recorded in `lean_audit`, so I did not attach it.

For step 1, `def-pc-euler-characteristic` explicitly defines chi as the alternating sum of cohomology dimensions; the stated `h^0=1` and positive-degree vanishing therefore give chi equal to one. For step 2, `lem-sc-flat-base-change-coherent` states the cohomology tensor-product isomorphism for a proper scheme and flat field extension, so it applies to the structure sheaf and the hypothesis `H^0(X,O_X)=k`. `lem-pc-genus-base-change` states `dim_K H^1(X_K,O)=g(X)`, and `lem-pc-vanishing-above-dim` states vanishing in degrees at least two for smooth projective curves; these are exactly the facts needed for `chi(O_{X_K})=1-g`. Step 3 uses the verbatim degree definition in `def-pc-degree-line-bundle` and is elementary substitution. Every citation is quoted in `citations.json` from the node statement itself.

I searched the DAG and blueprint for duplicate base-change or cohomology statements before editing; the existing nodes above cover all dependencies, so no new node was created. I also ran the required LeanFinder, Loogle, grep, and LeanSearch Mathlib searches for the item; LeanSearch was unavailable and is recorded as such, while the other searches returned no Mathlib declaration. The small edge cases are consistent: for genus zero the formula gives degree zero when the hypotheses hold, and the supplied counterexample explains why geometric irreducibility and `H^0(X,O_X)=k` are necessary.

## Second reading by J1

- Item statement: checked against the unit record and imported blueprint; definitions for genus, base change, field extension, and invertible sheaf are now cited explicitly.
- Step 1: checked against `def-pc-euler-characteristic`; the alternating-sum substitution uses exactly the stated vanishing hypotheses.
- Step 2: checked against `lem-sc-flat-base-change-coherent`, `lem-pc-genus-base-change`, and `lem-pc-vanishing-above-dim`; flatness of a field extension and preservation of smoothness/projectivity under base change are stated before applying the cited nodes.
- Step 3: checked against `def-pc-degree-line-bundle`; the final subtraction is an elementary substitution.
- New nodes: none; all auxiliary facts are covered by existing DAG nodes.
- Changes: added missing definition references in the item statement, made step 2 hypotheses explicit, and retained the verbatim citation quotes.
