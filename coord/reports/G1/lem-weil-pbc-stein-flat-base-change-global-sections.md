# Stage 1 split report: `lem-weil-pbc-stein-flat-base-change-global-sections`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-flat-base-change-global-sections.json`: split the item with one proof step using the existing generic flat-base-change node.
- No new child node was needed. The reusable result is already the imported node `lem-pc-flat-base-change-cohom`, whose statement covers all cohomological degrees and quasi-compact quasi-separated morphisms.

## Proof and source audit

The proof is the proper degree-zero specialization of Cohomology of Schemes, Lemma 30.5.2 (Stacks Tag `02KH`). In the cartesian square for `X -> Spec R` and `Spec R' -> Spec R`, use the quasi-coherent structure sheaf `O_X` and degree `i=0`. Properness supplies quasi-compactness and quasi-separatedness, and its pullback is `O_{X_U}`. The theorem gives

`H^0(X,O_X) tensor_R R' = H^0(X_U,O_{X_U})`.

Under `H^0(X,O_X)=R`, the left side is canonically `R'`, proving the final clause. The source is the statement and proof of Tag `02KH`, especially the affine formula and its hypotheses (online source lines 23--54); the item source also records its use in the proof of Stein factorization Theorem 37.53.5 (Tag `03H2`).

## Search audit

The item already records LeanSearch, Loogle, and Mathlib grep searches dated 2026-10-10. They find `Scheme.Hom.appTop` and related constructions but no theorem for proper global-sections flat base change, so the item is not a Mathlib leaf. The imported node `lem-pc-flat-base-change-cohom` is the required reusable proof lemma and is cited as the sole proof dependency/tool use.

## Review by G1

I checked the specialization against Tag `02KH`: the generic theorem assumes a flat base map and a quasi-compact, quasi-separated morphism, exactly supplied here by `R -> R'` and proper `f`. Its sheaf input is the quasi-coherent structure sheaf, and pullback identifies it with the structure sheaf on `X_U`. Taking `i=0` gives the stated canonical global-sections map; the normalization `H^0(X,O_X)=R` gives `R tensor_R R' = R'`. The proof uses only the existing imported generic DAG node, so no reusable lemma is private or omitted. The node retains unit `sk-thm-p1`, has a statement-only proof child requirement satisfied by the cited generic node, and passes the Stage 1 mechanical checks.
