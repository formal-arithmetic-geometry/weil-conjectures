# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-filtered-global-hom-exact-adjunction.json`: split statement, no new nodes, Mathlib search verdict no match for the filtered construction.
- `citations.json`: verbatim citations for every proof-step use.
- `report.md`: this report.

Attachments: none.

WANTED: none.

The imported statement was retained exactly. No source, blueprint, or brief error was found, and no new node was necessary: the existing filtered-injective model, filtered Hom-complex invariance, and filtered derived-Hom calculus provide the required interfaces. No proof remains unfinished.

## Review by Q69

I read the item node, the `sk-i-additivity` unit, the `sec-trace-formula` chapter, the current main-20261015 filtered-Hom/additivity blueprint material, and Varshavsky §5.1.5 together with §§5.1.1–5.1.2. I also opened the full statements of `lem-trf-filtered-localization-injective-model`, `lem-trf-filtered-hom-complex-invariance`, `lem-trf-filtered-derived-hom-calculus`, `def-sp-abelian`, `def-sp-injective-resolutions`, `def-sp-filtration`, `def-sp-filtered-complex-subquotients`, and `def-weil-abstract-derived-category`. The item hypotheses agree with the generic exact-adjunction route: both categories are abelian with enough injectives, filtrations are uniformly finite, L is additive and exact, R is its additive right adjoint, and the bounded-below derived unit is invertible.

Step 1 uses the filtered localization model exactly where its statement gives a filtered quasi-isomorphism to a bounded-below termwise filtered-injective complex, and the filtration and filtered-complex definitions supply the common finite interval and graded quotients. I checked that the resolution is taken in B for `L^F Q`, so its graded terms represent `L(gr^p Q)`.

Step 2 uses the injective extension-property statement and the abelian-category setting. I checked the only hypothesis that matters: exactness of L sends each monomorphism to a monomorphism. The two transposes are the given L ⊣ R adjunction, so the extension proves that R preserves injectives; the same argument is degreewise on graded terms.

Step 3 applies the stated derived-unit hypothesis to each bounded graded complex. Exactness of L identifies the graded image with `L(gr^p Q)`, and the filtered model identifies `gr^p J` with an injective resolution. The definition of quasi-isomorphism then gives a quasi-isomorphism on every grade, exactly the localization criterion. I checked that the filtration remains in the same finite interval.

Step 4 uses the explicit shift-filtered Hom-complex statement. I verified the termwise adjunction is compatible with the displayed differential and with the shift filtration: the required inclusion is transported through `L(F^aP)=F^a(LP)` because the lift is termwise exact. Naturality in both inputs follows from naturality of the adjunction and filtered chain maps.

Step 5 uses the filtered Hom-complex invariance and filtered-injective equivalence to descend the chain isomorphism, then uses the filtered derived-Hom calculus for the underlying, graded, and `H^0(omega t_{>=0}H)` descriptions. I checked that the graded index is target grade minus source grade (`q-p=r`), and that preservation of `F^0` and the quotient by `F^1` gives the forgetful and graded-projection compatibilities. Small cases checked were `L=R=id`, the zero complexes, a single pure grade (only the matching graded Hom survives), and the necessity of the derived-unit hypothesis (taking `L=R=0` fails the conclusion when the unit is not invertible).

I searched the whole DAG and blueprint for duplicate generic exact-adjunction or filtered-global-Hom statements before deciding that no child node was needed. The recorded Mathlib searches found only ordinary adjunction/injective-preservation declarations and no filtered derived global-Hom construction. Both off-unit generic tools used by the split are declared in `split_report.tool_uses`; they supply interfaces rather than replacing the additivity route.
