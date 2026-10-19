# Delivery report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-integral-pullback-comparison-realization.json` — repaired statement split; no Mathlib match.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none.

WANTED: none.

No new DAG node was needed. The existing reduction and coherence nodes already state the strict-level facts required by the construction.

## Review by Q75

I reread the item statement and the source nodes named in every repaired step. The imported statement is unchanged. The finite-level composition input is `lem-weil-pbc-proetale-derived-pullback-composition`; its statement gives the canonical termwise pullback map on K-flat complexes. The strict tower homotopy-limit node gives the functorial exact `Rlim` and its isomorphism criterion. For the integral level maps I checked `lem-pur-integral-operations-preserve-constructible` (1), whose hypotheses are precisely a morphism of schemes with \(\ell\) invertible and a constructible integral object, and whose conclusion is the canonical reduction isomorphism. For scalar reduction I checked `lem-pur-coefficient-extension-reduction-model`: it fixes the actual quotient maps and transitions, states the coherent reduction-system counit, its independence of representatives, the \(L=E\) reduction clause, and the successive-extension clause. I also checked `lem-pur-scalar-extension-tower-coherence`, including its strict \(\kappa,\sigma,c\) tower maps and its scalar-extension square identity. The K-flat, change-of-rings, K-injective, completed-operation, resolution-independence, completion-map \(\chi\), and rationalization statements were read at their cited files and match the hypotheses used.

Step 1 now uses the K-flat resolution, derived change of rings, the two operation definitions, the constructibility reduction isomorphism, and the coherent coefficient-extension model to establish the actual normalized quotient towers. Step 2 uses only the K-injective tower resolution and the strict-tower `Rlim` construction, so the counit is a whole-tower morphism. Step 3 constructs \(\eta,\lambda,\mu\) from those maps; the finite pullback map, constructibility reductions, and coefficient-extension counit supply levelwise isomorphisms, and the `Rlim` criterion supplies the realized isomorphisms. Step 4 uses the two well-definedness nodes for resolution independence and the reduction/tower-coherence nodes for compatibility with quotient transitions. Step 5 defines \(c^E\) and \(a\) only after Steps 1–3: the strict finite composition, scalar-association, and quotient-transition maps are explicitly the maps stated by the cited nodes, so these are valid choices rather than an appeal to an unrelated existence theorem.

Step 6 was expanded to identify each factor of the scalar/composition square: applying \(F_{h,L}\) to \(a_k\) means applying termwise \(h^*\) to its strict \(\kappa\)-map, while the other factors are the corresponding strict \(\kappa\), scalarized finite \(c_{h,k,n}\), and \(L\)-level maps. The strict scalar-extension square and finite pullback naturality then give equality before realization. Step 7 uses the strict three-map reassociation for associativity and units. For \(E=L\), it explicitly compares the coherent reduction counit with the \(\chi_{E/E}\) derived-completeness map: both use the same quotient component and zero shifted component, hence the scalar comparison is the identity under multiplication and completeness. Step 8 uses the coefficient-model and strict scalar-tower clauses for \(E\subset L\subset M\), then applies exact rationalization.

The returned faults were corrected as follows: Step 3 no longer claims that either unsupported integral-composition or scalar-extension theorem states \(\eta,\lambda,\mu\); Steps 5 and 8 no longer cite those off-route theorem nodes and instead use the strict reduction/coherence statements; Step 6 no longer treats \(F_{h,L}(a_k)\) as an unspecified quotient pullback; and Step 7 now proves the \(E=L\) identity against \(\chi_{E/E}\). The proof dependency list and `citations.json` were updated accordingly, with no tool uses declared.
