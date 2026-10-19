## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-mapping-adjunction.json` — repaired finite-level mapping-adjunction item.
- `dag/nodes/sec-six-functors/lem-coef-finite-point-internal-hom-evaluation.json` — repaired finite-Tor point internal-Hom evaluation node.
- `citations.json` — regenerated verbatim quotes for all 29 step/node citations.

## Attachments

None.

## WANTED:

None.

## Not duplicates

`lem-coef-finite-point-internal-hom-evaluation` vs `lem-pod-point-dualizing-complex`: the existing node gives the point dualizing normalization and coefficient duality, while this node restricts to the finite-Tor domain and adds the explicit evaluation-transpose characterization needed by the mapping-adjunction item.

## What was wrong and what was corrected

1. The previous Step 5 used “transport” without an interface stating what was transported. I added `lem-pur-projection-comparison-etale-origin` for the fixed-compactification projection map, `lem-pur-bounded-site-adjunction-transpose` for the bounded etale-origin adjunction transpose and counit, and `lem-sf-etale-proetale-exceptional-transport` for the transported exceptional counit. Step 5 now names the projection, evaluation, and counit composites and these three compatibilities explicitly.
2. The point node previously quantified over all bounded constructible point complexes, although its proof uses the finite-Tor fibre-tensor comparison. Its statement now quantifies over D^b_ctf(s,A_n), introduces R, varpi, and A_n, cites the matching coefficient and tensor/Hom definitions, and ties its normalization to `lem-pod-point-dualizing-complex`. The item proves that F_n M is ctf before applying it.
3. The former Step 3 applied the point statement to an etale object without checking its site and Tor hypotheses. It now applies the node to the pro-etale object F_n M, obtains its ctf property from `thm-sf-ctf-stability`, and uses `lem-sf-class-compact-support-comparison` plus `lem-sf-comparison-tor-amplitude` to check the etale compact-support origin as well.
4. Step 2 now invokes clause (ii) of `lem-sf-comparison-tor-amplitude` to verify that the chosen etale origin M_et has finite Tor amplitude before using `lem-weil-finite-duality-site-comparison`.
5. Step 4 now explicitly cites `lem-weil-pbc-comparison-global-cohomology` when transporting derived global sections from the etale adjunction to the pro-etale side.
6. The item statement no longer credits the point identification to the category equivalence `lem-weil-point-fibre-equivalence`; it cites the evaluation-defined point node and its point-dualizing normalization. The new node dependency list now matches every notion in its statement. The creator remains Q65 and no stale Q91 metadata remains.

## Review by Q65

I reread the current main-20261015 proof `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`, second paragraph, and the source statement for the item. The item keeps the source's finite object omega_X,n = Ra_n^! A_n, the fixed compactification, the bounded constructible finite-Tor hypothesis on M, and the counit-defined transpose. The point node's source is the corresponding point-dualizing proof; I checked its finite-stage specialization against `lem-pod-point-dualizing-complex`.

Step 1 uses `thm-fix-general-biduality` exactly for the image of the constant coefficient object under derived internal Hom into Ra_n^! A_n, and the two coefficient-category definitions for the ctf hypotheses. The constant finite coefficient object is the elementary bounded finite-projective object. Step 2 uses `lem-sf-proetale-constructible-origin` for the etale witness, `lem-sf-comparison-tor-amplitude` clause (ii) for the missing etale Tor-amplitude check, and `lem-weil-finite-duality-site-comparison` for the internal-Hom, dualizing-object, and evaluation comparisons; all hypotheses are now stated before application.

Step 3 uses clause (iv) of `thm-sf-ctf-stability` to put F_n M in D^b_ctf, the compact-support comparison to identify its etale origin, clause (ii) of the Tor-amplitude comparison for that origin, and the repaired point node for the evaluation-defined coefficient dual. Thus the point node is applied to a pro-etale ctf object, exactly its stated domain. Step 4 uses `prop-asd-internal-adjunction` with the compactifiable Noetherian structure map and then cites `lem-weil-pbc-comparison-global-cohomology` for the global-sections transport. The finite site comparison, compact-support witness, and Step 3 point map identify the two transported terms with the two sides of gamma.

Step 5 uses `lem-asd-internal-adjunction-evaluation` for the ordinary transpose formula. I read the statements of `lem-pur-projection-comparison-etale-origin`, `lem-pur-bounded-site-adjunction-transpose`, and `lem-sf-etale-proetale-exceptional-transport`; respectively they provide projection compatibility, the specified bounded-origin adjunction/counit compatibility, and the transported exceptional counit. Together with the two evaluation comparisons and compact-support comparison, they say exactly that the resulting map is the counit-defined map in the item. Step 6 records naturality only after citing each comparison that supplies it; it is marked non-elementary because naturality of the composite is inherited from those interfaces.

I checked every citation against its node statement and regenerated citations.json from those statements. The report declares the off-unit tools used by the route, including global cohomology comparison, finite-Tor stability, projection comparison, bounded adjunction transpose, exceptional transport, and point duality. I tested the repaired point statement and item on C = 0, M = 0, X = s, n = 1, and the identity compactification; the maps reduce to the zero, coefficient-unit, or ordinary module evaluation maps with the displayed types. No SGA source was used, no Lean file was written, and no compiler or build tool was run.

## What remains

The required server-side dry run is the remaining check for this repaired delivery.
