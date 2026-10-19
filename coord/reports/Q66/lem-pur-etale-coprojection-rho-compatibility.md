# Worker report: lem-pur-etale-coprojection-rho-compatibility

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-coprojection-rho-compatibility.json`: repaired split of the target; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-coprojection-composition-mate.json`: new statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-etale-rho-monoidal-mate.json`: new statement-only auxiliary lemma; no Mathlib match.
- `citations.json`: verbatim quotations for every node used by every proof step.

## Attachments

None. I searched the slopmaster2 source for the item id, its title, the five-arrow `B` comparison, and the relevant normalized-rho names. No sorry-free project declaration states the whole item.

## WANTED:

None.

## What was wrong and what I repaired

The returned split had a real E5/C4 gap in step 3. It asserted that the co-projection mate commutes without writing either required calculation. I added two smaller statement-only nodes. `lem-pur-coprojection-composition-mate` states the co-projection composition formula obtained by mating projection associativity along the canonical exceptional compositor. `lem-pur-etale-rho-monoidal-mate` states the missing finite-coefficient identity
`mu_e rho_{e,M tensor N} = (rho_{e,M} tensor 1) coProj_e`,
which says exactly that normalized etale `rho` intertwines the exceptional co-projection with the monoidality of `Le^*`. Both nodes introduce their own categories, morphisms, adjunctions, and inputs; neither restates the target square. I searched the whole DAG and current blueprint for both facts and found no duplicate. I also ran LeanFinder, Loogle, grep, and LeanSearch for each new node; the recorded results are the actual outputs, with unavailable/no-match verdicts as appropriate.

The item proof now replaces the broad `sk-thm-sf-compatibility` citation. Step 1 cites the narrow exceptional mate/compositor facts. Step 3 writes the two identities, substitutes the rho-monoidality equality into the composition mate equality, uses naturality of the closed-immersion co-projection and the canonical pullback/tensor comparisons, and explicitly observes that `Ex_!` is not used. Step 4 pastes this equality with the five arrows defining `B`. I changed `proof_origin` to `agent`, since the current blueprint's Step 4(ii) names the compatibility but does not supply this calculation.

## Not duplicates

- `lem-pur-coprojection-composition-mate` vs `lem-sf-composition-projection-mate`: the existing node states associativity for the direct-image projection transformation on compactification models; the new node states the resulting right-adjoint co-projection identity on the finite exceptional categories.
- `lem-pur-etale-rho-monoidal-mate` vs `lem-pur-finite-etale-dualizing-normalization`: the existing node gives rho identity, composition, base-change, and unit normalization; the new node gives the tensor/projection mate compatibility absent there.
- `lem-pur-etale-rho-monoidal-mate` vs `lem-pur-system-projection-tensor-associativity`: the existing node concerns strict semilinear systems and tensor associativity of projection maps; the new node concerns finite-coefficient normalized etale exceptional comparisons.

## Review by Q66

I read the retained target statement and the current `sk-thm-regular` unit, the Step 4(ii) paragraph in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/sk-thm-regular.proof.md`, and the full statements of every cited node. For the target I checked the fibre-product typing (`e i_U = i v`), the etaleness of `v`, the finite-Tor constructible domains, and the directions of `rho_e`, `rho_v`, `c_{e,i_U}`, and `c_{i,v}`. I checked that the five arrows defining `B` have matching source and target objects.

Step 1 uses the Stacks base-change node only for `v` etale, `pur9-def-upper-shriek-composition` for the displayed `c` arrows, `lem-sf-mate` and `thm-sf-comp-composition` for their mate-normalized composition and pasted counits, the normalized-rho node for `rho_e` and `rho_v`, and the new composition-mate node for the corresponding co-projection pasting. Step 2 uses the co-projection statement and the counit-defined projection transformation, so the two horizontal maps are the specified canonical maps. Step 3 uses the finite projection associativity clause through the narrow citations, then the two new nodes: the first gives the explicit co-projection composition equality and the second gives the rho/monoidality equality. I checked the substitution at `e`, the naturality square at `i_U`, and the canonical identification `Li_U^*Le^*L = Lv^*Li^*L`; no base-change exchange enters because `B` is built only from composition and pullback/tensor maps. Step 4 is the resulting paste with the five factors of `B`, and its naturality in `K` and invertible `L` gives the Tate twist specialization.

I checked small cases `e=id`, a clopen etale inclusion, the empty fibre product, codimension zero, and disconnected componentwise schemes; each reduces to the identity or componentwise canonical mate square. I verified that every `proof_deps` entry is the union of step uses and that every `citations.json` quote is a verbatim substring of its node statement. No Lean, compiler, Lake/build, live project, or launcher file was modified.

## What could not be finished

Nothing remains for this stage-1 split. The server `check_dag` check and delivery preflight both passed on the repaired sandbox.
