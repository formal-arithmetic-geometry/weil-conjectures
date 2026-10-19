# Stage 1 report: lem-sbc-base-change-arrow-localization

Files written:

- `dag/nodes/sec-smooth-base-change/lem-sbc-base-change-arrow-localization.json` — repaired five-step split; no statement change.
- `dag/nodes/sec-smooth-base-change/lem-sbc-sets-underived-exchange-sectionwise.json` — one new unsplit statement-only node; Mathlib searches found no match.
- `citations.json` — verbatim excerpts for every cited node in every step.
- `searches.jsonl` — retained the prior item searches and appended the four required searches for the new set-valued node.

Attachments: none. I found no exact sorry-free declaration for this item in the project Lean source.

WANTED: none.

## Not duplicates

`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-weil-pbc-underived-exchange-sectionwise`: the new node is for sheaves of sets and the existing node is only for abelian sheaves; their coefficient categories and exchange targets differ.

`lem-sbc-sets-underived-exchange-sectionwise` vs `def-weil-pbc-underived-exchange`: the existing definition states the abelian exchange and its representative clause, while the new node states the corresponding set-valued transpose and the sectionwise formula needed by this item.


`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-sbc-base-change-arrow-localization`: the new node is a general Cartesian-square section formula for one exchange map; the item compares global and localized maps and includes the maps (C_L,C_R), etale factorizations, and naturality.

`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-weil-pbc-etale-cover-detects-iso`: the existing node detects isomorphisms of abelian sheaves on a covering; the new node computes a set-valued exchange map on representatives.

`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-weil-pbc-etale-covering-base-change`: the existing node transports etale covering families under scheme base change; the new node computes sections of a set-valued exchange morphism.

`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-weil-pbc-etale-localization-exchange`: the existing node concerns localization of an abelian exchange map and its isomorphism; the new node is the set-valued section formula before localization.

`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-weil-pbc-etale-underived-exchange-restriction`: the existing node states the abelian restriction comparison; the new node supplies the missing set-valued representative formula.

`lem-sbc-sets-underived-exchange-sectionwise` vs `lemma-weil-pbc-target-locality`: the existing node is a locality/gluing statement for target properties; the new node is a sectionwise calculation for a Cartesian exchange map.

`lem-sbc-sets-underived-exchange-sectionwise` vs `lem-sbc-derived-base-change-arrow-localization`: the existing node compares derived exchange arrows; the new node is underived and set-valued.

`lem-sbc-sets-underived-exchange-sectionwise` vs `sbc-lem-etale-locality`: the existing node proves etale locality of base-change isomorphisms; the new node is the lower-level set-valued representative formula used to identify local and global arrows.

The item statement remains the statement of the current main-20261015 blueprint and Stacks Tag 0EZR. I read the item, the parent `sbc-lem-etale-locality`, the main-20261015 blueprint proof, Stacks Tag 0EZR (`lemma-base-change-local`), and all cited node statements. The returned version had four defects in step 3: it falsely identified the global and local representative targets, it used the wrong object map for the global representative, it said that the representative actions of (C_L) and (C_R) followed without calculation, and it applied the abelian-only sectionwise lemma to sheaves of sets. I corrected all four and split the long calculation into separate steps.

## Review by NJ

For the new node I searched the whole DAG and blueprint for set-valued sectionwise exchange statements and found only the abelian node `lem-weil-pbc-underived-exchange-sectionwise`; the new statement is therefore not a duplicate. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` for the new node. The hits were generic sheaf, pullback, and etale-stability declarations; none states the set-valued exchange formula, so `mathlib_match` is null. I tested the new statement on an identity Cartesian square, on an empty (V), and on a terminal sheaf; the representative formula reduces to ordinary restriction and remains well-defined.

Step 1 uses the base-change-square statement, inverse-image composition, and site-morphism composition. I checked that the universal property gives (Y_U\cong U\times_B T_B) and that (ce_U=ed). I explicitly define the canonical map
\[
\kappa:Y_U\times_{T_B}(T_B\times_BW)\to Y\times_T(T\times_SW)
\]
from (d,c,\mathrm{id}_W), and state only (kappa\ell_{\mathrm{loc}}=\ell_{\mathrm{glob}}); no isomorphism claim is made. This directly repairs the returned E3 counterexample.

Step 2 uses exactly the two natural isomorphisms in `lem-weil-pbc-slice-site-localization`, the slice-to-small-etale equivalence, and the set and abelian restriction statements to construct (C_L) and (C_R). It makes no mate-compatibility assumption.

Step 3 is the representative computation for (C_L). I checked the cited unit clause (c_{f,g,F}(g^*(f^*s))=(f\circ g)^*s) and both restriction-unit statements. The map (a:Q\to U\times_BW) is described as over (U), and the global representative is explicitly the map (Q\to X\times_SW), with (X)-component (Q\to U\to X). Thus the action (a'^*(f^*s)\mapsto a^*(f_U^*s)) is derived from the cited unit formula rather than asserted.

Step 4 uses the new set-valued sectionwise node and the existing abelian sectionwise node separately. For the global representative it computes (ell_{\mathrm{glob}}^*(e^*s)); for the local representative it computes (ell_{\mathrm{loc}}^*(e_U^*s_B)). The restriction clauses give (kappa^*(e^*s)=e_U^*s_B), and the map identity from step 1 then gives equality after (C_R). The transitions in (W) are covered by the sectionwise representative statements, so the calculation descends through sheafification. This repairs C4/E1 and the previous C1/E5 return.

Step 5 uses only the inverse/direct-image adjunction and the site-composition statement. Its adjunction hom-bijection is injective, so equality of adjuncts from step 4 gives the stated equality of transposes and naturality in (F).

I verified every step's `uses` against the cited node statement and copied each citation quote verbatim into `citations.json`; `proof_deps` is their union. The edge cases checked for the repaired item were identity maps, (B=S), (U=X), an empty (U), the zero sheaf, and an isomorphism (f_U). No SGA source is used.

