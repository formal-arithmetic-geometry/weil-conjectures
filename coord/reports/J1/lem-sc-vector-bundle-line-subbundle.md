# Delivery report

1. Files written:
   - `dag/nodes/sec-picard-framework/lem-sc-vector-bundle-line-subbundle.json` — item, statement node, Mathlib no-match after LeanSearch/LeanFinder/Loogle and source grep.
   - `dag/nodes/sec-picard-framework/lem-sc-dvr-saturation-line.json` — new unsplit statement node, Mathlib no-match after all three searches.
2. Attachments: none.
3. WANTED: none.
4. Nothing was wrong with the item statement. The imported proof was only a paragraph, so I made the stalkwise saturation argument and the coherence/local-freeness passage explicit. The supporting saturation node is deliberately statement-only as required for a new unsplit node.
5. I could not formalize the local algebra in Lean because this is a stage-1 DAG delivery; no Lean source was changed.

## Review by J1

I read the item node and the rank-induction source in `lem-sc-riemann-roch`, including the paragraph beginning “Choose 0 != s in E_eta”, and checked the Stacks source cited there. The relevant local algebra is the DVR calculation used in Tag 0CC4 (torsion-free finite modules over a regular one-dimensional local ring are free); the new node records the additional saturation calculation that is not a Mathlib declaration. I searched the full DAG and the slopmaster2 source for an existing saturation or line-subbundle statement and found none. The existing nodes `lem-sc-integral-scheme-stalks-in-function-field`, `lem-sc-regular-dim1-dvr`, `pqf-lem-pushforward-qcoh`, `lem-weil-pbc-quasi-coherent-module-kernel`, `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`, and `lem-sc-regular-curve-torsionfree-free` were read against the item hypotheses. I replaced an initial citation to the smooth-curve local-rings theorem because the item only assumes regularity; dimension one plus regularity supplies a DVR at every nongeneric point.

Step 1 uses the integral-scheme stalk statement for injectivity into the function field; this identifies the kernel stalk with `E_x cap K s` and gives generic fibre `K s`. Step 2 uses the regular-local-dimension-one theorem for DVR stalks and the new saturation node for rank-one freeness of the intersection and rank `r-1` freeness of the quotient. The generic point is handled directly as a field. Step 3 uses quasi-coherent pushforward and kernel statements before the coherent submodule theorem; the regular-curve torsion-free criterion then supplies finite local freeness and constant ranks, and rank one is invertible. Step 4 is elementary exactness from kernel and quotient definitions.

I tested the local statement on rank one with `s=1`, rank one with `s=t^n`, and on `R^2` with `s=(1,0)`; the saturated line is `R` in each rank-one case, while in the rank-two case it is `R(1,0)` with quotient `R`. For a general vector, clearing denominators gives a nonzero element of the intersection; saturation makes the quotient torsion-free, and the finite torsion-free modules over a DVR are free. I checked that `s=0` is excluded and that no proof dependency reaches the item itself. The item’s blueprint `from.place`, `same_as`, split status, proof dependencies, and `split_report` were filled; the new node has the required blueprint ancestor, source, searches, and statement-only unsplit form.
