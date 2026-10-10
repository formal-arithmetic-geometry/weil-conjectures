1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-noetherian-closed-points-finite.json` (item, statement split into three steps).
- `dag/nodes/sec-curve-estimates/lem-sc-noetherian-closed-subset-finite-components.json` (statement, Mathlib leaf; `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`).

2. Attachments: none. No sorry-free slopmaster2 declaration states the item.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had an empty proof and no proof dependencies. The first paragraph of the source uses finiteness of irreducible components for the closed subset itself, which was not stated by the existing scheme-level finite-components node, so I added the closed-subset specialization as a Mathlib leaf. The item now cites it explicitly, then cites scheme sobriety for the generic point of each component; the final finite-union step is elementary.

5. What I could not finish: nothing.

## Review by G1

I read the item source reference (Properties Lemma 0BA8) and the existing statement of `lem-sc-scheme-sober` (Schemes Lemma 01IS). I also read the Mathlib source around `noetherianSpace_of_isClosed` and `NoetherianSpace.finite_irreducibleComponents`, and searched the DAG and source checkout for an exact item declaration or an existing closed-subset component-finiteness node. The new leaf states exactly the fact used in step 1 and records the closed-subtype specialization and all three required searches. Step 1 uses only that leaf, whose statement explicitly gives a finite union of irreducible components of E. Step 2 uses the sober-node statement that each irreducible closed component has a generic point with closure equal to the component; since the item hypothesis makes that generic point closed, the closure is its singleton. Step 3 is the finite union calculation and is marked elementary. I checked the empty set (zero components), a one-point scheme, an integral curve (one component, with only its closed-point case satisfying the hypothesis), and a finite discrete scheme; all agree with the statement. The item and new node carry the required blueprint ancestry and the citations file quotes the exact statements used.
