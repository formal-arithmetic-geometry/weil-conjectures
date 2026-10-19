# Repair report: thm-pod-global-verdier-duality

## Files written
- dag/nodes/sec-six-functors/thm-pod-global-verdier-duality.json: retained repair replaces returned step 3 by short cited steps; statement and Lean audit unchanged.
- dag/nodes/sec-six-functors/lem-pod-point-duality-coefficient-compatibility.json: new statement-only lemma; no Mathlib match in the retained logged searches.

## Attachments
None. AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek in WeilConjectures/SixFunctors/Etale/Derived/GlobalDuality.lean gives only Nonempty at finite coefficients, with no specified canonical natural map or coefficient coherence. It does not state this item.

## WANTED
None. This repair follows the available current blueprint proof and its existing supporting statements.

## Faults repaired
The return identifies the 2239-character coefficient compatibility step as hiding arguments. The retained repair exposes the exchange square, point evaluation, operation reduction, point-duality coefficient coherence, and smooth orientation comparisons as distinct steps citing their actual statements. The point-duality coherence is a new, strictly smaller lemma, with no global cohomology or Verdier exchange assertion.

## Not duplicates
lem-pod-point-duality-coefficient-compatibility vs lem-pod-point-dualizing-complex: the existing lemma identifies point internal dual with coefficient dual but does not state compatibility of that specified identification with coefficient changes.
lem-pod-point-duality-coefficient-compatibility vs lem-fix-operation-reduction: the existing node compares site operations and evaluation under coefficient change but does not compare them through the point fibre identification.
lem-pod-point-duality-coefficient-compatibility vs lem-sf-point-fibre-derived-tensor: the existing node compares tensors and units, not the specified point-dualizing isomorphism.
lem-pod-point-duality-coefficient-compatibility vs lem-pod-global-duality-map-identification: the existing node identifies global-duality maps, depends on the present item, and supplies no general coefficient-change square for the point identification.

## Review by Q24
I read the item in the shared repository and retained sandbox, its main-20261015 statement and both proof paragraphs, the chapter record and sk-thm-sf-package unit route, and the statements of all dependencies. The statement and Lean record remain unchanged. The route remains exchange followed by evaluation at the point, followed by the coefficient-change comparison square and unit specialization; the proper case without descent uses thm-sf-global-duality as before.

Step 1 uses fix-cor-verdier-exchange with f=a_X, Y=s and M=K. The admissibility assumption is from def-pod-conventions; the identity compactification verifies identity admissibility directly. Step 2 uses precisely the point-dualizing identification and the definitions of the two cohomology functors, with Fib_s applied as a functor. Step 3 uses the exchange statement's coefficient compatibility, not a new ordinary-direct-image reduction theorem. Step 4 uses the tensor/unit comparison of lem-sf-point-fibre-derived-tensor. Step 5 uses operation reduction only on its stated domains, distinguishing integral and finite-quotient internal Hom. Step 6 isolates the formerly implicit point-duality coefficient-change coherence in the new lemma. Step 7 names the four existing purity comparison statements separately: finite reduction, integral reconstruction, integral scalar naturality and rational/common-stage transport. Step 8 substitutes those equalities. Step 9 proves the unit Hom identity by evaluation at 1 and its explicit inverse. Step 10 keeps the proper, non-descending branch and uses its stated canonical global-duality theorem, without deriving ambient admissibility from properness.

The new lemma's source is the site-perfect coefficient-comparison portion of the second blueprint proof paragraph. Its assertion is local to the point identification, not a clause restating global duality. I read its logged search hits: ordinary Module.Dual base change is not derived pro-etale point duality. I checked zero complexes, degree shifts, the identity coefficient map, n=m and the unit complex; the proposed compatibility is the commutation of canonical evaluation comparisons in these cases. The finite quotient need not be flat, so no flatness is assumed. The final repair adds the missing domain preservation citation and makes every cited comparison explicit. The completed second dry run passed server preflight and wrote the durable receipt at head 83004c3daf. The subsequent edits only complete the item search record and this report; the final check will validate those too.

## Validation and provenance
The first dry run found absent chapter/unit fields on the new node and the retained item status unsplit; both were repaired. The second passed. The proof origin is agent-written because the followed blueprint proof is itself agent-written, as brief-stage1 section 2 requires. The source document and places are retained. I reused the logged item searches and copied their actual query texts/results into the item rather than rerunning unchanged queries.

The new node was checked also against thm-sf-ctf-stability: that theorem supplies preservation and site internal-Hom coefficient comparisons, whereas the new node asserts the square for the specific evaluated point-dualizing identification. In applying it I verified C=Ra_X!K and D_sC lie in the point finite-Tor domain. This removes the prior ambiguous assumption that site-perfect K on X alone supplies site-perfect C on s. No extra hypothesis is added to the item. Its finite-quotient comparison is not inferred from flatness.

Step 8 has no citations because it only substitutes the already established equalities from steps 3--7; all non-elementary inputs remain explicitly cited there. The only new statement has no proof or proof dependencies. There are no long non-elementary proof steps, no source error requiring a statement dispute, no unlogged searches, and no change to Lean data. No SGA source is used. All work is stage 1.

## Remaining work
Final dry run, then direct delivery as authorized by the dispatched brief.
