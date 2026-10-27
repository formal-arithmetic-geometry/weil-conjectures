# Stage-1 worker report: lem-sfb-minimal-parabolic-split-centralizers

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-minimal-parabolic-split-centralizers.json`: item, split; statement and its statement dependencies retained; eight proof steps and exact proof-dependency union supplied. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-parabolic-prescribed-split-cocharacter.json`: new statement-only node; unsplit, no Mathlib match. A defining cocharacter of a parabolic inside a prescribed maximal split torus; no Levi or conjugacy conclusion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-unipotent-torus-absorption.json`: new statement-only node; unsplit, no Mathlib match. A split torus in U semidirect D can be conjugated into D under U(k); no reductive group, minimal parabolic, or Levi-centralizer assertion.
- Sandbox `citations.json` contains a verbatim statement quotation for every cited node in every item proof step. `searches.jsonl` contains the actual search-command results; all recorded new-node searches are drawn from it. `build_split.py` and `milne.txt` are sandbox working material, outside the delivery tree.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, minimal parabolics, split tori, centralizers and cocharacters. No declaration states this item. The older slopmaster2 source search also gave no matching declaration. No Lean was written and no compiler, Lake, or build was run.

## WANTED

None for the chosen route. The book is locally present. The author errata entry at https://www.jmilne.org/math/Books/iagerrata.html, “p.545 et seq.”, was read online to confirm the existing minimality correction. The proof does not invoke the unavailable Springer 1998, 16.1.1 reference from Milne 25.6(c). It supplies the conjugacy argument through Milne 16.54 instead. No SGA source is used.

## Source error

Milne 25.6(b) as printed omits minimality. For G=GL_2 and P=G, the diagonal maximal split torus has centralizer the diagonal torus, whereas R_u(G)=1; the asserted decomposition would make GL_2 equal to that torus. The author's errata explicitly adds minimality in (b). The live item already contains this correction and asserts only existence, not uniqueness, of the conjugator. I retained its statement unchanged. Minimality is used precisely in proof step 3 to turn P_lambda contained in P into equality. This is not an additional field hypothesis. I also used the actual all-field reductive-centralizer consequence 17.59, with the existing algebraically closed centralizer node, rather than misapplying the algebraically closed hypothesis of 17.57 directly over k.

The conjugacy source is not treated as a proof. Steps 6 and 7 write the comparison of the two cocharacters and the two reductive complements. Thus no new node simply repeats the conjugacy clause of the item.

## Not duplicates

lem-sfb-parabolic-prescribed-split-cocharacter vs lem-sfb-reductive-cocharacter-parabolic-geometry: the existing node constructs P_lambda and its quotient from an already given lambda; it does not state that a given parabolic has such a lambda in a prescribed maximal split torus. The new node asserts only this converse/choice, not the existing geometry.

lem-sfb-parabolic-prescribed-split-cocharacter vs lem-sfb-field-parabolic-isotropy-criterion: the latter starts with a noncentral split torus and asserts existence of some proper minimal parabolic; it neither starts with a specified P nor chooses a cocharacter in a specified maximal split torus of P.

lem-sfb-parabolic-prescribed-split-cocharacter vs lem-sfb-standard-parabolic-levi-charts: the latter concerns algebraically closed fields, semisimple groups and standard root-indexed parabolics; it does not give the prescribed rational split-torus cocharacter for an arbitrary reductive group over any field.

lem-sfb-split-unipotent-torus-absorption vs lem-sfb-triangular-quotient-section-conjugacy: the existing result concerns upper triangular groups over algebraically closed F and two sections of a fixed quotient. The new node concerns arbitrary k, a split smooth connected unipotent kernel, and a split torus subgroup that is not initially a section.

lem-sfb-split-unipotent-torus-absorption vs lem-sfb-solvable-torus-complements: the latter assumes algebraically closed F and identifies a maximal torus with a torus quotient; it does not give rational conjugacy or containment over arbitrary fields.

lem-sfb-split-unipotent-torus-absorption vs lem-sfb-split-solvable-torsors-and-variety: the latter proves Zariski-local triviality of torsors and the underlying scheme geometry of split solvable groups; it has no conjugacy conclusion.

lem-sfb-split-unipotent-torus-absorption vs lem-sfb-rosenlicht-split-solvable-criterion: Rosenlicht detects splitting from a dominant morphism from a torus; it does not absorb torus subgroups into a chosen complement.

lem-sfb-split-unipotent-torus-absorption vs lem-sfb-split-torus-no-invariants-unipotence: the latter supplies split-unipotent structure from absence of torus invariants in the tangent space; it has no assertion about conjugating a torus subgroup.

Both new nodes vs lem-sfb-minimal-parabolic-split-centralizers: neither restates its clauses. The first stops before centralizer equality, containment or Levi decomposition; these are proved by the weight perturbation, minimality and cocharacter geometry in steps 2--5. The second is a split-solvable tool applied to the image of a single cocharacter, not a statement about centralizers of maximal split tori in reductive groups. The conjugacy of the two reductive centralizers is obtained by the double centralizing argument in step 7.

Whole-DAG searches used the source places 25.1, 13.33, 17.60, 16.54 and 16.29(d), and the notions parabolic/cocharacter, Levi, split torus and split solvable/conjugacy. Whole-blueprint searches using tools/blueprint_refs.py for parabolic, cocharacter, torus, centralizer, split solvable, prescribed split torus, torus complement and split unipotent conjugate produced no duplicate. The three centralizer keyword hits concern characteristic-zero geometry of affine algebraic groups, not these assertions. The ancestor command reports blueprint.from.node = None for the item; this inherited rootless chain is preserved, with its full place and via list, and each new node prepends this item to via. same_as is empty.

## Mathlib searches

Ran the mandated msearch.py commands, read the actual results and tried two phrasings of each new assertion. Searches are recorded verbatim with the tool and query text and the actual result JSON. No service was down in these runs. Loogle found no parabolic/cocharacter or IsSolvable/IsConj match. The broad grep found mostly individual parabolic 2 by 2 matrices and the string Levi in Hopkins–Levitzki; the narrower AlgebraicGeometry grep found no cocharacter, split-torus, unipotent-conjugacy or parabolic-subgroup declaration. LeanFinder found Lie Cartan/coroot results and abstract GroupExtension splitting definitions and equivalences. LeanSearch found the same abstract-group and individual-matrix notions. Read Mathlib/GroupTheory/GroupExtension/Defs.lean:317 and Matrix/GeneralLinearGroup/FinTwo.lean:39--46: IsConj is a predicate defining conjugacy of splittings, not an existence theorem, and IsParabolic is a property of a single matrix, not a reductive group-scheme parabolic. None supplies a Mathlib leaf for these nodes.

## Review by Q126

I read the standing brief, worker role, stage-1 contract, the three levels of SETUP, GOAL, the chapter and unit records, and delivery-errors B--E. I also read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image statement/proof; this item realizes a lower supporting prerequisite of clause (3), and does not change that clause or its route. I read Milne Algebraic Groups printed pp.544--546 (25.1, 25.2 and 25.6), pp.265--266 (13.33, including the matrix equations), Lemma 13.51 and its finite-character separation proof, pp.371--372 (17.57, 17.59, 17.60), and pp.333--344 around 16.29 and 16.54. The proof origin is agent: the source motivates the cocharacter route, but I wrote the finite-weight perturbation and the cocharacter comparison rather than claiming the bare Springer reference supplies them. The two new nodes have no proof, no proof dependencies and no proof sketch in their statements. They introduce every object and convention; their source records point at the exact preparatory and split-solvable results being isolated.

Step 1 uses the new prescribed-cocharacter node, whose statement supplies P=P_lambda inside the given S on every algebra. The given S is maximal in P, exactly the hypothesis used. This avoids assuming rational conjugacy of maximal split tori, which would be circular.

Step 2 uses the existing faithful-linear-representation node for a closed immersion on all algebras, the split-torus weight-decomposition node for a simultaneous weight basis, and split-torus-hom-matrices for integral characters/cocharacters. I opened all three statements and their quotations are the assertions used. The finite integer-hyperplane avoidance and the explicit N bound are written out. It is a choice of integers, not an appeal to a rational point in a nonempty open over a possibly finite field.

Step 3 uses the cocharacter-geometry node's proper projective quotient to make the perturbed P_lambda parabolic. Every other inference is the displayed matrix entry formula and Laurent coefficient comparison. Preserving the signs of the originally nonzero pairings makes the new P smaller, never larger; minimality forces equality. Separating every nonzero character difference identifies the entire scheme centralizer, even over nonreduced test algebras. I checked that the extension remains in the closed subgroup G using injectivity of polynomial-to-Laurent restriction, not by checking geometric points alone.

Step 4 uses the same cocharacter node for the represented subgroups, retraction, semidirect product, split-unipotent kernel, and scalar extension. The existing reductive-torus-fixed-subgroup statement assumes algebraically closed F; I use it only after passing to F=bar k. Its smooth connected reductive conclusion, together with the already obtained all-field smoothness/geometric connectedness, gives exactly reductivity over k. No perfectness is inserted.

Step 5 uses affine-homomorphism-flat-image to form the image of any candidate normal unipotent subgroup under the retraction. The unipotent-normal-quotient-image statement requires the ambient homomorphism to be faithfully flat; I verify that explicitly from the product coordinates. It also assumes algebraic closure, so it is applied over bar k. Its statement says precisely that the image is smooth connected normal unipotent. Reductivity kills that image, and injectivity under field tensor gives the scheme-theoretic inclusion over k. This proves maximality of the constructed radical and does not presume the symbol R_u already has the required universal property.

Step 6 uses the flat-image theorem twice and the split-torus-flat-quotient theorem twice. The latter explicitly allows non-smooth and nonreduced kernels, which matters for cocharacter images in characteristic p. The preimage H in product coordinates is U semidirect D, so the new absorption lemma applies to a split unipotent group and a split torus over the actual field k. Its conclusion provides a rational u, not merely a geometric point. The conjugated cocharacter factors through L_2; the limit and centralizer equations conjugate on every algebra.

Step 7 uses only the cocharacter-geometry node, now applied to each of the reductive groups M and L_2. The two cocharacters commute because nu lies in C_G(lambda_2). If J is contained in P_eta, its limit subgroup inside J is J itself; the polynomial-to-Laurent injection checks the limit stays in the closed subgroup J. Its smooth connected normal unipotent kernel is trivial by reductivity, and the semidirect decomposition then makes J centralize eta. Applying this first to (M,lambda_2), then (L_2,nu), gives both inclusions. This short argument uses the conclusions stated in the cocharacter node; it does not extract something from its proof or cite a Levi-conjugacy clause under another name.

Step 8 is an elementary endpoint check, with no external assertion. I tested the construction on the trivial group, a split torus with P=G, an anisotropic reductive group with P=G, the upper triangular minimal parabolic in GL_2, rank zero, repeated weights, and characteristic p cocharacters divisible by p. In rank zero the character-difference set is empty and the zero cocharacter is allowed; when minimal P=G, reductivity gives U=1 and both centralizers are G. A split-unipotent H with D=1 has no nontrivial torus subgroup, consistent with the absorption statement. For U=1, absorption is immediate containment in D. The proofs consistently use integer characters, not differentiated Lie characters, so weights divisible by the characteristic are not discarded. Every non-elementary proof step is below 2000 characters. I checked that no reused dependency has a dependency path back to the item; the server will check the whole graph. No off-unit tool citation is needed at the immediate proof level.

The statement, statement dependencies, source and inherited blueprint metadata of the item have not been weakened. I corrected the initial plan by explicitly proving the unipotent-kernel maximality and checking that the algebraically closed image/centralizer lemmas are used only after scalar extension. Nothing mathematical remains unfinished beyond the intentionally statement-only supporting nodes, which join the queue.

## Validation

The required delivery dry run exited successfully: `OK (not pushed) deliver/Q126/lem-sfb-minimal-parabolic-split-centralizers at 303e30a1ea2: preflight passed`. The server ran the delivery preflight, including DAG and split checks. The report now records that result; a final dry run checks this exact report before the authorized push. No Lean or compiler check was run.
