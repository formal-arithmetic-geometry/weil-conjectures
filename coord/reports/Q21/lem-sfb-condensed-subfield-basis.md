# Q21 repair: lem-sfb-condensed-subfield-basis

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-condensed-subfield-basis.json`: existing statement, now three proof steps and 2095 proof-text characters; statement, statement dependencies, Lean attachment and maintainer fields retained.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-topological-module-condensation.json`: new statement, status `unsplit`, no proof steps or proof dependencies; not a Mathlib leaf. It specifies continuous-function condensation on topological modules, its internal action, its maps and its finite-product comparison.
- `citations.json`: exact statement excerpts for all three proof citations.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item tag and condensed-basis terminology found no finished matching declaration. `Profinite.exists_condensedSubfieldBasisIso` in `lean/Sheaf/FieldTheory/CondensedSubfieldBasis.lean` ends in `sorry`; it is the existing statement attachment, not a completed proof.

## WANTED

None. Both statements follow the current local blueprint, with the expanded arguments explicitly attributed to agents rather than to a nonexistent external theorem.

## What was wrong and what changed

The human returned the existing reviewed split because its 3588-character proof kept too much work in one node. The sandbox contained only dispatcher marker files, not the earlier JSON or report, so I copied the live returned item and retained its statement, citations, earlier Mathlib-search records, Lean record and reviewer metadata. I changed the proof and its split report, and added one independently workable statement-only obligation. This is a substantive re-split, not a rebase-only delivery. No Lean was written and no compiler or build was run.

The original topology arguments (old steps 1 and 2) remain verbatim as new steps 1 and 2. All the sheaf arguments of old steps 3, 4 and 5 move to the new node: continuous-function sheaves and restrictions, componentwise product sheaves, natural additive postcomposition, internal action by the objectwise tensor followed by sheafification, its unit and associativity diagrams, and internal linearity of postcomposition. The new statement prescribes the actual action and maps, including finite products and regular scalars, so none of those obligations is erased by saying merely that some isomorphism exists. New step 3 only applies this construction to the continuous inverse linear maps already obtained in step 2.

The new node does not assume a field extension, a basis or a finite-dimensional space. Its construction applies to arbitrary topological modules. Thus it can be proved independently while another worker proves the topology and basis part of the existing item. It does not relocate the entire item or restate its condensed-basis clause.

## Not duplicates

lem-sfb-topological-module-condensation vs def-weil-pbc-internal-abelian-sheaf-module-equivalence: the existing statement supplies an abstract equivalence once sheaves and an internal ring are given; the new statement constructs the continuous-function input from topological modules, specifies its actual internal action and functor on continuous maps, and normalizes its finite products and regular module. I rejected the initial idea of separate abstract sectionwise-action and linearity nodes because those would duplicate this equivalence.

lem-sfb-topological-module-condensation vs lem-pe-internal-section-tensor-comparison: the existing result compares relative tensors and derived complexes through an already given internal/sectionwise equivalence. It supplies no functor on topological modules or continuous linear maps.

lem-sfb-topological-module-condensation vs sk-def-sfb-condensed-ring: the existing definition constructs continuous-function ring sheaves and ring-homomorphism maps. It does not construct module objects for general topological modules or maps that are merely linear.

lem-sfb-topological-module-condensation vs lem-sfb-finite-free-scalar-coordinates: the existing result assumes a finite-free internal module isomorphism and identifies scalar extension with finite products. The new result concerns producing internal modules and maps directly from topological ones and assumes no finite-free internal isomorphism.

lem-sfb-topological-module-condensation vs lem-weil-pbc-finite-dimensional-linear-homeomorphism: the latter is purely topological and gives no continuous-function sheaf or internal-module construction.

lem-sfb-topological-module-condensation vs lem-sfb-condensed-subfield-basis: the item must prove continuity of field-basis coordinates and exhibit the basis homeomorphism; the new node has no field, basis, coordinate map or chosen isomorphism as a hypothesis or conclusion.

No Stacks tag is introduced, so there are no same-tag pairs. I searched the entire DAG, its statement fields, and the whole imported blueprint through `tools/blueprint_refs.py` using sectionwise actions, continuous linear maps, sheafified tensor, continuous functions, topological modules and module condensation. Blueprint hits concerned unrelated operations or ring sheaves, not this topological-module construction. Source-library searches also found the ring construction, not a finished declaration of this module functor.

## Mathlib searches for the new node

All six searches in the new node are actual calls of the required `msearch.py Q21 lem-sfb-condensed-subfield-basis` command and are present in `searches.jsonl`. I read both LeanFinder result sets, both Loogle result sets, LeanSearch's eight hits and the grep output. The second phrasing asked specifically for the sheafified-tensor internal action. No service was unavailable.

The main near hit is `ContinuousMap.module'`, `Mathlib/Topology/ContinuousMap/Algebra.lean:826`: it gives the pointwise `C(S,R)`-module structure on `C(S,M)`, not an internal module over the nonconstant ring sheaf or the normalized functor. I read lines 820–833. `CondensedMod` at `Mathlib/Condensed/Module.lean:42` and its constructors take a fixed ring type, so they do not give the asserted internal module over `S ↦ C(S,R)`. `TopCat.toSheafCompHausLike` and `topCatToSheafCompHausLike` in `Mathlib/Condensed/TopComparison.lean` provide the underlying set-valued construction, not the tensor module action. These are useful building blocks for the next worker, not exact matches or one-line specializations of the complete new statement.

## Review by Q21

I read the chapter and unit records and the whole current `main-20261015` proof `sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`. Its first two sentences require precisely continuous field coordinates and their condensed module isomorphism. Both the item and the new node serve that place. The item is a descendant of `lem-sfb-subfield-flat`; the new node's `blueprint.from.via` is `[lem-sfb-condensed-subfield-basis]`. The unit and chapter route is unchanged.

For step 1 I opened the statements of `def-weil-l-adic-numbers` and `lem-sfb-finite-dimensional-linear-map-continuous`. The former gives completeness and the normalized absolute value; the latter applies to every linear map from a finite-dimensional Hausdorff topological vector space over a complete nontrivially valued field. I checked the scalar field is Q_ell, not an unproved-complete extension: |ell|=ell^{-1} is neither 0 nor 1, F/Q_ell is finite, both topologies come from the extended absolute value, and E-linear coordinates are Q_ell-linear. Thus the cited statement supplies exactly their continuity.

Step 2 has no non-elementary citation: continuity of beta is a finite sum of fixed multiplications composed with the continuous inclusion. Its two inverse equations are the basis reconstruction and Kronecker-delta coordinate identities; these remain fully written out rather than moved into an unnamed assertion.

For step 3 I read the complete new statement against every use. It supplies internal actions on C(-,F) and C(-,E^n), postcomposition maps for both continuous E-linear arrows, preservation of composites and identities, and the specific product and regular-module normalizations. These clauses give the asserted inverse maps with exactly the required formulas. The field action and product topology meet its hypotheses. The section maps are continuous by steps 1 and 2, and their E-linearity is ordinary basis linearity. No tensor-sheaf evaluation is silently identified with an objectwise tensor product.

For the new node I read `sk-def-sfb-condensed-ring`, `sk-def-sfb-sheaf-tensor`, `sk-def-sfb-module-objects` and `def-weil-pbc-sheafification` in full. They respectively specify the profinite site and scalar ring, the sheafified tensor with strong monoidality, the actual internal action diagrams and morphism equation, and unique factorization to sheaves. The new statement uses exactly these notions, introduces R and every module and family, and states the construction's properties without inserting proof steps. Its argument guide below retains every old sheaf argument for the future worker. For general topological M, the additional underlying sheaf assertion uses descent of continuous maps through the quotient map from the finite disjoint union of a profinite cover; this does not require M to be Hausdorff. A surjection from a compact space to a Hausdorff profinite target is quotient. Product sections are tuples with product topology, including the empty family.

I tested E=F and a non-unit one-element basis (rescaling by any nonzero b), arbitrary bases rather than integral bases, the empty profinite test set, and the one-point test set. The finite-extension basis cannot have length zero because F is a nonzero field, while the new general construction does allow the zero module and an empty product. It also allows the zero scalar ring with its only unital module. The inverse equations and section formulas are valid in these cases. Nothing asserts full faithfulness for arbitrary topological spaces, exactness of condensation, or sheafification preserving arbitrary sectionwise equalities without its universal property.

I checked delivery-errors B–E: the new node is self-contained, searched, source-located, statement-only and nonduplicate; its parent citations quote its statement rather than its future proof; dependencies have no cycle back to the item; no stronger field/topology hypothesis is used; all old arguments have a recorded destination. The three assembly steps are individually below 2000 characters and their total is 2095. No SGA source is used, and the report makes no independent-review claim.

## Argument retained for the new node's future worker

The new node generalizes old steps 3–5; it has no proof steps in its JSON. To prove it, first use quotient descent for profinite covers to glue continuous maps to M; operations glue pointwise and restrictions are precomposition. A compatible tuple glues by gluing each component, and a finite product of continuous maps is continuous. For each module, the pairing (a,h) ↦ (s ↦ a(s)h(s)) is biadditive and compatible with restrictions. The ordinary tensor universal property gives an objectwise tensor-presheaf map. Sheafification extends it uniquely to the action on the sheaf tensor. The equations 1h=h and (aa')h=a(a'h) give the unit and associativity diagrams on pure tensors; additivity and uniqueness, with the strong monoidal sheafification identifications, give those diagrams on the sheaf tensors. A continuous linear map f gives the additive natural map h ↦ f∘h because (f∘h)∘u=f∘(h∘u). Its equality f(ah)=af(h) on every pure tensor gives the internal module-morphism square by the same tensor and sheafification uniqueness. Identity, composite and sum formulas hold on each section. Coordinate projections and tuple formation are inverse natural linear maps, so they identify the continuous-function module of a finite product with the product internal module. For M=R the action is the specified multiplication of the condensed ring, hence the regular module. Applying this to both c and beta gives the exact old sheaf proof. These obligations are assertions of the new node; they are not left as hidden work in the parent assembly.

## Unfinished work

No part of this stage-1 repair is intentionally deferred except proving the new statement-only node, as the return explicitly requires. Delivery validation and push are recorded by the delivery command.
