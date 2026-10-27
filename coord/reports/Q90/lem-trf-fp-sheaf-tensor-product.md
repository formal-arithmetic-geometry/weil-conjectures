# Stage-1 report: lem-trf-fp-sheaf-tensor-product

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fp-sheaf-tensor-product.json`: item split in four steps; unchanged statement and statement dependencies; no Mathlib match for the sheaf theorem.
- `citations.json`: nine entries, one per cited node per step, checked as literal substrings of the current node statements.
- `report.md`: this report. No new nodes, no new Mathlib leaves, no unit or chapter changes. `searches.jsonl` is the search command's own record; `write_split.py` is sandbox-only preparation code.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the blueprint id and finite-presentation/tensor terminology. `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj`, in `AlgebraicGeometry/Modules/ProjectionFormula.lean:170`, requires its second factor to be invertible, while this item assumes only finite presentation of both factors. It cannot attach this item. The tensor-pullback theorems and ordinary module scalar-extension results also have different statements.

## WANTED

None. All sources used are present in the read-only literature tree.

## Corrections and search findings

The item was unsplit, with no proof. Its statement is correct and remains unchanged. I read Stacks Tag 01CE, `modules-lemma-tensor-product-permanence`, especially its displayed two-presentation complex. Clause (4)'s final sentence omits details; the split supplies the finite free basis identifications and the two-lift kernel chase. This follows that source's route without creating a helper which just repeats the item. Tensoring need only be right exact, so no flatness or Noetherian hypothesis is added.

The source tools `tools/blueprint_refs.py search` were run on “01CE”, “01CC”, “tensor finitely presented”, “finite presentation tensor”, and “tensor product”, across the whole imported blueprint. The exact conceptual searches had no matches; the broad search produced unrelated tensor, coefficient and representation results. The live DAG was searched for Tag 01CE, its label, exactness and tensor/presentation keywords. The existing finite-presentation tensor item, its parent, and the invertible/quasi-coherent/affine tensor variants do not furnish a proof of this item. The generic tools needed for the actual argument already exist. The ancestor command identifies `lem-trf-local-term-locality`; the item's precise inherited `blueprint.from.place` and `via` chain are retained and `same_as` is the searched empty list. I read the current `literature/blueprint/latest/` unit and ancestor proof (snapshot 7284bb09daf97437d544c51882b325f9c52cd345). This is a commutative-algebra tool below the recorded fibrewise ampleness argument, not a replacement of the unit route.

I used only the mandated `msearch.py` for Mathlib searches, including LeanSearch, Loogle, grep in `Algebra/Category/ModuleCat/Sheaf`, and two distinct LeanFinder phrasings. I read the returned hits: `SheafOfModules.IsFinitePresentation` is the local presentation predicate, and `presentationOfIsCokernelFree` constructs data from an already supplied cokernel. Neither proves the tensor exact sequence. `instFinitePresentationTensorProduct` is ordinary module scalar extension, and `Module.Finite.tensorProduct` asserts finite generation. I inspected `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:236–269` and the project's local finite-presentation API. The existing searches on the copied item are retained; new queries actually run by Q90 and their results are appended. No service returned unavailable in this run.

## Not duplicates

No nodes created. All generic facts are citations of existing nodes; the short coordinate computation and kernel chase are explicit proof steps, not separate nodes. In particular I did not create a second tensor-right-exactness node, a new finite-free-tensor node, or a new “tensor finite presentations” node restating the item.

## Review by Q90

I checked delivery-errors B–E against the source and every cited statement, not just their titles. The item is self-contained: it introduces X, both modules, and the exact local finite-presentation condition, and its original three definition dependencies cover schemes, module sheaves and the tensor construction. There are no new statements whose hypotheses or definitions require auditing, and no new Mathlib leaf with a declaration/line obligation. The JSON uses ordinary TeX escaping and retains all original metadata.

For step 1 I read `lem-weil-pbc-module-restriction-open-immersion-colimits`: its statement gives the actual sectionwise restriction and the restriction of maps. Hence restricting again to the intersection does not change a stalk at any point of the intersection. I read clause (5) of `lem-weil-pbc-module-stalk-exact`: it gives exactly the equivalence between sheaf exactness and stalk exactness needed for both restricted presentations. Common-neighbourhood restriction is an elementary consequence of the stated restriction formula; I do not assume intersections of affine opens are affine, since no affine opens are needed.

For step 2 I read `def-pur-sheaf-tensor-product` and the full statement of `lem-pc-sites-sheaf-tensor-bilinear-universal`. The latter explicitly represents sectionwise bilinear sheaf maps, rather than merely defining a tensor object. It therefore constructs the displayed maps and the finite-free coordinate maps. The inverse basis map and the two composites are written out, so distributivity or finite-free tensor permanence is not silently taken from a definition. Both maps commute with restrictions because their coefficients use only multiplication, addition and the canonical basis. The sum has rank ms+nr and the middle term rank ns, with every rank finite.

For step 3 I read `lem-weil-pbc-module-stalk-tensor`: its statement provides the natural tensor-stalk comparison and its formula on germs, which identifies the actual maps, not only the objects. I reread all five clauses of `lem-weil-pbc-module-stalk-exact`: the fifth supplies exactness of the input stalk sequences and the kernel/cokernel clauses agree with the use of surjections. I read `lem-weil-pbc-tensor-right-exact`: it states preservation of an exact sequence ending in zero, including surjectivity and either tensor order, for arbitrary modules over a commutative ring. These are exactly the three applications at the commutative stalk ring. The two lifts in the kernel calculation are explicitly given in the order permitted by those surjections; I never lift a sheaf section globally through an epimorphism. Equality after subtracting the lifted second-factor relation is the precise first-factor kernel condition. Finite sums and their stalks are handled by one common neighbourhood for finitely many coordinates. Thus the calculation does not hide an extra generic comparison lemma or require flatness.

For step 4 I checked that clause (5) of the exactness node applies twice: at the middle term and at the last term followed by zero. The statement of `lem-weil-pbc-module-restriction-tensor-comparison` explicitly gives the open restriction isomorphism, so the constructed local presentation has the last term the item asks for. No derived, etale or coefficient-category tensor is substituted for the Zariski sheaf tensor. All cited sheaf tools are Lean-closed, and the ordinary module right-exactness node is already a Mathlib leaf, so there is no off-unit unfinished tool to declare. None of these nodes depends on the item.

I tested zero ranks and zero factors: the empty-basis maps still work, and the same sequence presents the zero tensor. The empty scheme satisfies the local condition vacuously. Over a non-flat example such as F=G=Z/2 on Spec Z, the argument uses right exactness only and gives two copies of the same relation in a valid finite presentation. Non-Noetherian schemes and modules with non-finitely-generated higher syzygies cause no issue: only the two given relation maps occur. No statement dispute or source correction is needed. Every step is under 2000 characters (596, 817, 1263, 651), and the only new computation is the routine source-prescribed tensor-presentation argument, not a relabelled clause of the item.

## Unfinished work

No mathematical part remains in this one-level split. New unsplit nodes: zero. The required remote dry run and final push are the remaining delivery actions.
