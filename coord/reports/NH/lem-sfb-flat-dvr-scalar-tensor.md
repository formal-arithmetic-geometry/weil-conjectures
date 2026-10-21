# Stage-1 delivery: lem-sfb-flat-dvr-scalar-tensor

Group NH; 2026-10-21. One-level split, direct delivery. The mathematical statement is unchanged.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-dvr-scalar-tensor.json`: statement item, now split in six steps; not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for each node used by each numbered step.
- `searches.jsonl`: actual msearch.py queries and their recorded answers. The item's earlier Mathlib search records were retained, and the newly run queries were appended to the item.
- `report.md`: this report. `write_split.py` is sandbox-only scratch work.

No new DAG nodes and no new Mathlib leaves. No unit or chapter file is changed: this item is not the unit's key node.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, the item id, DVR tensor, scalar-model tensor and uniformizer/Tor terminology found no declaration stating every clause of the item. The matching DVR tensor files concern ramification or field extensions, not derived tensor of scalar module sheaves. The project declarations of auxiliary nodes are not an attachment of this item.

## WANTED

None. The blueprint and all Stacks sources used here are available locally.

## Corrections and source error

The imported item is true; its statement was preserved. Its source paragraph (2) says that tensor with a bounded finite free complex is locally a finite sum of shifts of the other factor. This inference is false: on the point site, take A=Z_ell, K=A[0] and M=[A --ell--> A] in degrees -1,0. Its only cohomology is A/ell in degree zero, whereas a finite direct sum of shifts of A has free cohomology. The item's existing source metadata already identifies this error and asks for the explicit DVR scalar-model calculation. This split supplies that calculation; it does not apply a splitting of finite free complexes.

The statement dependencies now also name the site, finite-presentation and sheaf-tensor notions occurring in the statement. The existing derived-tensor-descent dependency is retained because it supplies the derived tensor bifunctor meant there. No imported flags, pointers, provenance or blueprint metadata were removed.

## Mathlib and duplicate searches

The actual queries are in searches.jsonl and verbatim in the new mathlib_searches records. LeanFinder was tried both for the full flat sheaf-algebra assertion and, with a second phrasing, for the general PID cyclic quotient/free-resolution calculation. LeanSearch, Loogle and msearch grep were also run. All services answered. The second phrasing returned ordinary tensor-quotient identities; I read `TensorProduct.quotTensorEquivQuotSMul` and `tensorQuotEquivQuotSMul` in Mathlib/LinearAlgebra/TensorProduct/Quotient.lean:153-166. These concern ordinary modules and degree zero and do not prove derived Tor or the sheaf assertion. The flatness hits (including Module.Flat.iff_rTensor_exact, read at RingTheory/Flat/Basic.lean:393-397) are ordinary scalar-module exactness. They are ingredients, not a one-line specialization giving this item. Cotangent-module hits do not concern this assertion. The grep hits concern DVR factorization and normalized valuations.

Whole-DAG statement/title searches found the already existing rectangular Smith, exact constant realization, bounded-above flat K-flatness, K-flat localization and K-flat quasi-isomorphism lemmas used here. I also read the nearby scalar-model finite-flat-resolution and local-integral-perfect-model cohomology nodes: the former gives the length-one bound but does not itself identify all cohomology as scalar finite models; the latter assumes completed arithmetic coefficients on scheme sites, so cannot replace our arbitrary flat algebra over an arbitrary small site. Blueprint searches for `DVR tensor`, `flat DVR scalar`, `Smith`, `cyclic quotient` and `derived tensor scalar` found no blueprint node stating this item in another form. Thus blueprint.same_as remains empty.

## Not duplicates

No new node is introduced. Generic facts and scalar decomposition are reused or written as elementary steps, rather than creating nodes for the item's own clauses. In particular the existing `lem-sfb-dvr-matrix-smith-powers` is used to obtain the finite cyclic decomposition from a finite presentation; no new module-structure theorem is created.

## Review by NH

I read the item, the chapter record, the sk-lem-integral-models unit and its complete proof, and the source detail proof paragraph (2). The split realizes the finite scalar local-model tensor calculation used by the unit's tensor-product step; it changes neither the unit nor the chapter route. I read Stacks sites-modules.tex Tag 093J (lemma-constant-exact), Tag 03ER (definition-flat (3)) and the sheaf tensor definition in Section 03EK; sites-cohomology.tex Tag 06YQ (lemma-bounded-flat-K-flat), Tag 06YP (lemma-K-flat-quasi-isomorphism) and the construction before Tag 06YU (definition-derived-tor); and the DVR convention of algebra.tex Tag 00PD. The node's proof_origin is agent: the explicit scalar calculation is written here, rather than attributed to a theorem that the blueprint does not actually prove. There are no new-node sources to audit.

For step 1 I opened def-sc-finitely-presented-module and lem-sfb-dvr-matrix-smith-powers and read their statements. The former supplies the finite rectangular presentation; the latter supplies invertible changes of basis and the precise diagonal pi powers, including empty sizes and unit pivots. The cokernel is therefore the finite direct sum described in the step by coordinate quotient maps. The hypotheses needed are precisely a DVR domain and a generator of its maximal ideal, both present in the item. I do not cite the cancellation lemma or a continuous Smith theorem for a claim those statements do not make.

For step 2 I read the statement of lem-weil-pbc-finite-type-constant-exact: despite its title it applies to any small site and any commutative coefficient ring and explicitly preserves finite kernels and cokernels. The flatness citation is appropriate here because def-pc-flat-sheaf-modules literally defines flatness by exactness of tensor with that very sheaf; no inference from stalkwise flatness, scalar-ring flatness, or a different flatness convention is hidden. The R-action on the computed kernels and quotient cokernels is induced by the R-linear maps. The tensor definition gives the displayed unit and balanced maps. Composing the two exact functors proves all claimed preservation statements, with no points or sectionwise exactness of general sheaf sequences assumed.

For step 3 I read def-sc-discrete-valuation-ring: its nonzero maximal ideal and domain clauses make pi and its positive powers nonzero. This gives the explicit scalar short exact sequence by cancellation. Exact T from step 2 gives the asserted sheaf resolution even when R is zero or pi becomes a unit. The quotient augmentation is the actual scalar-extension quotient map. This step does not merely appeal to an unspecified finite free resolution: the map is explicitly pi^r.

For step 4 I opened lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-site-derived-tensor-descent, lem-pur-kflat-tensor-quasiiso-independent and def-pc-tensor-complex-sheaves. The first applies to the bounded complexes just constructed, whose finite free terms are flat since tensor is a finite coordinate sum of the identity. The second supplies the exact derived comparison for two K-flat, flat-term representatives. The third inverts the actual augmentation of C_Q while C_P is K-flat; the signed interchange supplies its stated second-factor orientation. The total-tensor definition gives the remaining two-term complex and its multiplication differential. The site is small in a sufficiently large common coefficient universe, so the essentially-small/coefficient-universe hypothesis in the quasi-isomorphism lemma is met. Neither Q_R nor its torsion summands are assumed flat. These statements, not merely the definitions of derived categories, supply the non-elementary derived-computation facts.

For step 5 the only external algebraic input is the domain clause of the DVR definition. I checked both explicit divisibilities: for r<s, pi^r a=pi^s b gives a=pi^(s-r)b, and pi^(s-r)b=pi^s c gives b=pi^r c. This proves both surjectivity onto the kernel and its stated kernel, without invoking an unquoted structure theorem. The scalar cokernel is the quotient by the sum of the two principal ideals, namely (pi^min(r,s)). When r>=s the differential is zero. Exact T then carries these scalar kernels and cokernels to the sheaf kernels and cokernels. No division by pi in R is used; the cancellation takes place only in A.

For step 6 I re-read the tensor and total-complex definitions. The finite coordinate balanced maps distribute the displayed representative into the computed pairwise blocks. Cohomology of a finite block diagonal differential is its coordinate kernel modulo coordinate image. Thus there is no extra assertion about arbitrary infinite sums. The scalar modules N are explicitly finite sums of copies of A and A/(pi^t), hence have the displayed finite block presentations; no unquoted Noetherian finiteness theorem is needed. This proves the whole finite-scalar-model clause as well as the explicit cyclic and free clauses, without creating a restatement node.

I checked r=s=1 (zero differential on R/pi, two nonzero possible cohomology sheaves), r=1,s=3 (kernel identified by multiplication by pi^2), r=3,s=1 (zero differential), P=0, Q=0, both modules free, a free/torsion pair and mixed finite sums. For R=A[1/pi] all torsion blocks vanish and the formulas still hold. For R=0 all assertions give zero. The proof works on a site without enough points because only sheaf exact functors, not point detection, are used. Flatness is essential: for the point site R=A/pi, the cyclic model P=Q=A/pi gives R tensor_R^L R=R[0], contradicting the asserted H^-1 formula without flatness. This confirms the exactness hypothesis has not silently been dropped.

I checked delivery-errors B through E against these files. There is no new-node proof, missing new-node definition, duplicate or relabelled clause (B and D). Every cited node's statement was opened and the exact part used is in citations.json (C4); every non-elementary step has its actual theorem citations (C1). All remaining quotient, coordinate and finite-presentation arguments are written out. No node created here can introduce a cycle; the server checks additionally validate the existing dependency route. The definition and derived theorem hypotheses were checked at the steps above (E1); all object and coefficient categories remain those of the original item (E4/E6). No SGA is used. Every proof step is below 2000 characters, so there is no long step concealing an additional lemma.

The off-unit generic tool statements are declared in split_report.tool_uses with the exact role of each. They are generic algebra/sheaf homological algebra inputs, not replacement routes for the geometric unit.

## Unfinished work

None in this one-level split. The proof dependencies that were already open remain the project's existing items; no Lean was written and no compiler, Lake or build tool was run.
