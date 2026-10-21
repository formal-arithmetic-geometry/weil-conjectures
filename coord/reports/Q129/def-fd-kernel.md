## Worker report

Files written:

- `dag/nodes/sec-fourier-transform/def-fd-kernel.json`: existing definition, now split into its existing statement dependencies; not a Mathlib leaf.
- `dag/units/sk-def-kernel.json`: only `realized` and `realized_by`, binding the definition to the unit statement; there are no unit proof steps.
- `citations.json`: `[]`, since the item is a definition with no proof steps.
- `report.md`: this report and the signed self-review.

New nodes: 0. New Mathlib leaves: 0. No earlier item copy, split, report or citations were present in the sandbox. The search results written by this attempt are preserved in `searches.jsonl` and recorded verbatim by tool and query in the item's `mathlib_searches`.

Attachments: none. In particular, this delivery does not renew the rejected attachment.

WANTED: none.

## Statement corrected

The imported `statement` still described the old adic vector-bundle kernel and integrand. I replaced it with the general-coefficient kernel of the item's `blueprint_update.statement`, checked against `literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-kernel/def-fd-kernel.md` and the unit `_section.md` (orders 3035 and 3034). No target statement or chapter/unit route is changed. The old `source`, title, Lean metadata, import fields and entire `blueprint_update` are preserved, as required by field ownership; the actual current source is named here and in `split_report.blueprint`.

The data are an arbitrary commutative coefficient ring Lambda with p invertible, arbitrary scheme morphisms V -> S and V' -> S, p=0 in the global sections of W=V x_S V', an arbitrary function b and a possibly trivial character F_p -> Lambda^units. The object is a discrete Lambda-module sheaf on W's small etale site. There is no adic category or derived integrand in the new source, so `def-weil-pbc-qbar-category` is removed. The illustrative vector-bundle case is retained. I wrote its dual-frame formula and the affine-line product explicitly.

The canonical F_p structure and function morphism are now explicit: factor Z -> Gamma(W,O_W) through Z/p, then use the affine-target correspondence on F_p and F_p[t], sending t to b. This does not impose CharP or nonemptiness. The existing Mathlib leaf `lem-a1-locally-ringed-space-affine-adjunction` supplies the correspondence, so no new lemma is introduced.

The meaning of `def-fd-artin-schreier-sheaf` here is explicitly its current main-20261015 general-coefficient definition, not the obsolete Qbar statement still present in that node's imported main field. I read both the node's `blueprint_update` and its current blueprint source. That source defines L_{Psi,f}=f^* L_Psi for every k-scheme X, not just nonempty ones. No assertion about the characteristic of a nonzero global-section ring is used.

## Lean audit and Mathlib searches

Read `lean/WeilConjectures/FourierTransform/Defs.lean` at the blueprint tag and definition, lines 136-158, and `ArtinSchreier.lean`, lines 464-516. `AlgebraicGeometry.Etale.fourierKernel` at Defs.lean:154 requires `[CharP Gamma(W,top) p]`; `artinSchreierSheafZMod` at ArtinSchreier.lean:512 has the same restriction. On the empty scheme the global-section ring is the zero ring, whose characteristic is 1; a prime p is not 1, although p=0 holds there. Thus neither declaration states the item on its full domain. The lower-level `artinSchreierSheafOf` at line 469 accepts any scheme with the specified field structure and explains how the desired construction works, but it is not the Fourier-kernel declaration and is not offered as an attachment. No compiler was run.

All six queries were run through the mandated `msearch.py Q129 def-fd-kernel` command and the hits were read:

- LeanFinder: `Fourier kernel on the small etale site defined as pullback of the Artin Schreier sheaf along a global function`.
- Loogle: `"artinSchreier"`.
- grep: `fourierKernel|artinSchreierSheaf|Fourier.Deligne`.
- LeanSearch: `Artin Schreier sheaf of an additive character pulled back along a pairing of schemes`.
- grep in AlgebraicGeometry: `Artin.Schreier|artin[Ss]chreier|exponential[Ss]heaf`.
- LeanFinder, second phrasing: `Isotypic component of pushforward along x to x to the p minus x over a finite field defining an exponential etale sheaf`.

Both greps and Loogle returned zero hits. The first semantic search returned small etale topology, etale categories and general/structure-sheaf pullback constructions. LeanSearch returned Scheme.Modules pullbacks, their adjunction/composition, and ordinary scheme pullbacks. The second semantic phrasing returned standard-etale ring presentations, an etale-locus theorem and BDeRham. These are not the Artin–Schreier sheaf or its Fourier kernel. None is an exact match or one-line specialization for the whole definition. All services answered successfully; none was recorded as unavailable.

Whole-DAG and blueprint searches used `blueprint_refs.py ancestor def-fd-kernel` and searches for `Fourier kernel`, `kernel and integrand`, `global function`, and `functions as morphisms`, together with whole-DAG text/filename searches for global functions, affine-target adjunction, inverse image, fibre products, affine space and vector bundles. `sk-def-kernel` states the same definition at unit level and is recorded in `blueprint.same_as`. `def-fd-transform` only uses the kernel and defines another object. No helper node is needed; no duplicate is created.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The already-existing affine-target adjunction leaf is reused rather than recreated. The kernel remains the canonical item `def-fd-kernel`; its unit-level counterpart `sk-def-kernel` is only a `same_as` reference, not a dependency that could cycle.

## Review by Q129

I read the current kernel node and unit source in main-20261015, the chapter overview, the imported unit/chapter records, and the current Artin–Schreier definition at `sec-fourier-transform/sk-def-as/def-fd-artin-schreier-sheaf.md`. The latter explicitly allows an arbitrary commutative Lambda with q invertible, has e_Psi=(1/q) sum Psi(-a) sigma_a, and defines the function sheaf by pullback. Taking k=F_p gives q=p and exactly the coefficient hypothesis of the kernel. No nontriviality, finite coefficient ring, finite-type condition on the general W, or adic interpretation is introduced.

This item is a definition. Its `proof`, `proof_deps` and `proof_origin` are empty/null, as the source has no proof. There is therefore no numbered proof step whose citation could hide a lemma, and no step longer than 2000 characters. The dependency audit, clause by clause, is as follows:

- `def-pc-fibre-product`: I opened its statement. It defines X x_S Y for every pair of scheme morphisms, not merely affine or nonempty schemes, and supplies the projections and universal property needed to name W.
- `def-weil-pbc-scheme-conventions`: I opened its statement. It points to actual definitions of schemes, separatedness and finite type; it imposes no universal finite-type restriction. These conventions are used for the scheme data and the final application only.
- `lem-a1-locally-ringed-space-affine-adjunction`: I opened its statement and checked Stacks Tag 01I1, `schemes.tex`, label `lemma-morphism-into-affine`, lines 840-855 and the construction beginning at line 857. The statement gives the bijection for any locally ringed space Z and any commutative ring R, natural in both, including the map Z -> Spec Gamma(Z). Applying it first to R=F_p and then to R=F_p[t] constructs precisely the structure map and b morphism. Factoring through Z/p and evaluating a polynomial at b are elementary ring constructions; no new node is justified for them. The two ring maps commute with constants, so the function map is over F_p by the same bijection.
- `def-sbc-affine-space`: I opened its statement. Its affine-base description is Spec(R[x_1,...,x_n]); n=1 and R=F_p give exactly the target Spec(F_p[t]). I did not use smoothness or any dimension theorem from this definition.
- `def-fd-artin-schreier-sheaf`: I opened its node and current source. The displayed L_{Psi,f}=f^*L_Psi is exactly what defines the kernel for f=b. Equality of the two names is definitional, so no finite-etale base-change theorem is smuggled into the definition. The general coefficient form is explicitly identified to avoid taking a claim from its obsolete imported statement.
- `def-weil-pbc-etale-site`: I opened its statement. The objects, morphisms and jointly surjective covers define W_et for any scheme W; no scheme finiteness or nonemptiness is needed.
- `def-weil-pbc-inverse-image`: I opened its statement, including its last sentence on fixed-coefficient module sheaves. That is the underived inverse image used in b^*; the kernel definition uses no derived tensor or six-functor compactification assertion.
- `def-fourier-set`: I opened its statement and current blueprint source at `sk-def-fourier-set/def-fourier-set.md`, order 3014. Its opening sentence supplies the prime p, power q=p^a and field k_0=F_q explicitly used in the vector-bundle application. No derived-category conclusion or adic/discrete comparison is taken from it. This realizes the unit edge sk-def-kernel -> sk-def-fourier-set; the arbitrary-Lambda construction before the example is unchanged.
- `def-asd-vector-bundle-zero-section`: I opened its statement and its current blueprint update. It gives the locally free finite-rank vector-bundle convention and frames. The finite-type field-base application is within its Noetherian setting. The dual bundle in the application is described by inverse-transpose changes in these frames; the scalar sum x_i xi_i is unchanged because (Ax)^T(A^{-T}xi)=x^Txi. This is a two-line matrix identity, not a new substantive lemma or an assertion about a general pairing being bilinear. The general b remains arbitrary.

Small cases checked explicitly: W empty (unique ring maps F_p -> 0 and F_p[t] -> 0, hence unique function morphism and its sheaf inverse image); disjoint V and V' over S, giving just that empty case; rank r=0 (empty coordinate sum b=0, still the same pullback definition); Lambda the zero ring (p is a unit since 0=1, and the only module sheaf is zero); trivial Psi (the Artin–Schreier image construction is still defined); arbitrary b not bilinear (no use of bilinearity outside the vector-bundle example); and p=2 (the same definitions and character formulas apply). The failure of CharP on the empty scheme is an error in the proposed attachment domain, not a reason to strengthen the mathematical item.

I checked delivery-errors B–E against this definition: all objects are introduced, TeX has single logical escapes, all substantive construction dependencies already exist and have been read, no statement-only new node has an illicit proof, no theorem is relabelled as a helper, and no cycle is introduced through a counterpart or citer. All imported metadata are retained. I corrected the stale coefficient setting, removed the obsolete integrand/qbar dependency, added the missing direct construction dependencies, and made the empty-case structure-map construction explicit. No SGA source is used.

Nothing remains mathematically unfinished for this one-level definition split. Subsequent proof work or generalization of the upstream CharP interface is outside stage 1.

## Dry-run repair

The first full dry run returned exactly one finding: `units: sk-def-kernel cites sk-def-fourier-set, which its nodes do not reach`. I read that unit and the current source of `def-fourier-set` and made the final example explicitly use its finite-field data q=p^a and k_0=F_q. The new dependency therefore supplies data actually named in the application. It imposes no adic assumptions on the general kernel and makes no comparison of the two coefficient categories. The earlier isolated server review_split check had already passed with zero new nodes. The required full dry run is rerun after this repair.
