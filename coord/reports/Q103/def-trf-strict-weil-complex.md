# Stage-1 worker report: def-trf-strict-weil-complex

## Files written

- `dag/nodes/sec-six-functors/def-trf-strict-weil-complex.json`: marked the imported definition `split`, updated its statement to the current main-20261015 `blueprint_update`, retained all seven existing statement dependencies, and added the split report; no new nodes or Mathlib leaves.
- `dag/units/sk-def-sf-weil-complexes.json`: recorded the item's realized unit statement (the unit has no proof steps).
- `citations.json`: empty, because a definition has no proof steps.

## Attachments

None. I searched the project source for `(blueprint: def-trf-strict-weil-complex)`, `StrictWeilComplex`, and the proposed fully qualified names. The prior worker's candidate attachment was refused by the delivery server; following the brief, I did not answer ATTACH and treated the item as a DAG definition split.

## WANTED

None. The current blueprint definition and all seven cited definitions are available in the repository. No Mathlib leaf is involved: the strict Weil category is a project notion built from the cited project interfaces.

## Source and DAG audit

I read the item's imported node, the current main-20261015 blueprint file `sec-smooth-purity/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md` (order 2509), its older master counterpart, the `sk-def-sf-weil-complexes` unit and `sec-six-functors` chapter records, and the project source file `WeilConjectures/SixFunctors/ProEtale/Derived/WeilComplex.lean`. I searched the whole DAG and blueprint for strict-Weil-complex duplicates and for each dependency's key terms. The current blueprint_update differs from the imported statement: it moves the Hom-group/Jordan-block sentence into its own paragraph and removes the older closing sentence “Only traces, stalk Frobenius maps, weights of cohomology sheaves, equivariant maps and functorial triangles are used.” I followed the current update exactly; this is recorded in the item split report rather than silently retaining stale text.

The seven existing statement dependencies are sufficient and are not duplicates of the item. `def-trf-coefficient-conventions` supplies the finite ring `A=A_{E,n}`, separated finite-type `X₀`, geometric fibre `X`, and `D^b_{ctf}(X,A)`. `def-trf-scheme-frobenius` supplies `g_γ=g_X` and identifies it as geometric Frobenius. `def-weil-derived-pullback-tensor-hom` supplies the derived pullback `Lg_γ^*`. `def-weil-finite-field-fiber` supplies the global finite-field datum and base-change notation. `def-weil-pbc-proetale-site` supplies the small pro-etale site and its derived module category. `def-weil-scheme-morphism-properties` supplies the separated/finite-type scheme conventions. `def-weil-weil-sheaf-complex` supplies the comparison category `D^b_{c,W}` used in the non-triangulated/non-Ext warning. The pair, commuting-morphism condition, category notation, and forgetful functor are the definition's own elementary construction from these interfaces, so no additional node is warranted.

## Review by Q103

I checked the statement clause by clause against the current blueprint: `A=A_{E,n}`, the separated finite-type `X₀/k₀`, `X=X₀×_{k₀}k`, the small pro-etale setting, `K∈D^b_{ctf}(X,A)`, an isomorphism `Lg_γ^*K≅K`, the geometric-Frobenius identification, commuting morphisms, the resulting category and forgetful functor, and the distinction from `D^b_{c,W}` together with the Jordan-block warning. Every cited dependency says the corresponding object or operation listed above; none is being used for a theorem absent from its statement. Since this is a definition, there are no proof steps and hence no citation entries.

I checked edge cases at the level of the definition: the zero complex and the constant coefficient complex admit the required pair data whenever an isomorphism is chosen; taking `X₀=Spec(k₀)` specializes the construction to a point without changing the typing of `Lg_γ^*`; and the Jordan-block clause is explicitly a warning about the pair category rather than an added hypothesis. The statement introduces no extra smoothness, properness, or coefficient-field assumptions beyond the cited convention node. The unit's realized statement now points to this item, with no unit proof steps.

No new node was created, so there are no duplicate pairs to report and no Mathlib search records to add. The item is not a Mathlib declaration: it is a project-specific category of pairs whose ingredients are the cited project definitions.

## What was wrong in the imported node

The imported node was still `status: imported`, had `blueprint.same_as: null`, and used the stale master wording despite carrying a main-20261015 `blueprint_update`. I changed only those stage-1 fields required for a split, followed the current statement, and recorded the unit realization. The prior Lean attachment proposal is not reused because the server explicitly refused it.

## What I could not finish

Nothing remains for this stage-1 split. A second worker should rerun the required server dry run and deliver the accepted sandbox.

## Second reading by Q103

- Item `def-trf-strict-weil-complex`: checked the complete statement against current `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sf-weil-complexes/def-trf-strict-weil-complex.md` (order 2509), the current unit `_section.md` (order 1837), the older master definition (order 2165), and `WeilConjectures/SixFunctors/ProEtale/Derived/WeilComplex.lean`, lines 95–198 and 209–237; the finite ring, geometric fibre, geometric rather than arithmetic Frobenius, bounded constructible finite-Tor underlying complex, invertible structure, commuting morphisms and forgetful functor agree. The obsolete description of the comparison category required the correction below.
- Proof steps: none (`kind: definition`, `proof: []`, `proof_deps: []`), matching the source definition; there is no non-elementary proof concealed in a new node and no per-step citation to quote. `citations.json` remains exactly `[]`.
- New nodes: none; B1–B7 and new-node Mathlib searches have no instances in this delivery. No searches that were not run have been recorded.
- Dependency `def-trf-coefficient-conventions`: read its statement; it fixes the nonzero finite ring `A=O_E/varpi_E^n`, `ell != p`, `n >= 1`, the separated finite-type scheme, the small pro-etale site, and cites the definitions of `D^b_c` and `D^b_ctf`; sufficient. Also opened `def-weil-finite-torsion-constructibility` and `def-weil-finite-tor-amplitude`: finite Tor amplitude is an additional condition at finite coefficients, and the underlying subcategory is full.
- Dependency `def-trf-scheme-frobenius`: read its statement; `gamma=(z -> z^q)^(-1)` and `g_gamma=id x Spec(gamma)` are the geometric Galois automorphism. No relative power-Frobenius preservation result is required; sufficient.
- Dependency `def-weil-derived-pullback-tensor-hom`: read its full finite-level clause; derived pullback is defined on the ambient derived module category. The pair is defined with its isomorphism in that ambient category, so no uncited preservation theorem is needed to type it; sufficient.
- Dependency `def-weil-finite-field-fiber`: read its statement; supplies `p,a,q,k_0,k`, `a >= 1`, the algebraic closure, geometric base change and `n >= 1`; sufficient.
- Dependency `def-weil-pbc-proetale-site`: read its statement; supplies the small site, constant ring sheaf, module-sheaf category and derived category; sufficient.
- Dependency `def-weil-scheme-morphism-properties`: read its statement; this is a collection of references, not a fresh definition. Its finite-type and separated entries point to `def-weil-finite-type-morphism` and `def-weil-proper-morphism`; no geometric theorem is taken from this collection.
- Dependency `def-weil-weil-sheaf-complex`: read all four clauses and the final paragraph; it defines rational-coefficient fixed pairs, explicitly denies that it is a derived category of Weil sheaves, and puts the Jordan-block illustration on `Spec(k_0)`. The first reader's description of it as a derived comparison category is superseded by the correction below.
- Unit realization: checked the sandbox unit against the repository unit and master `_section.md`; only `realized.statement=[def-trf-strict-weil-complex]` and `realized_by` were supplied, with no unit proof steps and no change to the unit's fixed statement or route. The current smooth-purity unit has a more general coefficient convention and additional twists/duals; this delivery does not claim to realize those added clauses.
- Duplicate audit: searched the whole `dag/nodes` tree for `strict Weil`, `category of pairs over`, and `endofunctor-fixed-pair`; opened `sk-def-sf-weil-complexes`, `def-wf-weil-category`, and `def-weil-endofunctor-fixed-pair-category`. The current blueprint node `sk-def-sf-weil-complexes` gives the same pair notion with general admissible coefficients, now recorded in `blueprint.same_as`. The other two nodes respectively treat rational stages/filtered scalar extension and an arbitrary endofunctor; neither is a new finite-coefficient result to create. The existing named finite-coefficient item remains, and no duplicate child was introduced.

### Source error

STATEMENT-DISPUTED: the imported sentence calls `D^b_{c,W}` of `def-weil-weil-sheaf-complex` a triangulated (derived) category of Weil sheaves. This is a definition mismatch: clause 1 of that cited node defines it as `D^b_c(Y,Lambda)^{Lg_Y^*}`, and its last paragraph explicitly says it is a category of pairs, not a derived category. The current blueprint's general Weil-structure unit says the same. I repaired the comparison to say that both notations are categories of pairs and that this definition supplies no triangulated structure or derived-category identification. This changes no objects, Weil isomorphisms, morphisms, or coefficient hypotheses.

The point example was checked explicitly, including the finite-ring case rather than only a coefficient field. For `X_0=Spec(k_0)` and every permitted `n >= 1`, the Jordan matrix `J(x,y)=(x+y,y)` on `A^2` is invertible. The first-coordinate copy of `A` and the second-coordinate quotient both have identity Frobenius. An equivariant section of the quotient would send `1` to `(c,1)` and would require `(c+1,1)=(c,1)`, impossible since `A` is nonzero. Thus the Weil-sheaf extension is nonsplit. On `Spec(k)`, sections of pro-etale module sheaves are exact by the existing `lem-weil-point-proetale-sections-exact` (whose full statement I opened); since `Hom_{A_X}(A_X,F)=Gamma(X,F)`, the coefficient sheaf is projective and its derived `Hom(A,A[1])` vanishes. A commuting pair morphism is an underlying derived morphism, so it too vanishes. This verifies the illustration without creating a node for a few-line consequence. I also opened Stacks `proetale.tex`, labels `lemma-w-local-strictly-henselian-extremally-disconnected` and `lemma-w-contractible-is-weakly-contractible` (0982 and 098H, the sources of the exact-sections node): for an algebraically closed field the spectrum is a point with strictly henselian local ring, giving the required contractibility. The rational comparison node and the source Lean independently locate exactly this example on the point. I made that location and the canonical structures explicit; I did not assert vanishing for a general scheme.

For the rest of the edge-case audit, the zero complex has its unique structure isomorphism, and on the empty scheme the underlying category is the zero category, so the pair construction is well-typed and introduces no non-emptiness hypothesis. At `n=1` the coefficient ring is the residue field and the Jordan check still applies; `n=0` is excluded by the cited coefficient conventions. The pair category and forgetful functor use only elementary functoriality: if `u phi_K=phi_L P(u)` and `v phi_L=phi_M P(v)`, then `(vu) phi_K=phi_M P(v)P(u)=phi_M P(vu)`, and identities satisfy the equation because `P(id)=id`. Forgetting a composite or identity gives the original composite or identity. No choice of cones or triangulated structure on pairs is involved.

Changes made in the second reading:

1. Corrected the obsolete derived-category comparison, with the explicit definition mismatch above, following the current blueprint's intent and the cited node's actual statement.
2. Qualified the Jordan-block illustration by `X_0=Spec(k_0)` and the canonical structures, so it cannot be misread as global vanishing on every `X`.
3. Recorded the current blueprint's matching general definition in `blueprint.same_as` and explained its scope in `split_report`.
4. Appended this independent reading, preserving every first-worker section, including `## Review by Q103`. The source field remains historical maintainer-owned metadata; the current source path and exact order are identified above and in `split_report`.

Validation: the required server dry run `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q103 def-trf-strict-weil-complex --no-push .` printed `OK (not pushed) deliver/Q103/def-trf-strict-weil-complex at 58c1d6c22f: preflight passed`. No validation repair was required. All edits are confined to this item's sandbox; no Lean, compiler or local preflight/checker was run.
