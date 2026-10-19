# Stage-1 report: def-trf-trace-class

## Files written

- `dag/nodes/sec-trace-formula/def-trf-trace-class.json`: existing definition node, split; no new child nodes and no Mathlib leaves.
- `citations.json`: empty list, because a definition has no proof steps.

## Attachments

None. The declaration `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass` in `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Pairing.lean:387` was read. Its type is the later supported-pairing construction on a `Correspondence` and returns `G.borelMooreSections c.fixStr`; it does not state this item's Verdier composite
`A → RΓ(C, 𝓗_c(K)) → RΓ(F, ω_{F,A})` or its global-sections-adjunction identification. The declaration therefore is not an exact attachment. The source also has no declaration tagged `(blueprint: def-trf-trace-class)`.

## WANTED

None.

## What was checked and changed

The item was compared with `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-pairing/def-trf-trace-class.md` (order 2653), including its mate description, the composite through `𝔱_{c,K}`, the adjunction identification, and the dualizing complex. The older master copy and the `blueprint_update` were also read; the obsolete opening sentence pointing to `prop-trf-trace-class-unconditional` was removed because it is absent from the current blueprint. The direct conventions are now explicitly cited in the statement: `def-weil-finite-field-fiber`, `def-trf-coefficient-conventions`, `def-trf-correspondence`, and `def-weil-scheme-morphism-properties`; the fixed scheme, trace-class source, trace map, and dualizing-complex citations were already present. All of these are existing nodes, so the definition needs no newly split lemma or Mathlib search.

## Review by N6

I read the item source and current blueprint, then opened the source module `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Pairing.lean` around `traceClass` and `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Correspondence.lean` around `traceClassSource` and `mate`. I checked the cited DAG statements for `def-trf-fixed-scheme`, `def-trf-trace-class-source`, `lem-trf-trace-map-from-external-duality`, `def-trf-dualizing-complex`, `def-trf-coefficient-conventions`, `def-trf-correspondence`, `def-weil-finite-field-fiber`, and `def-weil-scheme-morphism-properties`. Each cited node supplies the corresponding object or convention used by the definition; no proof step uses any further fact. Since this is a definition, there are no proof steps to cite and `citations.json` is correctly empty. I tested the edge case of the empty correspondence support conceptually: the definition only forms the class after an admissible correspondence and its fixed scheme are supplied, so no extra existence assertion is hidden. I corrected the stale unconditional-pointer sentence and added the missing direct citations before marking the node `split`.

## Second reading by N6

- Item statement: read current `main-20261015/.../sk-d-pairing/def-trf-trace-class.md`, node `def-trf-trace-class`, order 2653, and its `blueprint_update`; the mate, two-arrow composite, target Hom group, and dualizing object agree. This is a blueprint definition, with no Stacks tag to verify.
- Proof steps: none (`proof=[]`); stage-1 §3(2) splits a definition by its statement dependencies. There is no disguised proof delegated to a new node; `citations.json=[]` remains exact.
- New nodes: none. B1–B7 and fresh Mathlib-leaf searches have no new node to apply to; the delivery creates zero Mathlib leaves. No searches are claimed to have run.
- `def-weil-finite-field-fiber`: checked the specified algebraic closure, prime-to-characteristic coefficient stage, and base `s`; PASS.
- `def-trf-coefficient-conventions`: checked finite level `A=O_E/(varpi_E^n)`, `n>=1`, and the constructible finite-Tor categories; PASS, no integral/rational-stage extension is asserted.
- `def-weil-scheme-morphism-properties`: opened the statement and its definition-node index; separated finite-type schemes are the properties used here; PASS.
- `def-trf-correspondence`: opened its statement and current update; checked separated finite-type `X,C`, `K in D^b_ctf(X,A)`, ordinary leg `c_2`, exceptional leg `c_1`, and admissibility; PASS after explicitly binding `X,C,K`.
- `def-trf-fixed-scheme`: checked `F=C x_(X x_s X) X`, projections `i_F,d`, and the same leg order; PASS. No reduced-intersection or pointwise fixed-set replacement is made.
- `def-trf-trace-class-source`: read the entire statement; its displayed tensor–internal-Hom isomorphism supplies precisely the sheaf mate `A_C -> H_c(K)`; PASS.
- `lem-trf-trace-map-from-external-duality`: read its statement and current source at `sk-d-trace-class/lem-trf-trace-map-from-external-duality.md`, order 2661; it supplies exactly `RΓ(C,H_c(K)) -> RΓ(F,omega_F)`, not a trace scalar; PASS. Also opened `def-trf-admissibility`: its constructible exceptional functors apply to all separated finite-type maps here, including the fixed-square maps and structure maps. No ambient FullCD hypothesis is used or added.
- `def-trf-dualizing-complex`: checked the separated finite-type domain and `omega_F=Ra_F^! A_s`; PASS. Since `X` is separated, `F` is the closed pullback of its diagonal inside `C`, hence again separated finite type.
- `def-weil-finite-tor-amplitude`: read its finite-level definition of `D^b_ctf`; PASS, now cited at the explicit binder for `K`.
- `def-weil-derived-pullback-tensor-hom`: read its finite-level statement defining constant coefficient objects and the ambient derived categories; PASS, now directly cited for `A_C,A_F`.
- `def-weil-ordinary-compact-cohomology`: read its definition `RΓ(T,M)=Fib_s(Ra_T* M)`; PASS, now cited for the ordinary global-sections notation rather than compact supports.
- `lem-pur-rhom-global-sections`: opened its statement for an arbitrary small ringed site; specialize `L=A_T`, use internal Hom from the tensor unit `RHom(A_T,M)=M`, and `Hom_D(A)(A,N)=H^0(N)` since `A` is free of rank one. This gives both global-sections identifications; PASS. These are unit-object identifications, with no duality or finiteness theorem hidden in them.
- Existing-node and attachment check: searched the whole DAG for “Verdier trace class”, “trace-class notation”, and “global-sections adjunction”; opened `sk-d-trace-class` and `lem-trf-trace-class-diagonal-pairing`. The former defines the diagonal pairing and the latter compares it with this construction, so neither replaces this definition. Read slopmaster2 `Correspondence.lean:263–279` and `Pairing.lean:379–409`: `traceClass` is the supported contraction tagged `sk-d-trace-class`; its agreement with the present Verdier composite is a separate comparison. The worker correctly declined an exact attachment.
- Edge cases: `K=0` or `u=0` gives the zero mate and zero composite; for `C` empty, `F` is empty and the unique class is zero. For `X=C=s` with identity legs and `K=A` in degree zero, the mate and adjunction are ordinary scalar maps and all displayed types agree. At `n=1` the coefficient ring is the residue field and the formula remains defined; `n=0` is excluded by the coefficient convention. No properness or nonempty fixed-locus condition is introduced.

Changes made by the second reader:

1. Updated `source.document` and `source.place` to the current snapshot and order 2653; the worker had updated the text but retained the old source location.
2. Made the separated finite-type schemes `X,C` and the finite-Tor constructible object `K` explicit, with an existing definition citation. **STATEMENT-DISPUTED (implicit binding):** the imported standalone text writes `Lc_2^*K` without introducing `K` or its category; as a standalone type expression it contains a free variable. The repaired binder is exactly the one in `def-trf-correspondence` and the current trace-class sketch, rather than a new hypothesis on that object.
3. Distinguished the sheaf map `tilde u:A_C -> H_c(K)` from its adjoint `widehat u:A -> RΓ(C,H_c(K))`; displaying the former as the latter without this identification conflates two Hom groups. Added the explicit adjunction isomorphism and existing-node citations for the constant objects, global sections, and derived-Hom identification. The defined class is the same composite.
4. Preserved the first worker's report, its `## Review by N6`, the correct construction, all existing dependencies, and the empty proof/citations. No new node, proof step, or Mathlib leaf was added.

Validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py N6 def-trf-trace-class --no-push .` printed `OK (not pushed) ... preflight passed` at dry-run commit `73662aee35`. All preflight checks ran through the delivery tool on the Weil server; no local DAG checker or compiler was run.
