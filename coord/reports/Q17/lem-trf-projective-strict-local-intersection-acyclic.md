Files written:
- `dag/nodes/sec-trace-formula/lem-trf-projective-strict-local-intersection-acyclic.json` — statement, split proof, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-artin-tensor-etale-acyclic.json` — new unsplit statement node, no Mathlib match.
- `citations.json` — 10 verbatim statement citations.

Attachments:
- No Lean attachment found. The item has no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

WANTED:
- Local copy of Hübner–Schmidt, *The tame site of a scheme*, for Definition 7.8, Proposition 7.9 and Theorem 7.10; the online PDF was read at the cited pages.
- Local copy of Orgogozo, *Modifications et cycles proches sur une base générale*, Proposition 2.3, proof, for the common-affine specialization; the online author PDF was not needed for the final three-step argument beyond the source pointer.

## Not duplicates

- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-strictly-henselian-etale-acyclic`: the new node concerns tensor products of two ind-etale algebras over a common ring and their resulting scheme; the existing node concerns one strictly henselian local ring and its own etale cohomology.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-pd-projective-finite-affine-neighbourhood`: the new node is an etale-cohomological tensor theorem; the existing node only supplies an affine open containing finitely many projective points.
- `lem-trf-projective-strict-local-intersection-acyclic` vs `lem-trf-artin-tensor-etale-acyclic`: the item is the geometric projective strict-localization intersection; the new node is the general affine algebra tensor input used to prove it.

- `lem-trf-artin-tensor-etale-acyclic` vs `def-weil-pbc-strict-henselization-restriction`: tensor-product acyclicity of two ind-etale algebras versus the definition of restriction from a higher-direct-image stalk.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-source-cocycle-exact-restriction`: a geometric tensor-product theorem versus exact restriction of source cocycles.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-strict-local-germ-restriction-iso`: etale cohomology vanishing for a tensor product versus an isomorphism on strict-local germs.
- `lem-trf-artin-tensor-etale-acyclic` vs `def-weil-pbc-derived-global-germ`: tensor acyclicity versus a definition of derived global germs.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-abelian-stalk-exchange-localization`: tensor-product etale acyclicity versus an abelian stalk/exchange localization statement.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-abelian-strictly-henselian-open-germ`: tensor-product acyclicity versus comparison of an open germ on a strictly henselian base.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-derived-global-germ-exchange`: tensor-product cohomology vanishing versus derived global-germ exchange.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-finite-stalk-formula-restriction`: arbitrary torsion-sheaf acyclicity on a tensor product versus a finite-stalk restriction formula.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite`: tensor-product etale acyclicity versus finiteness of a finite pushforward stalk fibre.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective`: tensor-product etale acyclicity versus bijectivity of a finite pushforward stalk map.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-sets-finite-pushforward-stalk`: tensor-product etale acyclicity versus a finite pushforward stalk identification.
- `lem-trf-artin-tensor-etale-acyclic` vs `lem-weil-pbc-sets-strictly-henselian-open-sections-stalk`: tensor-product acyclicity versus open sections/stalk comparison for sheaves of sets.

## Review by Q17

I checked the imported item against its statement and source pointer, and searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its geometric terminology, and a blueprint tag; no finished declaration exists. I read the current statements of every cited node. Step 1 uses the projective-morphism definition and the existing finite-projective-set affine-neighbourhood theorem; the latter supplies an affine open containing both geometric points, and I declared it as a generic tool because the trace-formula unit has no replacement. Step 2 uses strict-localization invariance under the open immersion, the strict-henselization affine-chart ind-etale theorem, functoriality (including strict henselian locality), and the existing theorem that a strictly henselian local scheme has vanishing higher etale cohomology. Step 3 uses the fibre-product definition and the new Artin tensor-acyclicity statement to identify the fibre product with `Spec (B_x ⊗_R B_u)` and conclude for every torsion sheaf. I verified that the empty tensor product gives the empty scheme and that the argument does not impose a bound on connected components. The new node is exactly Hübner–Schmidt Definition 7.8, Proposition 7.9 and Theorem 7.10 combined with Stacks Tag 03QO; it is strictly more general than the projective item and is not a restatement. All proof uses are present in `proof_deps`, and every citation quote is copied verbatim from the cited node statement. The item and new node have current blueprint ancestry and the required Mathlib searches; none matched.

## Source error

None found. The imported statement's empty/infinitely-many-component clauses agree with the cited tensor theorem's unrestricted formulation.

What could not be finished: the new Artin tensor node remains unsplit by design for the next stage; no Lean source or compiler was used, per the stage-1 restriction.
