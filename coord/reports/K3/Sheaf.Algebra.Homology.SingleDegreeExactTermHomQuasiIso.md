## What changed

Proved `CategoryTheory.quasiIso_homComplex_map_of_single_degree_exact_term` in
`Sheaf.Algebra.Homology.SingleDegreeExactTermHomQuasiIso`, with its signature and
existing docstring unchanged. Added four proof-only imports: Mathlib's exact-functor
criterion and preservation of zero objects, the library's proved Hom-complex projection
interface, and the proved presheaf internal-Hom additivity/zero-precomposition lemmas.
Two proved private helpers establish covariant internal-Hom additivity and invertibility
of a limit-fan projection when all other factors are zero.

The proof constructs the projection inverses, checks differential compatibility and
naturality, then transports the exact functor's preservation of three-term
quasi-isomorphisms through an isomorphism of arrows. The DAG proof now records the
projection interface explicitly and retains every previous proof dependency.
The blueprint unit's statement and route remain unchanged.

The source formulas were checked against Stacks Project Tags
[0A8X](https://stacks.math.columbia.edu/tag/0A8X) and
[010N](https://stacks.math.columbia.edu/tag/010N), and the Mathlib/source declaration
signatures were read locally. The local literature paths listed in the node are absent
on this machine. The construction covers arbitrary integer k, unbounded M and N,
zero source term P.X k, zero rings, and empty sites without extra assumptions.

The complete module compiles without warnings. Extracting the generic fan argument
into a private lemma reduced the measured compile time from 55.3 to 36.8 seconds.
A declaration-scoped heartbeat increase accommodates dependent projection elaboration.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.quasiIso_homComplex_map_of_single_degree_exact_term`
(node `lem-pc-single-degree-exact-term-hom-quasi-iso`).
No `sorry` remains in the delivered module; no holes were added or split off.
The two new private lemmas are fully proved. This is a proof, not a decomposition.

## No longer needed

None of the original imports, nodes, or proof dependencies is pruned. All three steps
of the original argument are realized. No shift-of-complex theorem or new intermediate
statement is needed: the integer translation is handled by explicit three-term indices.
The broader `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree` import
used during development was replaced by the narrower
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit` import; finite-free,
monoidal-free, and locally-free theory is not used by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface was wrong. The original DAG called the first
step elementary but did not name the existing proved projection interface. The updated
proof dependency `lem-sc-hom-complex-projections` supplies that interface, and its
product, differential, and chain-map equations are used explicitly. No statement,
definition, target, or other group's module was changed.

## Second reading by K3

1. PASS: Compared the entire delivered module with the repository version. The only
   existing declaration's signature is byte-for-byte identical (also checked by extracting
   its text before `:= by`); its docstring and all original public imports are unchanged.
   Only proof-only imports, two private proved helpers, scoped elaboration options, and
   the theorem proof were added. There are no interface changes or change records.
2. PASS: Independently compiled the module without errors or warnings in 37.7 seconds.
   Compiled a scratch copy with `#print axioms` for the theorem and both private helpers:
   each uses only `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   Searched the delivered Lean for forbidden declarations and holes; none occur.
   The chosen projection family is used inside a proof, and its limit, differential,
   and naturality specifications are supplied by the proved projection interface;
   no definition chooses an arbitrary witness from an unproved existence theorem.
3. PASS: No statements were split off and no holes were added. Read both helper proofs:
   additivity is sectionwise addition of linear maps; the fan inverse has identity
   component at k and zero components elsewhere, with the two inverse equations proved
   by the universal property. The argument includes P.X k zero, all integer k, and
   unbounded target complexes. Loogle search `CategoryTheory.Limits.Fan,
   CategoryTheory.IsIso` and independent grep searches for invertible product
   projections and single-degree quasi-isomorphisms found no direct shorter match.
4. PASS: Read the proof from its conclusion through the arrow isomorphism, the three
   invertible projections, and exact-functor preservation. Checked Mathlib's
   `Functor.exact_tfae` indices and the quasi-isomorphism preservation instance.
   The source differential lands at k+1 and vanishes; translation preserves both
   adjacent indices without a sign assumption. The four added imports supply the
   exactness criterion, zero-object preservation, projections, and precomposition
   identities. All old proof dependencies are used; `## No longer needed` is complete.
   Read `dag/units/sk-thm-picard-duality.json`: the unit statement, route, and realized
   fields are untouched; this delivery only implements the existing node-level tool.
5. PASS: Compared the node diff and read every old proof dependency and its Mathlib
   match or Lean interface. Only `proof`, `proof_deps`, and `proof_origin` changed.
   The recorded steps follow the actual Lean proof; the added projection dependency
   supplies precisely the product, differential, and map specifications used.

Second reading changed only this report by adding the independent review. No Lean
or node repair was necessary. One original hole closed; zero holes added or split off;
no original modules or nodes pruned.
