## What changed

Proved `TopCat.Sheaf.IsFlasque.subsingleton_H'_top` without changing its signature.
Added proof-only imports for enough injectives and
`WeilConjectures.Mathlib.Topology.Sheaves.Flasque`. The source library already proves
flasque acyclicity for `H`. The proof constructs the natural isomorphism between the
free representable of the top open and the constant `ULift ℤ` presheaf, sheafifies it,
and transports vanishing by `Ext.precompAddEquiv`. The explicit type on the final
additive equivalence fixes the Ext universe. Updated the primary node's proof route.

## Proved and sorry left

Proved `TopCat.Sheaf.IsFlasque.subsingleton_H'_top`
(`lem-sc-zariski-flasque-acyclic`, also `lem-sc-topological-flasque-acyclic`).
No sorry remains in the delivered module; no new sorry or module is added.
Local compilation passes. The delivery dry run checks the axiom closure and server compile.

## No longer needed

No existing imports were removed: both public Mathlib imports support the statement.
Second reading removed the redundant added proof-only import
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`; the final file compiles without it.
The proof does not need `lem-sc-ringed-space-injective-restriction-surjective`
(`Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`): the source
library proves injective abelian sheaves flasque directly with free open sheaves.
The other conceptual plan dependencies are retained: enough injectives, flasque
quotient sections, flasqueness and cohomology. Their results are used inside the
existing source-library proof. No claim is made that the removed node is globally
unreachable, since other targets may need it.

## Where the brief, the DAG or earlier work was wrong

The upstream acyclicity theorem was already proved, as the node's Lean note anticipated.
The only required bridge was the explicit comparison of `H'` at the top and `H`.
The blueprint unit's injective embedding and dimension-shifting route is retained
inside that theorem, rather than reimplemented. No statement or definition changes.

## Second reading by J1

1. Compared the whole delivered module with the repository version. The sole existing
   declaration's signature is byte-for-byte identical: arbitrary `X : TopCat.{u}`, the
   same `HasExt.{u}`, abelian sheaf `F`, flasque instance, natural degree `q`, and
   `0 < q`, concluding `Subsingleton (Sheaf.H' F q ⊤)`. No definition, statement,
   public import, or other declaration changed; no change record is needed. Pass.
2. Compiled the module locally without errors or warnings. A scratch copy with
   `#print axioms` for both `IsFlasque.subsingleton_H` and
   `IsFlasque.subsingleton_H'_top` reports exactly `propext`, `Classical.choice`,
   and `Quot.sound`. Rechecked the final reduced-import version likewise. There is
   no remaining `sorry`, hollow definition, axiom, unsafe code, opaque declaration,
   `implemented_by`, or `extern`. Pass.
3. No statements were split off, and no helpers or modules were added. Thus no new
   lemma needs an edge-case audit or duplicate search. The actual comparison remains
   inside the proof: every open, including the empty open and on the empty space,
   has a unique inclusion into the top open. Its free abelian group is therefore
   canonically the integers; this does not require connectedness or nonemptiness.
   Positive degrees start at `q = 1`, corresponding to `n = 0`; degree zero is
   correctly excluded. Pass.
4. Read the upstream `WeilConjectures.Mathlib.Topology.Sheaves.Flasque` proof,
   particularly `isFlasque_of_injective` and `IsFlasque.subsingleton_H`, and Mathlib's
   definitions of `H`, `H'`, and the flasque short-exact-sequence lemmas. The upstream
   base case uses surjective sections; the inductive case embeds into an injective,
   proves the quotient flasque, and uses the connecting map to dimension shift.
   The local naturality proof checks free generators, then sheafification and the
   contravariant Ext equivalence transport vanishing with the correct universe.
   Searches in `lean/Sheaf/Topology`, the upstream sheaf-cohomology modules, and
   Mathlib's sheaf-cohomology basic module found no existing all-degree `H'`/`H`
   comparison that removes this bridge. The unit record `dag/units/sk-prop-sf-cbc.json`
   has empty `steps` and empty `realized` fields; no realized step is bypassed or
   changed. The old dependency on ringed-space injective restriction surjectivity
   is the sole pruned node, as reported above. Both public imports support the
   unchanged statement. Removing `EnoughInjectives` experimentally fails instance
   synthesis, while removing `GrothendieckAxioms.Sheaf` compiles. Pass after repair.
5. Compared the primary node JSON with the repository: only `proof`, `proof_deps`,
   and `proof_origin` changed. Its two steps describe precisely the upstream
   acyclicity route and the singleton-representable/constant-presheaf comparison.
   The retained quotient, enough-injectives, flasqueness and cohomology dependencies
   account for those steps. The second node `lem-sc-topological-flasque-acyclic`
   already records this same declaration and correctly specializes the primary
   node; its existing dependency route needs no change. No new nodes exist. Pass.

Changed only the redundant added proof-only import
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` and the report documenting
its removal and this second reading. The proof body itself was correct and retained.
