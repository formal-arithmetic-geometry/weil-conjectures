## What changed

Completed `lean/Sheaf/AlgebraicGeometry/EpiOverFunctor.lean` without changing the
signature or visibility of `epi_overFunctor_map` or either original public import.
Added proof-only imports of `Mathlib.Algebra.Category.Grp.Ulift`,
`Mathlib.Algebra.Category.Grp.FilteredColimits`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.
Updated the proof and proof_origin of `lem-stage3-epi-over-functor` to describe
what the compiled proof does; there are no additional DAG proof dependencies.

The prior sandbox contained a compiling reduction to an unproved
`PresheafOfModules.exists_locally_injective_sheaf_map` in a new module without a
node or report. This delivery proves the required realization in private helpers
inside the item and removes that unfinished new module from the delivered set.

The argument first constructs a small sheaf realization of any presheaf of modules.
Abelian sheafification exists in `max u v`; the locally bijective characterization
is obtained by transporting from an essentially small site model in that universe.
On `C/U`, compare its restriction with the lifted small sheafification available
by hypothesis. The comparison is locally bijective, hence an isomorphism.
Evaluation at the terminal object of `C/U` proves that the global large
sheafification value at U is small. Shrink the values and conjugate all maps,
reflect the sheaf condition along universe lift, and explicitly transport the unit.
Mathlib's module sheafification gives the scalar action.

Apply this construction to the presheaf cokernel of e. Its projection composed
with the realization map is zero because e is epi. Local injectivity of the
realization then makes every cokernel section coming from B locally zero.
Pointwise cokernel exactness supplies the local lifts under e. Cocontinuity of
`Over.forget U` transports those lifts to the over-site; local surjectivity there
implies epimorphy of the underlying abelian-sheaf map, and the faithful forgetful
functor reflects epimorphisms.

Every helper is proved. No arbitrary witness from an unproved existence theorem
is used. The construction also applies to the empty site, zero modules, the
identity epimorphism, and independent universes u and v; no nonemptiness, binary
products, or global small-valued sheafification hypothesis was added. The route
is below the unit level and leaves all realized statements and steps of
`sk-thm-p1` intact.

## Proved and sorry left

Closed the one original hole: `epi_overFunctor_map`
(node `lem-stage3-epi-over-functor`).
Added zero holes; no `sorry` remains in the delivered module.
This is a complete proof from Mathlib, not a decomposition into unproved statements.

Single-file compilation succeeds. The axiom check for `epi_overFunctor_map`
shows only `propext`, `Classical.choice`, and `Quot.sound`.
All lines have at most 100 characters. The delivery dry run is the final check.

## No longer needed

No original import, existing DAG node, or existing library module was pruned.
The abandoned sandbox-only module
`Sheaf.Algebra.Category.ModuleCat.Presheaf.LocalSheafRealization` and its proposed
node `lem-stage3-presheaf-module-local-sheaf-realization` are not delivered or
imported: the realization is proved in this item.

Individually tested proof imports `Mathlib.Algebra.Group.Shrink` and
`Mathlib.CategoryTheory.Sites.Equivalence` were unnecessary and omitted; their
required declarations are already transitively available. Removing each of the
three retained proof imports causes compilation errors, so all three are used.
The two original public imports remain to preserve the public interface.

## Where the brief, the DAG or earlier work was wrong

The original docstring and node source cite Stacks tag 01BY as a local lifting
criterion. Tag 01BY is actually a lemma about coherent modules on ringed spaces:
https://stacks.math.columbia.edu/tag/01BY . The relevant sources are the
sheafification construction and module-cokernel argument:
https://stacks.math.columbia.edu/tag/00WK ,
https://stacks.math.columbia.edu/tag/03CX , and
https://stacks.math.columbia.edu/tag/03D9 . The existing docstring and source field
are left intact; the updated proof_origin records the correct proof sources.

The hypotheses give sheafification only on over-sites in universe u, not on the
whole site in universe u. Therefore one cannot directly use a global
small-valued module-sheafification functor or the usual epi-to-local-surjectivity
instance without first solving this size issue. The private comparison and
shrinking argument supplies exactly that missing work with no extra hypothesis.

## Second reading by S1

1. I compared the delivered module with the repository version. The public theorem
   signature, declaration visibility, and both original public imports are byte-for-byte
   unchanged. The only existing declaration changed is the proof of
   `epi_overFunctor_map`; the three added imports are proof-only.

2. I compiled the item with `python3 /home/ubuntu/weil-launcher/lcompile.py` and compiled
   a scratch copy with axiom checks for every private helper and the public theorem.
   Compilation is clean, there are no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern` declarations, and every checked declaration uses only
   `propext`, `Classical.choice`, and `Quot.sound`.

3. The node statement is unchanged and matches the Lean theorem hypothesis by
   hypothesis, including the site and universe parameters, both sheafification
   assumptions, the module epimorphism, and the over-site conclusion. The new private
   helpers are implementation lemmas rather than split-off public statements, so they
   add no holes or nodes. I checked the local edge cases described in the report: empty
   sites, zero modules, identity epimorphisms, and distinct universes.

4. I checked the proof from the top down against the actual declarations used. The
   universe-lift comparison, shrinking construction, cokernel exactness, and
   cocontinuous restriction are all explicitly present in the proof; no arbitrary witness
   is selected from an unproved existence theorem. The three proof-only imports are used,
   while the tested unused alternatives are omitted. The DAG proof and proof_origin now
   describe this route and have no stale proof dependencies.

5. The unit route is preserved: this is below `sk-thm-p1`, and the unit's statement and
   realized steps remain untouched. I also checked the cited Stacks pages while reviewing:
   00WK concerns sheafification sections, 03CX module sheafification, 03D9 the abelian
   category of sheaves of modules, and 01BY is not the local lifting criterion claimed by
   the old prose. I changed only the proof imports, proof, DAG proof metadata, and this
   review report; no statement or definition was changed.
