## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine` with a complete Lean proof
following the existing two-step route. The statement and its universe binders are unchanged.
Added proof-only imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
and `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.

Restriction of scalars has exactly the same underlying sheaf of abelian groups.
Reflection and preservation of finite limits and colimits therefore give its exactness
and conservativity. The existing `rightDerivedFunctorHomologyFunctorIso` and
`DerivedCategory.isIso_iff` prove that its unbounded right derived functor reflects
isomorphisms. Choose the standard derived category of the direct-image algebra, apply
`finite_affine_derived_equivalence`, lift the given morphism into the full subcategory,
and transport invertibility through the two natural comparison isomorphisms. The full
subcategory inclusion and equivalence then reflect invertibility back to the original
morphism.

## Proved and sorry left

Closed: `AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine`
(node `lem-sc-affine-derived-pushforward-conservative`): 1 of 1 local holes.
Added holes: none. Local holes remaining: none. This is a proof from existing declarations,
not a decomposition. It still depends on the existing `finite_affine_derived_equivalence`
and the existing assumptions supplying K-injective resolutions in imported modules;
no claim is made that its transitive axiom closure is already free of `sorryAx`.

Local single-file compilation passed without warnings. The mathematical source was read
at Stacks Project `perfect.tex`, labels `lemma-affine-morphism` and
`lemma-affine-morphism-equivalence` (Tags 08I8 and 0AVW). The proof uses the equivalence
route already prescribed by the node. The unit `sk-thm-picard-duality` has no realized
nodes in its statement or proof steps, and no unit route was bypassed.

## No longer needed

None. The existing affine derived equivalence remains needed, and all original imports
are retained. No new modules or nodes are needed. The two new proof-only imports provide
the exact-derived homology comparison and preservation of finite colimits by the
underlying-abelian-sheaf functor, respectively.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG calls restriction-of-scalars
conservativity elementary; its Lean proof additionally requires proving exactness from
underlying abelian sheaves and using the existing exact-derived homology comparison.
The affine equivalence's statement does not provide conservativity itself, so it was
proved here rather than assumed. The caller does not have a derived-category instance
for the auxiliary direct-image algebra: the proof installs `HasDerivedCategory.standard`
locally without altering the theorem's signature.

Searches: LeanFinder found ordinary restriction-of-scalars and forgetful conservativity,
not the derived scheme theorem. Loogle and the prescribed grep search were also run;
local searches in both library roots located the existing exact-derived comparison.


## Second reading by A2

1. **Visible declarations unchanged — pass.** Compared the complete delivered module
   with the repository by `diff -u`. The only changes are the replacement of the theorem's
   proof and two plain, proof-only imports. The existing theorem header, universe binders,
   public imports, definitions (none), and docstrings are byte for byte unchanged. There
   are no statement changes and no change records are required.
2. **Kernel proof — pass.** Independently compiled the delivered file through `lcompile.py`
   without errors or warnings (7.4 seconds). Scanned it for `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by`, and `extern`: none. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine`; its list is
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is inherited
   from existing imported assumptions, including `finite_affine_derived_equivalence`,
   not a new local hole. The auxiliary algebra's derived category is constructed by
   `HasDerivedCategory.standard`, not selected from an unproved existence theorem.
   Destructuring the equivalence theorem supplies proof-local witnesses only; no new
   definition or persistent data is chosen from its existential statement.
3. **Split-off statements — pass, none.** No new declarations, modules, or nodes were
   added, and no lower hole merely renames the conclusion. Closed one local hole and
   added zero holes. Scalar-restriction conservativity is proved inside the existing
   proof, without special cases or additional hypotheses. In particular no boundedness,
   finite-morphism, nonempty-space, or nonzero-ring assumption has been introduced.
4. **Route and pruning — pass.** Read the statements of `finite_affine_derived_equivalence`,
   `rightDerivedFunctorHomologyFunctorIso`, the underlying-sheaf colimit-preservation
   instance, and the direct-image algebra definitions. Scalar restriction has definitionally
   identical underlying abelian sheaves (`Iso.refl`); reflection and preservation give
   finite exactness. The exact-derived comparison, degree by degree for all integers,
   and `DerivedCategory.isIso_iff` give derived conservativity. The two natural
   comparisons `eΦ` and `eS` transport the assumed invertibility, after which the full
   subcategory inclusions and the equivalence reflect it. Both `hE` and `hF` are used
   to lift the morphism into the full subcategory. Searched both Lean roots and Mathlib's
   homology files for derived reflection/conservativity, using different words from the
   first worker. The upstream joint-reflection theorem for `mapDerivedCategory` would
   additionally require transport from the right derived functor and a singleton-family
   specialization; it does not shorten this direct homology argument. All five imports
   serve the statement or this proof, and the sole old proof dependency remains used,
   so `## No longer needed` is complete. Read `dag/units/sk-thm-picard-duality.json`:
   `realized.statement` and its sole `realized.steps` entry are empty; no recorded unit
   realization or route was removed. Checked the source statements and proof at
   https://stacks.math.columbia.edu/tag/08I8 (lemma-affine-morphism) and
   https://stacks.math.columbia.edu/tag/0AVW (lemma-affine-morphism-equivalence).
5. **DAG agrees — pass.** Read
   `dag/nodes/sec-picard-framework/lem-sc-affine-derived-pushforward-conservative.json`.
   Its first step uses the affine derived equivalence and exact conservative scalar
   restriction; its second reflects along the equivalence. These are exactly the Lean
   proof's two stages. `proof_deps` remains the singleton
   `lem-sc-finite-affine-derived-equivalence`, which the proof uses, and `proof_origin`
   still correctly names Tags 0AVW and 08I8. No new node needs a schema or search record.

Changed in the second reading: appended this independent review and recorded the
independent axiom check; no Lean or DAG repair was needed. The local proof closes
`AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine` (1 of 1); added holes: none;
pruned modules: none.
