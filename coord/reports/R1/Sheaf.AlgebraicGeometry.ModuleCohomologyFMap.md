## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_nonempty` in
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`, keeping every existing signature,
visibility, structure field, and definition body unchanged. Four proved private helpers
construct a natural-indexed injective replacement, extend a cycle map along an injective
resolution, identify global sections of a direct image, and transport the existing
integer-indexed sections quasi-isomorphism theorem to natural indices.

The injective replacement uses Mathlib's same-lower-bound theorem directly, rather than
the project's stronger monomorphic replacement. The augmentation lift is constructed
degree by degree using injectivity and exactness. The sections comparison is pinned to
the prescribed restriction map, not an arbitrary isomorphism. The inverse homology maps
are justified using the existing named sections quasi-isomorphism theorem.

Added proof-only imports of `Mathlib.Algebra.Homology.Factorizations.CM5a` and
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap`. Updated the node's proof,
proof dependencies, and proof origin, and updated the existence proof's docstring.
The node is not a realized statement or step of `sk-thm-p1`; that unit's route is unchanged.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMapData_nonempty`
(node `def-weil-pbc-module-cohomology-fmap`).

There are no `sorry` declarations left in the item's module, and none are added by this
delivery. No statements are split off. This closes the upper hole from an existing
named dependency. At second reading the repository version of
`AlgebraicGeometry.Scheme.Modules.quasiIso_globalSections_pushforward_injectives`
in `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`
(node `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`) has a proof.
The compiled axiom closure still includes `sorryAx` through existing dependencies;
this delivery neither closes those transitive holes nor adds new ones. No new axioms
or hollow definitions were introduced.

Validation: the complete module compiles with the required launcher compiler, without
errors or warnings. The natural-indexed resolution and lift were separately developed
and compiled in the same module before assembling the final proof. No scheme hypotheses
were added; the construction works for zero coefficients, empty schemes and the identity
morphism as well, since it uses categorical resolutions and the canonical equality of
whole-space inverse images. Width is at most 100 characters. The delivery dry run is the
final mechanical check.

## No longer needed

Removed direct imports:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`.
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`.
- `Sheaf.AlgebraicGeometry.TensorPullback` (redundant; the unchanged public
  `TensorPullbackAdjunction` import already supplies it).

Removed proof dependencies of this node:

- `lem-weil-pbc-complex-injective-resolution-mono`: degreewise monomorphisms are not
  required by the bundled data; Mathlib supplies the needed injective quasi-isomorphism
  preserving lower bound zero.
- `lem-weil-pbc-lift-along-injective-quasi-iso`: replaced by the proved direct inductive
  lift for the augmentation of the chosen injective resolution.
- `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`: uniqueness is not needed for
  existence of the choices. It remains relevant to downstream independence statements.

These are removals of this node's direct proof dependencies. They do not assert that
those modules are unreachable from all other targets. The tensor-pullback notion and
adjunction remain required by the unchanged public definitions and are not pruned.
The other original dependencies remain, and the tensor-pullback adjunction node is
explicitly included in the revised proof-dependency union for the named pullback case.

## Where the brief, the DAG or earlier work was wrong

The existing resolution and sections dependencies use integer indices whereas the
item uses natural indices. The final proof supplies complete bridges through extension
by zero, truncation and the natural functor comparison, without changing either
interface. The DAG's general lifting theorem is more than needed for an injective
resolution augmentation, and its homotopy-uniqueness theorem is unnecessary for this
existence statement. No mathematical statement is disputed and no interface adaptation
is needed.

The cited Stacks source is absent from this clone's literature directory. Remark 01FB
and Lemma 01EZ were read from the Stacks project's cohomology.tex into the sandbox's
scratchpad; that local reference copy is not part of the delivery.


## Second reading by R1

1. Compared the entire delivered module with the repository version and checked the
   declaration table with the delivery parser. Every existing declaration statement,
   visibility, structure field and definition body is unchanged. The only existing
   theorem body changed is `moduleCohomologyFMapData_nonempty`; there are four proved
   private helpers. No other module or change record is delivered. Verdict: pass.

2. Independently compiled the complete module through `lcompile.py` (18.4 seconds),
   with no errors or warnings, and compiled a scratch copy with `#print axioms` for
   all four helpers, the existence theorem and the four named cohomology maps.
   The replacement, augmentation lift and canonical sections isomorphism depend only
   on `propext`, `Classical.choice`, `Quot.sound`. The sections transport and public
   maps additionally depend on `sorryAx` through existing imported declarations.
   The delivered sources contain no `sorry` and no prohibited declarations or
   attributes. The new private definition constructs its component isomorphisms
   directly from inverse-image-of-top equality and naturality. Verdict: pass.

3. No statements were split off, no new public statement or node was added, and no
   hole was moved into a definition. Read the private helpers: lower bound zero
   handles degree zero correctly; negative integer terms are zero and injective;
   the lift starts with the monomorphic augmentation, then uses exactness and
   injectivity at each successor. The comparison is pinned to the required
   restriction map (`sections` is proved by `rfl`). These arguments also apply to
   the zero complex, zero coefficients, empty schemes and identity maps without
   extra assumptions. Verdict: pass.

4. Rechecked shorter routes by Loogle search through the required `msearch.py`
   wrapper (`CategoryTheory.InjectiveResolution, CochainComplex`) and by reading
   Mathlib's injective-resolution descent and same-lower-bound replacement, together
   with upstream `descOfQuasiIso`. The descent results target an injective resolution
   of an object, whereas K here is an injective replacement of h_*I, so they do not
   replace this cycle-lifting helper. The proof already uses Mathlib's replacement
   and exact-short-complex extension. All remaining imports are needed for the
   public definitions or these proofs, and new proof imports are plain `import`.
   Checked the old proof-dependency set: all three removed nodes are reported in
   `No longer needed`; no claim of global unreachability is made. Read
   `dag/units/sk-thm-p1.json`: neither this node nor the removed nodes realizes a
   statement or step there, and the unit record is unchanged. Verdict: pass.

5. Compared the node JSON with the repository: only `proof`, `proof_deps` and
   `proof_origin` changed. The dependency set is exactly the union of the steps'
   `uses`; the five steps describe the Lean construction and the unchanged named
   specializations. The node's statement and Lean record are unchanged. There are
   no new nodes whose mandatory fields need checking. Verdict: pass.

Second reading changed only documentation: corrected the stale report assertion
that the sections quasi-isomorphism theorem itself still contains `sorry`, and
removed the same stale assertion from the node's proof origin. Its compiled
transitive closure still includes `sorryAx`. No Lean repair was needed.
