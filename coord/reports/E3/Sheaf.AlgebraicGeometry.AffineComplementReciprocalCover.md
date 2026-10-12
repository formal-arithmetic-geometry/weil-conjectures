## What changed

Filled `AlgebraicGeometry.exists_affine_complement_reciprocal_cover` in
`lean/Sheaf/AlgebraicGeometry/AffineComplementReciprocalCover.lean` without changing
its signature or visibility. Three proved private helpers compute the stalk dimension
outside the nonempty open, put the generic point in each nonempty open, and commute
restriction with the map to the function field. Their names are
`complement_stalk_dimension`, `generic_mem_open`, and `functionField_res`.
All original imports are retained;
no other module, definition, or statement is changed. The second reader aligned
the theorem docstring and the existing node’s last proof step with the actual
empty-complement branch; `proof_deps` and `proof_origin` are unchanged.

The proof follows the existing node's three steps. Mathlib identifies stalk dimension
with specialization coheight; the generic point strictly generalizes each complement
point, so its stalk dimension is exactly one. Mathlib supplies the Noetherian stalk,
domain, local-ring, finite maximal-spectrum, and fraction-ring instances. Apply
`AlgebraicGeometry.Scheme.separated_affine_functionField_surjective`, identify its
canonical tensor map with `Algebra.TensorProduct.productMap`, and apply
`RingTheory.exists_inv_mem_jacobson_of_tensor_surjective` to the finite complement.
Represent the inverse germs by sections, prove compatibility using injectivity into
the function field, and use `X.sheaf.existsUnique_gluing`. The resulting open covers
the complement. Its section has nonunit germs there, and its restriction to the
overlap with U is a unit because its product with f is one. These two facts prove
the exact basic-open equality.

When the complement is empty, the gluing is over the empty family, V is bottom,
and the overlap ring has a unique element. This branch avoids assuming that V or
U intersect V is nonempty. In the other branch, the generic point supplies a point
of every intersection used for function-field injectivity. The witnesses occur
inside an existential proof; no definition chooses data from an unproved existence
statement.

Validation: the module compiles cleanly through the prescribed local compiler
(about five seconds). Lines are at most 100 characters. The existing statement,
public imports, and unit route are unchanged. Source checked against the first
paragraph and open-cover construction of
[Stacks Tag 09NB](https://stacks.math.columbia.edu/tag/09NB).

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_affine_complement_reciprocal_cover`
(node `lem-sc-affine-complement-reciprocal-cover`).

No sorry remains in the delivered module, and no hole is added or split off.
The proof intentionally uses the existing stated dependencies
`AlgebraicGeometry.Scheme.separated_affine_functionField_surjective`
(node `lem-sc-separated-affine-function-field-surjective`) and
`RingTheory.exists_inv_mem_jacobson_of_tensor_surjective`
(node `lem-sc-jacobson-denominator-function-field`); their existing proofs contain
sorry in the current checkout and are outside this delivery. This closes the
item's hole from its planned dependencies, rather than completing those dependencies.
The three private helpers are proved directly from Mathlib.

## No longer needed

None. No original import, node, or module is pruned. The existing proof route and
its dependencies are retained; its infrastructure facts are available in Mathlib,
so no new statement modules are necessary. Trial imports of
`Mathlib.AlgebraicGeometry.Properties` and
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing` were removed before the final
compile because the original imports already expose their declarations.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. An initial dry run flagged a
file-level local-instance attribute as a possible interface change. It was removed;
the partial order is now introduced inside the dimension helper's proof. An
unnecessary file-level elaboration option was also removed, and the complete
module still compiles cleanly. The separatedness dependency presents
its canonical map as a tensor-product lift, whereas the denominator dependency uses
`productMap`; `convert` and `congr 1` prove the required identification. This needs no
signature adaptation. The proposed stalk and gluing infrastructure already exists
in Mathlib, and the node's source proof is preserved.

The repository copy has no `literature/stacks-project/varieties.tex`; the source
was read at the public Stacks Tag 09NB page instead. There is no stage-3 section I
in the current `coord/delivery-errors.md`; the standing brief and stage-3 document
supply the applicable delivery rules.


## Second reading by E3

1. Compared the complete delivered module with the repository using `diff -u`.
   The sole existing theorem’s signature and visibility are byte for byte unchanged.
   The only additions are three private proved helpers and the replacement proof;
   the second reading also corrects a proof docstring. No definitions, other modules,
   public imports, or target statements changed; no change record is required.
2. Compiled the delivered module and a scratch copy with `#print axioms` for all
   four declarations through `lcompile.py`. Both compiled without errors or warnings.
   Each helper uses only `propext`, `Classical.choice`, and `Quot.sound`. The item also
   uses `sorryAx`, inherited from the two existing planned dependencies named above.
   No delivered declaration contains `sorry`, and there is no axiom, unsafe code,
   opaque declaration, external implementation, or data definition. Existential
   witnesses are used only within this theorem’s proof, never to define an object.
3. No statement was split off and no new node was introduced. Checked the private
   helpers: the complement point differs from the generic point, giving positive
   coheight bounded by one; nonempty opens contain the generic point; restriction
   compatibility is exactly the presheaf germ restriction theorem. Checked the empty
   complement separately: the empty gluing family gives V bottom, and the overlap
   section ring is subsingleton. In the nonempty case every intersection used for
   injectivity contains the generic point. The final two inclusions of D(g) use
   nonunit complement germs and the reciprocal equation respectively.
4. Independently searched LeanFinder for reciprocal sections near finite affine
   complements and searched `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib using
   generic-point, restriction-map, and reciprocal-cover terms. No shorter existing
   proof of this item was found. An upstream restriction lemma is the same one-line
   germ calculation as the private helper and does not justify importing its large
   divisor module. The four public Mathlib imports provide notions in the theorem’s
   signature; both Sheaf imports are proof-only and actually used. Nothing is pruned.
   Read `dag/units/sk-thm-curveestimate.json`, including `realized`: this auxiliary
   node does not replace any realized unit statement or step, and its route stays.
5. Read the existing node, all eight proof-dependency records, and both imported
   Sheaf statements. The infrastructure dependencies match Mathlib declarations
   and instances used by the proof, and the two open dependencies are applied with
   their original full hypotheses. `proof_deps` is still the union of the steps’
   uses, and the document-based `proof_origin` remains correct. Checked the source
   construction against [Stacks Tag 09NB](https://stacks.math.columbia.edu/tag/09NB).
   No new-node fields or statement changes are involved.

Verdict: passes all five checks. Changed only the theorem’s proof docstring and the
node’s last proof-step text: the empty-complement branch retains the denominator
witness f rather than explicitly setting f to one, and actual indexed neighbourhood
intersections contain the generic point. The Lean proof itself needed no repair.
