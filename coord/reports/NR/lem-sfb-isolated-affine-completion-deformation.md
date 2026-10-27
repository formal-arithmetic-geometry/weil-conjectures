## Worker report

The item is stated in `Sheaf.RingTheory.IsolatedAffineCompletionDeformation`, declaration
`Algebra.FlatDeformation.isolatedAffine_completion_deformation`. Its only theorem has
proof `sorry`. All helper definitions have real data. The item statement, accepted
proof plan, and original dependencies are unchanged. Added statement dependencies
reuse the landed test-category and marked-flat-algebra interfaces and introduce the
explicit predicate for the tangent vector operations.

Clause-by-clause reading:

* The field is `{k : Type u} [Field k]`; the commutative algebra is
  `{P : Type u} [CommRing P] [Algebra k P] [Algebra.FiniteType k P]`.
* The finite list is `m : Fin r → Ideal P`, with `[∀ i, (m i).IsMaximal]`.
  `hdistinct : Function.Injective m` expresses distinctness. There is no positivity
  hypothesis on `r` and no residue-field identification on the listed points.
* `hsmooth` quantifies over every point of `Spec (CommRingCat.of P)` whose ideal
  differs from every `m i`. Its open neighborhood `U` has smooth structure morphism
  `U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k P))`. This uses the recorded
  scheme-smoothness declaration, rather than formal smoothness of a local ring.
* `completedFibre m i` is `LocalizedCompletion (m i).primeCompl (m i)`:
  `Localization (m i).primeCompl` is definitionally `Localization.AtPrime (m i)`;
  the completion ideal is the image of `m i` in that ring. `AdicCompletion` is
  the inverse limit of all power quotients, with the harmless level-zero quotient.
* `TestCategory k k` is the existing category of local Artinian k-algebras with
  a specified augmentation to k, and residue-preserving k-maps. The augmentation
  is surjective with maximal kernel, hence specifies exactly the residue marking.
* `Groupoid P A` is the existing groupoid of flat coefficient-algebra factorizations
  with a surjective marking to P and kernel the coefficient maximal ideal times Q.
  Its core arrows are exactly coefficient-algebra isomorphisms preserving the marking.
  The first clause of `IsPointCompletionFunctor` asserts all these source objects are
  finite type; nilpotent lifting makes this full groupoid equal the source in the node.
* `pointDenominators (m i) Q` is the inverse image of the complement of `m i` under
  `marking Q`. Thus `pointCompletion` is the completion of the actual local ring at
  the inverse-image maximal ideal, not an arbitrary chosen point or ring.
* `F A i` is a functor from the source groupoid to the ith completed-fibre groupoid;
  the collection is the product-valued functor. `e A i Q` identifies its underlying
  algebra with this actual completed local ring. The scalar equation fixes its
  coefficient map. `IsLocalizedCompletionMap` fixes its marking at every finite
  quotient of the localization, including fractional representatives.
* Every object of a completed-fibre groupoid is asserted complete Noetherian local
  by `IsCompleteLocalDeformation`; this gives exactly the complete target category
  in the node. The arrow condition says marked isomorphisms preserve all powers of
  the maximal ideals. This implies continuity for their maximal-ideal adic topologies;
  applying it to the inverse gives a homeomorphism. No unrelated topology is chosen.
* The last clause of `IsPointCompletionFunctor` preserves every marked tensor base
  change, for arbitrary test arrows, with a unique map characterized quotientwise.
  It gives the natural base-change comparisons and their identity/composition
  compatibility by uniqueness. `IsBaseChange` retains the actual tensor comparison
  and its formula on every simple tensor.
* `IsPointCompletionSmooth` quantifies over every surjective test arrow `f : A' ⟶ A`,
  every marked Q, every family D over A', and every specified marked base-change
  map `j i : D_i → F_i(Q)`. Specifying this map with `IsBaseChange` is equivalent
  to specifying the node's tensor-reduction isomorphism. It gives Q', the specified
  source reduction map q, and marked isomorphisms `beta i : F_i(Q') ≅ D_i`.
  The last quotientwise equality says `(j i).comp (hom (beta i).hom)` is precisely
  the completion of q, transported by e. Thus it retains every supplied reduction
  isomorphism; it is stronger than a bare existence-of-lifts assertion only in the
  manner explicitly required by the node.
* `HasPointCompletionTangentEquiv` uses the exact isomorphism classes over
  `squareZeroTest k`, whose underlying algebra is k[epsilon]/epsilon². The
  existential vector structures are constrained by `IsCanonicalTangentModule`:
  scalar base change and gluing the two square-zero directions followed by addition
  specify their operations. They cannot be arbitrary vector structures on these sets.
  `dF` is a k-linear equivalence onto the product, with its value fixed on every
  dual-number deformation by `tangentClass ((F _ i).obj Q)`. Thus it is the induced
  tangent map, and the target operations are coordinatewise.

Dependency declarations read and reused:

* `Field`, Mathlib.Algebra.Field.Defs.
* `AlgebraicGeometry.Spec`, `Spec.map`, Mathlib.AlgebraicGeometry.Scheme.
* `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
* `Localization.AtPrime`, Mathlib.RingTheory.Localization.AtPrime.Basic.
* `AdicCompletion`, `IsAdicComplete`, Mathlib.RingTheory.AdicCompletion.Basic;
  ring and algebra structures from Mathlib.RingTheory.AdicCompletion.Algebra.
* `RingHom.Flat`, Mathlib.RingTheory.RingHom.Flat, used through the existing groupoid.
* `AlgebraicGeometry.ArtinDeformation.TestCategory`, `ring`, `residue`, `map`,
  `squareZeroTest`, Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory.
* `Algebra.FlatDeformation.Groupoid`, `algebra`, `scalar`, `marking`, `hom`, `ideal`,
  `IsBaseChange`, Sheaf.RingTheory.MarkedFlatAlgebraDeformations.
* `AlgebraicGeometry.ArtinDeformation.squareZeroMap`,
  Sheaf.AlgebraicGeometry.ArtinRSTangentTensor, gives the actual square-zero map.

The available proof modules are imported without `public`: the completion-functor
lemma, completion-reflects-flat-liftability, and finite-type-lift-nilpotent. The proof
is copied clause by clause into the theorem docstring, including CRT, unique lifted
idempotents, the Exal tangent comparison, and the marked smoothness criterion.
Proof dependencies without Lean statements are not manufactured as assumptions.

Edge cases checked before writing: r=0 is allowed and makes the product tangent
space the zero space; smoothness then states unobstructedness of the everywhere
smooth P. P=0 has no listed maximal ideals and terminal deformation groupoids.
No nontriviality assumption on P was added. Smooth listed points are allowed.
The residue fields of the listed points may be arbitrary finite extensions of k,
including inseparable extensions where appropriate. Coefficient arrows include
identity maps and arbitrary surjections, not only small extensions. The tangent
operations include scalar zero, scalar one, and zero tangent classes. All rings,
including k, can be lifted to one arbitrary common universe u; this imposes no
size restriction on a fixed algebra, while keeping test rings large enough to
include its coefficient field. autoImplicit is disabled throughout.

Searches run: msearch leanfinder with the affine isolated completion-deformation
statement returned eight ordinary smoothness results, none the deformation theorem.
msearch loogle `"deformation", "completion"` returned zero hits; msearch grep
`isolated.*deform|deform.*isolated|Deformation.*Tangent|deformation.*tangent` found
only a comment in Perfectoid/FontaineTheta. Project rg searches in both roots for
isolated/deformation and the item id found the different localization-based
AffineIsolatedDeformationLift, not this completion statement. Searches for tangent
operations are recorded verbatim in the new node. DAG and blueprint searches found
no existing definition node with this predicate. The general `tangentSet` and the
RS tangent theorem concern an independently supplied cofibred groupoid, not this
flat algebra core; their square-zero tests and maps are reused.

No statement correction, unusable dependency, or disputed mathematical assertion
was found. Initial elaboration errors in the tangent helper were resolved by making
its implicit coefficient field explicit; the width warning was repaired by wrapping
its signature. Compilation and the prescribed delivery dry run validate every file.

## New nodes

`def-sfb-flat-algebra-deformation-tangent-module` defines the exact quotient set of
flat dual-number deformations, its representative map, base-change relation along
linear parameter maps, and the predicate fixing the canonical vector operations.
It follows Stacks 0DY3 and the square-zero tangent operations of formal-defos.tex.
Its separate module is `Sheaf.RingTheory.FlatAlgebraDeformationTangentModule`.
It has no theorem or sorry. The actual algebra groupoids, test objects and parameter
maps are reused. LeanSearch returned dual-number and derivation lift constructions;
Loogle returned no deformation/tangent match; Mathlib grep found only unrelated
sphere tangent sets. Both project roots and the DAG were also searched: the general
cofibred tangent-set definition and RS theorem do not define this specialization's
operation predicate, and no existing node carries it. `blueprint_refs.py ancestor`
reports a null blueprint ancestor; the new node retains that null ancestor and the
item's full inherited lineage with this item prefixed to `via`.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
