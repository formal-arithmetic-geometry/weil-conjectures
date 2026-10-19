## Worker report

The module `Sheaf.RingTheory.EtaleContraction` defines the construction in
`def-weil-pbc-etale-contraction`. The main declaration is
`CommRingCat.etaleContraction`. Supporting declarations are in the namespace
`CommRingCat.EtaleContraction`: `Representatives`, `finiteDiagram`, `step`, `stage`,
`sequence`, and `ι`. All are actual definitions; there are no theorem proofs or
`sorry` terms. No node statement or dependency was changed, and no new notion or
new node was needed.

Clause-by-clause correspondence:

- A commutative ring in a fixed universe is `(R : CommRingCat.{u})`. Internally
  it is `op R` because the framework constructs finite tensor products as finite
  wide pullbacks in the opposite category. This changes neither the rings nor
  the direction of their ring maps after `unop`.
- The chosen faithfully flat étale algebras are the objects of
  `((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ (op R))`.
  The structural arrow is the opposite of a ring map from `R` to the algebra.
  The horizontal property `⊤` allows every base-algebra homomorphism, so its
  isomorphisms are exactly base-algebra isomorphisms. `CommRingCat.etale` is
  `RingHom.Etale` (Etale.lean, definition and `etale_iff`); on spectra this is
  precisely `AlgebraicGeometry.Etale`, by its `HasRingHomProperty` instance.
  `RingHom.Etale` includes finite presentation as its second conjunct, so the
  finite-presentation clause is present without an additional restriction.
  `CommRingCat.faithfullyFlat` uses `RingHom.FaithfullyFlat`.
- `Representatives` is the `Skeleton` of `SmallModel.{u}` of that category.
  The existing essentially-small instance in `ProEtale.Etale` supplies the
  small model. Its equivalence preserves and reflects isomorphism classes;
  `Skeleton` chooses one representative of each such class. Consequently
  there is exactly one factor per algebra isomorphism class. All of these
  representatives, rings, and finite-subset indexing types remain in `u`
  throughout the recursion. No independent, smaller index universe is used.
- `FiniteFamilies (Representatives R)` is the preorder of finite subsets of
  these representatives. `FiniteFamilies.map (fromSkeleton ...)` sends a
  finite subset to its finite set of chosen objects in the small model.
  `fromSkeleton` is injective on objects: equality of representatives gives
  an isomorphism of skeletal objects and hence equality. Thus no factor is
  lost or duplicated by this image operation.
- `finiteDiagram` precomposes the framework's `FiniteFamilies.diag` with that
  finite-subset map. In `FiniteFamilies.diag`, an object is
  `Over.mk (WidePullback.base U.hom)`. Dually this is the coproduct of the
  finite family in commutative base algebras, which has exactly the universal
  property specified for `B_{n,E}`. The ring at the empty subset is canonically
  isomorphic to the base ring, since the empty wide pullback is the base.
- For an inclusion of finite subsets, `FiniteFamilies.diag` uses
  `WidePullback.lift` with `WidePullback.π` for the factors in the smaller
  subset. After reversing arrows these are exactly the coproduct inclusions
  into the larger tensor product, adjoining units in the new factors.
- `step R := limit (finiteDiagram R)` in `Over R` is the dual of the filtered
  ring colimit of these finite tensor coproducts. Its `.hom` is the structural
  map in the opposite direction. The finite-subset preorder includes the
  empty subset and is directed by union. Dually its limit is a ring colimit:
  compatible maps determine the base-ring map from the empty subset, and
  the universal property in the base-algebra category then applies.
- `stage R` starts at `R` by its zero equation, and its successor is
  `(step (stage R n)).left`. This is exactly `R_0 = R` and the stated formula
  for `R_{n+1}`. The `.hom` agrees with the map induced by the empty subset
  by the limiting cone's compatibility and the empty-product universal
  property.
- `sequence R := Functor.ofOpSequence ...` uses precisely those structural
  arrows. `CommRingCat.etaleContraction R` takes its limit and then `unop`;
  hence it is the ring colimit over the natural numbers, namely `Rᵉ`.
- `CommRingCat.EtaleContraction.ι R n` is `(limit.π ... (op n)).unop`, the
  canonical ring map `R_n → Rᵉ`. At each of the two levels the chosen
  categorical `limit` supplies a universal cone, and reversing the arrows
  supplies exactly the compatible-family factorization and uniqueness for
  ring maps stated in the node. In particular no arbitrary ring was selected
  from a bare existence theorem.

Dependency declarations read and used:

- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`, via
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`; the
  latter is used by `CommRingCat.faithfullyFlat` in
  `WeilConjectures.RingTheory.ProEtale.FaithfullyFlat`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, and
  `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
  The affine criterion is the `HasRingHomProperty @Etale RingHom.Etale`
  instance; the actual ring-side predicate is `CommRingCat.etale` from
  `WeilConjectures.RingTheory.ProEtale.Etale`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
  `RingHom.Etale` is formal étaleness together with finite presentation.
- `Mathlib.Algebra.Category.CommAlgCat.Basic`: `instHasColimitsCommAlgCat`,
  and `Mathlib.Algebra.Category.Ring.Colimits`:
  `CommRingCat.Colimits.hasColimits_commRingCat`. Ring colimit instances
  provide the opposite-category limits used here. Base-algebra coproducts
  are represented dually by wide pullbacks.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`, universal
  cones and canonical maps, dual to the dependency's `colimit` and
  `colimit.ι`. These are the same Mathlib chosen-(co)limit definitions.
- Additional existing machinery, not new notions: `Skeleton`, `fromSkeleton`
  in `Mathlib.CategoryTheory.Skeletal`; `SmallModel`, `equivSmallModel`;
  `FiniteFamilies.map`, `FiniteFamilies.diag` and the finite-wide-pullback
  constructors in `WeilConjectures.RingTheory.ProEtale.Contraction.Covers`;
  `Functor.ofOpSequence`.

Edge cases inspected: the zero ring is allowed (no `Nontrivial` assumption);
its identity algebra is still faithfully flat and étale. Fields and arbitrary
positive characteristic are allowed. The empty finite subset is retained and
yields the base ring, and inclusions from it yield the structural maps. The
zero stage is the input ring, and its canonical map to the final ring is `ι R 0`.
An empty set of representatives would still give the empty-tensor construction;
in fact the identity algebra always supplies a class. Nontrivial automorphisms
of a representative do not cause repeat factors because the skeleton indexes
objects, not morphisms. Arbitrarily large fixed universes are covered by `u`.

Searches for an existing construction (2026-10-15):

- `msearch.py leanfinder`, query `successive tensor products of one representative
  of every faithfully flat etale algebra and sequential colimit`: eight hits,
  including `Algebra.FormallyEtale.instTensorProduct`,
  `Algebra.Etale.exists_subalgebra_fg`, `Algebra.Etale.baseChange`, and composition
  lemmas; no complete construction matching the node.
- `msearch.py loogle`, query `Algebra.Etale`: twelve hits defining étaleness and
  its basic properties, including the finite-presentation field; no complete
  construction matching the node.
- `msearch.py grep`, query
  `EtaleContraction|etaleContraction|etale.*contraction`: no Mathlib hit.
- `rg` in upstream `WeilConjectures`, query `EtaleContraction|etaleContraction`,
  and searches for `Contraction`, `IndEtale`, `FaithfullyFlat`: located
  `IndEtaleContraction` in `RingTheory/ProEtale/ProEtaleContraction.lean` and
  its supporting construction. Read the full relevant definitions in the
  group clone, as well as `coord/pefw-upstream-framework.md`.
  That construction takes finite subsets of a possibly non-skeletal
  `SmallModel`, so it need not take exactly one factor per isomorphism class.
  The present node already identifies that distinction in its split report.
  The new construction reuses its finite diagram machinery after restricting
  to the skeleton; it does not redefine any existing tensor, colimit, or
  representative-selection notion.
- `rg` in upstream for the exact blueprint id: no hit. `rg` in `lean/Sheaf` for
  contraction and skeletal representatives: existing uses of skeletons and
  representatives for other constructions, no étale-contraction definition.
  The proposed declaration names have no match in `dag/lean_names_upstream.json`.

Server validation: `scompile.py NA def-weil-pbc-etale-contraction` compiled the
module cleanly, 1.7 seconds, nice 19, two threads, 60-second limit. No local
compiler or build was run. No statement fault or dispute was found.

## Second reading by NA

I independently opened the node, its blueprint source at
`sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-etale-contraction.md`
(order 1226), all six statement-dependency nodes, their recorded Mathlib
signatures, and the delivered Lean file. The source for this item is the blueprint
rather than a Stacks tag. It assumes only a commutative ring and a fixed universe;
there is no ambient Noetherian, field, nonzero, or characteristic hypothesis.
I also read the exact group-clone `ProEtale.Etale`, `ProEtale.FaithfullyFlat`,
`Contraction.Covers`, and `ProEtaleContraction` modules and
`coord/pefw-upstream-framework.md`.

Object, hypothesis, and conclusion checklist (all verdicts: matches):

1. An arbitrary commutative ring R: `(R : CommRingCat.{u})` in
   `CommRingCat.etaleContraction`. The helper arguments `op R` are the same
   ring in the opposite category, with ring homomorphisms reversed.
2. At every stage, exactly one representative of each isomorphism class of
   faithfully flat, étale, finitely presented base algebras:
   `Representatives R = Skeleton (SmallModel.{u}
   ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R))`.
   I read `etale_iff` and `faithfullyFlat_iff`: these use `RingHom.Etale`
   and `RingHom.FaithfullyFlat`, respectively. The latter is faithful flatness
   of the codomain module for the induced algebra structure, the dependency's
   notion. `RingHom.Etale` uses `Algebra.Etale`, whose finite-presentation
   field supplies the explicit finite-presentation condition without any
   stronger assumption. The recorded `AlgebraicGeometry.Etale` has
   `HasRingHomProperty @Etale RingHom.Etale`, agreeing on the recorded `Spec`
   and `Spec.map`. `⊤` permits all base-algebra morphisms. Thus its isomorphisms
   are precisely base-algebra isomorphisms, in the opposite direction.
3. Fixed universe throughout: the essentially-small instance in `Etale.lean`
   is at `u`; `SmallModel.{u}`, its `Skeleton`, finite subsets, and every
   recursive ring are at that same universe. No independent index universe
   or extra user-supplied instance restricts R.
4. Finite subsets E of the representatives: the domain of `finiteDiagram`
   is `(FiniteFamilies (Representatives R))ᵒᵖ`. I read `Skeleton`,
   `fromSkeleton`, and `toSkeleton_fromSkeleton_obj` in Mathlib. In particular
   the latter makes `fromSkeleton.obj` injective, so `FiniteFamilies.map`
   taking images of finite subsets loses no factors. The small-model
   equivalence also cannot identify nonisomorphic skeleton representatives.
5. The finite tensor coproduct B_E and its universal property:
   `FiniteFamilies.diag` takes `Over.mk (WidePullback.base U.hom)`.
   In opposite rings the wide-pullback universal property is exactly the
   coproduct property of base algebras, including all factor maps. This reuses
   categorical limits rather than introducing an alternative tensor notion.
6. The empty subset gives the base ring up to its canonical isomorphism:
   the wide-pullback diagram of an empty family has only its base object.
   No nonempty-family condition appears in `finiteDiagram`.
7. Inclusion E ⊆ E' gives the canonical tensor inclusion: `FiniteFamilies.map`
   sends subset inclusions to inclusions of images; `FiniteFamilies.diag.map`
   is `WidePullback.lift` with projections to the smaller family. Unop gives
   exactly the factor inclusions into the larger coproduct, adjoining units.
8. R_(n+1) is the filtered ring colimit, with structural map from the empty
   subset: `step R = limit (finiteDiagram R)` and its `.hom`. The limit is
   taken in opposite-ring `Over R`, i.e. base algebras dually. This also gives
   the ring colimit: the finite-subset indexing category is nonempty and
   directed by union; a compatible family of ring maps fixes one common
   base-ring map through the empty subset. The base-algebra universal property
   therefore gives the unrestricted compatible-family ring universal property.
   The structural arrow is the empty-subset arrow by cone compatibility and
   the empty-wide-pullback universal property.
9. R_0 = R and recursion: the two equations of `stage` are respectively
   `0 => R` and `n + 1 => (step (stage R n)).left`.
10. The natural-number structural diagram: `sequence` uses
    `Functor.ofOpSequence (X := stage R)` with exactly the arrows from `step`.
11. R^e and its canonical maps: `etaleContraction` is
    `(limit (sequence (op R))).unop`, and `ι R n` is the unop of its limit
    projection. The chosen `limit` and `limit.isLimit` supply compatible
    families, their factorizations, and uniqueness; reversing arrows gives
    exactly both colimit universal properties specified by the node. The
    recorded `lean.statement` is the declaration's signature verbatim from
    the `def` keyword. Every universe and variable is explicitly bound.

Edge cases: zero rings (hence the empty affine scheme) are included; no
`Nontrivial` binder is present. All characteristics and fields are included.
The empty finite subset remains present even for a hypothetical empty
representative type; the identity algebra in fact supplies an isomorphism class.
Stage zero and `ι R 0` are defined. Finite subsets are a preorder with union as
an upper bound, so no assumption of a linear or well order is implicit.
Nontrivial automorphism groups do not cause multiple factors: the skeleton
quotients objects by isomorphism, not by morphisms. There are no sheaves,
cohomological degrees, or zero objects imposing further edge conditions here.

Independent searches on 2026-10-15:

- `msearch.py leanfinder` with "iterating coproducts of all etale faithfully
  flat algebras with a small skeleton and taking a direct limit": eight hits
  about étale descent, finite products, composition and standard smoothness;
  no complete construction.
- `msearch.py loogle` with `RingHom.Etale`: twelve hits about the ring-map
  predicate and stability properties; no complete construction.
- `msearch.py grep` with
  `etaleContraction|EtaleContraction|tensor.*representative|representative.*tensor`:
  zero Mathlib hits. Direct `rg` over Mathlib, upstream `WeilConjectures`,
  project `lean/Sheaf`, and the upstream name index found the related
  `IndEtaleContraction` and its uses, not the present declaration.
- I unfolded the related existing construction through `precontraction`,
  `Contraction.Construction.obj`, and `.diag`. It indexes finite subsets of
  `SmallModel` without passing to a skeleton. Thus it does not implement the
  source's exact choice of one representative per isomorphism class. The
  delivered module correctly reuses its finite-diagram machinery with a
  skeleton; it is not a duplicate of an available exact construction.

No new nodes, dependency modules, or statement correction are needed. There is
no `statement_change` to audit. All delivered declarations have source and
blueprint docstrings. The node has no proof steps, and the module has no theorem
proofs, `sorry`, hollow data, private copies, or file-local notation/instances.
No mismatch was found and no Lean or node text was changed. This reading adds
only this independent review and fresh validation to the worker report.
