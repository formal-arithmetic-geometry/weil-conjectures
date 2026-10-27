## Worker report

The module Sheaf.AlgebraicGeometry.ArtinObjectGradedApproximation states
AlgebraicGeometry.artin_object_graded_approximation with sorry. No definition or
additional theorem is introduced. The source read is Stacks artin.tex,
lemma-approximate (07XB), its full statement and proof. All six conclusions are
retained. The prior NO merge was a stage-1 split; the current node has no lean
record, no repair note, and coord/queue.tsv assigns stage 2.

Hypotheses and clauses:

- R is a commutative Noetherian ring: `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`.
- S is Spec R: the base of `F : BasedCategory.{v, w} (Over (Spec (.of R)))`.
  The independent explicitly declared universes u, v, w retain the size
  convention. All schemes and rings are U-small; total category objects and
  arrows have the separately specified bounds.
- Category fibred in groupoids: `hF : IsFibredInGroupoids F`, the existing
  predicate of StablePointedModuliGroupoids. Its definition gives a fibred
  projection and strong cartesianness of every arrow, equivalently groupoid
  fibres. Automorphisms are retained.
- Directed affine limits on objects: `hLimits` quantifies over nonempty directed
  preorders I : Type u, every inverse diagram D and limiting affine cone c, and
  every object in the limit fibre. Its conclusion is an object xi at some i
  and an arrow over the cone projection. Under hF that arrow is cartesian and
  thus identifies x with its pullback. This states only object descent, not
  arrow descent or full limit preservation. IsDirected is a binary upper-bound
  condition, so Nonempty is necessary to express a directed indexing set.
- C is a commutative Noetherian local R-algebra: CommRing, Algebra,
  IsNoetherianRing, IsLocalRing binders. Its named maximal ideal is
  IsLocalRing.maximalIdeal C. Completeness is IsAdicComplete at that ideal.
  k is literally the quotient C/m, so no noncanonical residue-field choice.
- Spec k to S finite type: LocallyOfFiniteType and QuasiCompact on the Spec map
  of algebraMap R (C/m), using the recorded dependency's conjunction convention.
- The image point s: `Ideal.comap (algebraMap R C) (IsLocalRing.maximalIdeal C)`.
  Its primality is inferred. hG is IsGRing of Localization.AtPrime at that prime.
- xC is in Functor.Fiber F.p at the canonical R-spectrum of C, constructed by
  the existing algSpec functor. N : Nat and hN : 1 ≤ N express every positive
  integer precision, with no extra bound such as N ≥ 2.
- Conclusion (1): existential A : Type u, its CommRing and Algebra structures,
  and Algebra.FiniteType R A, precisely finite generation as an algebra.
- Conclusion (2): existential n : Ideal A and n.IsMaximal.
- Conclusion (3): y is an object of the fibre at the canonical R-spectrum of A.
- Conclusion (4): eN : C/m^N ≃ₐ[R] A/n^N, in the direction requested.
- Conclusion (5): z in the C/m^N fibre and arrows a to xC and b to y over,
  respectively, the quotient map C → C/m^N and the composite
  A → A/n^N →[eN.symm] C/m^N. All arrows are cartesian by hF, so these are
  equivalent to the requested isomorphism of restricted objects over eN.
  No unrelated arbitrary comparison map is used.
- Conclusion (6): e₀ : C/m ≃ₐ[R] A/n is related to eN by the canonical
  quotient square using Ideal.Quotient.factorₐ and Ideal.pow_le_self.
  Surjectivity of C/m^N → C/m uniquely determines e₀. The existential ring
  isomorphism g of the two recorded associated graded rings maps the range
  of DirectSum.of in each degree exactly onto its counterpart, hence is a
  graded isomorphism. Its last equality commutes with the two degree-zero
  algebra maps under e₀. Thus it is an isomorphism of graded k-algebras
  with precisely the residue-field identification induced by eN. Ring-map
  compatibility with scalars implies scalar multiplication compatibility.

Dependency declarations read and used:

- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing.
- Mathlib.AlgebraicGeometry.Scheme: Scheme, Spec, Spec.map.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- Mathlib.Algebra.Field.Defs: Field (the residue field instance for C/m).
- Mathlib.RingTheory.AdicCompletion.Basic: IsAdicComplete.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime.
- WeilConjectures.RingTheory.GRing: IsGRing.
- WeilConjectures.RingTheory.AssociatedGradedRing: Ideal.associatedGraded,
  Ideal.associatedGradedPiece, Ideal.associatedGradedAlgebra.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  CategoryTheory.IsFibredInGroupoids. The owning already-landed definition node
  def-sfb-stable-pointed-moduli-groupoids is added to stmt_deps. No node is
  redefined or repaired.
- Mathlib.AlgebraicGeometry.Group.Affine: algSpec, the canonical functor from
  opposite R-algebras to schemes over Spec R.
- Mathlib.CategoryTheory.FiberedCategory.Fiber: Functor.Fiber.

Edge cases checked: N=1 gives precisely residue comparison and the same full
associated graded conclusion. If C is a field, m=0 and all positive graded
pieces vanish; the statement still makes sense. All characteristics and residue
field extensions of finite type are included. The zero ring cannot be local
with field residue, as required by the source. Empty fibres give no xC and
no accidental existence assertion. Empty indexing sets are excluded only in
accordance with the nonempty convention for directed sets. No finite or
skeletal restriction is placed on groupoid fibres, and automorphisms survive.
Grading includes degree zero and the algebra-map compatibility clause; a mere
ungraded ring isomorphism would not suffice.

Searches actually run with msearch.py:

- leanfinder: "Artin approximation of objects of a category fibered in groupoids
  preserving limits with prescribed jet and associated graded ring": eight
  hits, principally formally smooth lifts, Artinian schemes, and affine limit
  Hom descent; no match.
- loogle: "CategoryTheory.Functor.IsFibered, CategoryTheory.Fiber": no hits,
  unknown identifier CategoryTheory.Fiber. Source inspection resolves the name
  as CategoryTheory.Functor.Fiber.
- grep: "artin.*[Aa]pprox|[Aa]rtin.*[Aa]pprox|graded.*approx": zero hits.
- leanfinder: "IsFibered functor all fibers are groupoids limit preserving on
  objects": found Mathlib's IsFibered and HasFibers, which were inspected;
  neither is an approximation theorem.
- rg on lean/WeilConjectures and lean/Sheaf for Artin/artin, Fibered/Fibred,
  approximation, object descent and the item id found no exact theorem.
  Existing IsFibredInGroupoids was found and reused. ObjectsDescend in
  ArtinRepresentableDiagonalCriterion was read: it is specialized to Spec Z,
  whereas this item has arbitrary Noetherian R; the identical quantified
  condition is therefore stated directly as hLimits, without a new definition.

Compilation: scompile.py checked the delivered file on the server against the
live build; it succeeded with no errors or unexpected warnings.

No statement correction, new node, dependency repair, or disputed statement.
The example CompactObject.lean is currently a withdrawn empty module; the
current module-mode conventions in brief-stage2 were followed instead.

The four available separate proof-dependency modules are imported privately:
ArtinApproximationEtaleLocalMap, EtaleCompletionCongruence,
AdicCompletionNoetherian and FiniteTypeGRing. Proof prerequisites with no recorded
Lean module are not re-created merely to import them; their proof plan is
retained in the theorem docstring and the node.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
