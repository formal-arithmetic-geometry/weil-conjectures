## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRingInvariantPowerLifting`
states `AlgebraicGeometry.reductive_ring_invariant_power_lifting`, with exactly one
postponed theorem proof. It assumes no finite generation or flatness of either algebra.
The source was opened at the primary journal PDF,
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf:
Alper Theorem 9.7.5, Proposition 9.3.1(i), Lemma 9.2.5(2),(3), pp.522--528.
The current blueprint unit is the six-functor stability proposition; this is a
supporting invariant-theory lemma, not that unit's own statement.

Clause-by-clause reading of the unchanged node statement:

- A commutative ring is `R : CommRingCat.{u}`; a group scheme over its spectrum is
  `G : Grp (Over (Spec R))`. `GrpObj` supplies the multiplication, identity, inverse
  and their group-object diagrams in the over category. The field-only wording of
  the old group-scheme node's explanatory note does not limit `GrpObj` itself.
- Smooth and affine are `[Smooth G.X.hom]` and `[IsAffineHom G.X.hom]`.
  Finite presentation is explicitly all three of
  `[LocallyOfFinitePresentation G.X.hom]`, `[QuasiCompact G.X.hom]`, and
  `[QuasiSeparated G.X.hom]`, as the item specifies.
- `hgeom` quantifies over every algebraically closed R-field Ω and applies the
  existing `ReductiveTorusCentralizer.IsReductive` to the pulled-back group.
  Algebraically closed R-fields give all geometric points, hence geometric fibres.
  The reused predicate says affine finite type and smooth, geometrically connected,
  and every smooth connected normal closed unipotent subgroup over an algebraic
  closure is trivial. Its affine/finite-type/smooth parts follow already from the
  structure-morphism hypotheses by base change, so add no mathematical restriction.
  Taking an algebraic closure of an already algebraically closed Ω adds no
  restriction either. Its unipotence is the existing faithful finite-dimensional
  closed representation with nilpotent matrix minus identity on geometric points.
  Thus this is precisely the stated geometric connectedness and trivial smooth
  connected unipotent radical, with no splitness assumption.
- `R' : CommRingCat.{u}` with `[Algebra R R']` is an arbitrary base algebra.
  Every occurrence of `((Over.pullback (Spec.map (CommRingCat.ofHom
  (algebraMap R R')))).mapGrp).obj G` is the actual base change G', with
  transported multiplication, identity and inverse. Its underlying scheme is the
  recorded `pullback G.X.hom (Spec.map ...)`, structure map `pullback.snd`.
- `AffineGroupAction.Coaction R' G' E` uses C' = `Γ(G'.X.left, ⊤)` with the
  canonical Hopf structure from the given group object, not an arbitrary Hopf
  structure or a map chosen from an existence theorem. The coaction's `map` is
  an R'-algebra homomorphism E -> E tensor_R' C'. `counit` is the composition
  with id tensor epsilon, followed by `TensorProduct.rid`; `coassoc` is
  `(rho tensor id) rho = (id tensor Delta) rho`, with `TensorProduct.assoc`.
  Both coactions in the theorem have exactly these laws.
- `E : Type v`, `F : Type w`, their `CommRing` and `Algebra R'` instances are
  unrestricted. In particular they are not required to be finite, finite type,
  flat, reduced, or nonzero. Independent universes v and w retain arbitrary sizes.
  R and R' share one arbitrary universe u so their schemes can form a fibre
  product; every particular pair can be placed in a common universe. Geometric
  test fields use u (not a possibly smaller independent universe), so hgeom is
  nonvacuous whenever the base has a geometric point.
- `f : E →ₐ[R'] F` and `hf : Function.Surjective f` encode the surjection u.
  `heq` is exactly `(f tensor id_C') rho_E = rho_F f`, as a linear map equality;
  the maps are algebra maps, so linear-map equality imposes the same square.
- `b : F` and `hb : ρF.map b = b ⊗ₜ[R'] 1` encode b in F^{G'}.
- The conclusion `∃ (N : ℕ) (a : E), 1 ≤ N ∧
  ρE.map a = a ⊗ₜ[R'] 1 ∧ f a = b ^ N` supplies the positive exponent,
  the invariant lift, and exactly the required equality.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`,
  `isAffine_of_isAffineHom` and the affine pullback instances.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; the standard `QuasiCompact`, `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, as used by IsReductive.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: scheme base change is
  `Over.pullback`, group base change its `mapGrp`. The former module arrives
  through the existing reductive-terminology imports; no duplicate construction.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `Map`: `TensorProduct`,
  `TensorProduct.tmul`, `LinearMap.rTensor`, with the standard associator/unitor.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`. Its implementation
  uses `SolvableGroupStructure.IsUnipotent` from the corresponding module.
- `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`:
  `HopfAction.affineCoordinateHopfAlgebra` owned by
  `def-sfb-affine-coordinate-hopf-algebra`. This returns Mathlib's existing
  canonical instance in `Mathlib.AlgebraicGeometry.Group.Affine`.
- The theorem imports the recorded proof interfaces for determinant,
  Cauchy--Binet, smooth-fibre criterion, affine spectrum fibre products,
  affine flatness, flat tensor exactness, and symmetric algebra universal
  property and grading. The three new stage-1 reductive/DVR proof nodes have
  no Lean record yet, so no fictional import was added. Their complete
  five-step proof plan, including arbitrary base change and the pullback
  module M, is in the theorem docstring.

Edge cases checked before writing:

- Zero base ring: no geometric field points, while unital algebras over it are
  zero rings; the lifting conclusion remains correct. No Nontrivial assumption.
- The trivial group has coaction e -> e tensor 1, so any preimage of b works
  with N = 1. No positive dimension or nontrivial group is required.
- b = 0 has a = 0 and N = 1; N = 0 is explicitly excluded.
- Positive characteristic, mixed characteristic, non-Noetherian and nonreduced
  bases are included. No characteristic or perfectness hypothesis.
- A torus satisfies the geometric hypothesis. A nontrivial smooth connected
  unipotent group fails it by its identity closed normal subgroup.
- Arbitrarily large and nonflat E and F are allowed; the proof plan only uses
  flatness of the coordinate ring supplied by smoothness of G.

Searches for the item and missing notion were made through the prescribed wrapper;
`searches.jsonl` contains receipts. LeanFinder query "Reductive group schemes lift
positive powers of invariants under arbitrary equivariant surjective algebra maps"
returned purely inseparable/Frobenius and abstract invariant-ring declarations, no
match. Loogle `"AlgebraCoaction"` returned 0. Mathlib grep
`geometrically.?reductive|AlgebraCoaction|IsReductive` returned 0. LeanSearch query
"An algebra coaction over any commutative ring is an algebra map to the tensor
product satisfying counit and coassociativity" returned coalgebra and bialgebra
structures, not algebra coactions. LeanFinder's coaction query returned HopfAlgebra
and Bialgebra constructors, no action. Mathlib grep
`AlgebraCoaction|ComoduleAlgebra` returned 0.

Project/source rg searches for reductivity, coactions, AlgebraCoaction,
ComoduleAlgebra and the item id found the field-only HopfAction.AlgebraCoaction
and RelativeHopf.Coaction, and the PGL-specific invariant-power theorem in
`Sheaf.RepresentationTheory.PGLGeometricReductivity`. The latter requires a field,
PGL and finite-type algebras, so does not state the item. No upstream match.
DAG searches found the existing coordinate-Hopf and field-only action nodes;
`tools/blueprint_refs.py search coaction` returned 0 blueprint matches and the
ancestor command returned None, retained as in the item's existing provenance.
No statement correction and no STATEMENT-DISPUTED issue.

Validation: both delivered modules compile independently with scompile.py against
published live dependencies, including a private overlay for their import.
No errors or warnings (the postponed theorem is the only sorry).
The initial typeclass failure on the base-changed structure morphism was repaired
with `baseChange_isAffineHom`, whose body is the existing affine pullback instance;
no extra hypothesis or postponed theorem was introduced.

## New nodes

`def-sfb-ring-algebra-coaction` defines counital coassociative algebra coactions over
an arbitrary commutative ring, and their specialization to the actual coordinate
Hopf algebra of a bundled affine group scheme. Source: Alper Lemma 9.2.5 and
Proposition 9.3.1(i). It also exposes the existing canonical coordinate Hopf
structure and the existing affine pullback instance for inference. All data and
instance proofs are real terms; no sorry occurs in this module. The existing
`def-sfb-hopf-action-module-data` explicitly assumes a field and hence cannot
supply the ring notion. Its statement is not wrong, so it is preserved. Mathlib,
upstream, project and DAG searches above found no arbitrary-ring replacement.
The new node's three search receipts are recorded verbatim with their results.
The item additionally cites the already landed reductive terminology node, whose
actual definition is reused rather than copied.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
