## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteClosedSetRationalLifts` states
`AlgebraicGeometry.exists_finite_extension_rational_lifts_of_finite_closed_set`.
Its sole proof is `sorry`; it introduces no definitions. The node's accepted
stage-1 split is unchanged. The inherited "already split" rejection belongs
to stage 1: the current queue explicitly assigns this item stage 2 and the
current node has no Lean record. No repair note is present for this item.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- The two k-schemes and their structure maps are `X Y : Over (Spec (.of k))`,
  with underlying schemes `X.left`, `Y.left` and maps `X.hom`, `Y.hom`.
- Each finite-type hypothesis is the pair `[LocallyOfFiniteType _.hom]`
  and `[QuasiCompact _.hom]`, exactly the recorded finite-type convention.
- The k-morphism is `f : X ⟶ Y`; its commuting triangle is part of an Over
  morphism. Surjectivity is `[Surjective f.left]` on underlying points.
- `S : Set Y.left`, `hS : S.Finite` and `hclosed : S ⊆ closedPoints Y.left`
  express exactly a finite set of closed target points.
- The existential field K, its `Field K` and `Algebra k K` structures, and
  `Module.Finite k K` express a finite-dimensional field extension of k.
  Using the same universe loses no finite extension: a finite algebraic
  extension of a field in Type u has a representative in Type u.
- The base changes are the actual pullbacks along
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`; their structure maps
  are `pullback.snd`, and p_Y is `pullback.fst Y.hom` along that same map.
- `zs : List ((pullback.snd X.hom ...).fieldPoints K)` is a finite list
  of K-rational source points. `fieldPoints K` is the existing subtype
  of maps from Spec K commuting with the K-structure map; for K/K this
  is precisely a section. No alternate rational-point notion is introduced.
- The first conjunct quantifies over every underlying point y of Y_K whose
  projection belongs to S and supplies a K-rational point q with
  `q.1 default = y`. This is the assertion that every point of p_Y⁻¹(S)
  is K-rational, not just a chosen point over each s.
- The second conjunct uses the actual canonical base-changed morphism
  `((Over.pullback ...).map f).left` and equates the set of images of list
  members with `pullback.fst Y.hom ... ⁻¹' S`. The list is not required to
  be distinct. Spec K has a unique point, denoted `default`.
- No nonemptiness condition is imposed on S or zs. If S is empty, the empty
  list is permitted, and equality forces it to be empty. There are no
  separability, smoothness, reducedness, flatness or separation hypotheses.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`:
  `Algebra` and `algebraMap` (through the public dependency imports).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`, literally `IsClosed {x}`.
- `WeilConjectures.AlgebraicGeometry.DensePoints`:
  `Scheme.Hom.baseChangeFieldPoint`, whose signature and docstring identify
  `Scheme.Hom.fieldPoints` as sections and construct their induced sections.
  The underlying `fieldPoints` definition was also read in
  `lean/Comparator/Weil/Definitions.lean`: the required commuting triangle.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  `baseChange_morphism_projections` and its explicit convention of
  `Over.pullback` for base change of a morphism; `pullback.fst` and
  `pullback.snd` are the recorded projections. The `Over.pullback` functor's
  full definition was read in Mathlib.CategoryTheory.Comma.Over.Pullback.

The module privately imports the stated proof dependencies: scheme properties
(sobriety), compact T0 closed-point existence, closed-point residue-field
finiteness, fibre residue arrows, and surjective base change. The affine
pullback, residue-field and fibre modules are already public dependencies
of BaseChangeConventions. `lem-sfb-common-normal-compatible-groups` and
`lem-sfb-normal-field-tensor-rational-points` currently have neither a Lean
record nor a Mathlib match and supply only postponed proof steps, so there
is no module for them to import. They are not needed to type the statement.

Source read: Milne, Algebraic Groups (2017), PDF pp.617–618, printed pp.605–606,
Theorem B.37 Step 2, especially its second paragraph. It explicitly chooses
finite normal K containing all closed lifts' residue fields and retains all
points above the selected target points, as required by the generalized node.

Edge cases checked before writing: empty S; empty X and Y (surjectivity forces
Y empty if X is empty); identity morphisms; a finite inseparable extension
in positive characteristic; nonreduced finite tensor rings; and multiple points
above one closed target point after a separable splitting extension. The list
may contain repetitions. None of these cases is excluded. No statement dispute
or correction was needed; no dependency module or new node was needed.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder` with "A surjective morphism of finite type schemes
  over a field admits rational lifts of all points above a finite set of closed
  points after one finite field extension": eight hits, including
  `Scheme.PartialMap.toRationalMap_surjective`, `pointsPi_surjective`,
  `Scheme.residue_surjective`, and finite fibres. None states the assertion.
- `msearch.py ... leansearch` with "A finite extension of the base field
  simultaneously splits a finite set of closed points and gives rational lifts
  under a surjective morphism of finite type schemes": eight hits concerning
  finite residue extensions, lifting a splitting polynomial, and normality;
  no simultaneous rational-lift theorem.
- `msearch.py ... loogle` with `"Scheme", "RationalPoint", "Surjective"`:
  zero hits.
- `msearch.py ... grep` with
  `rational.*lift|finite.*extension.*rational|finite.*closed.*point` in
  Mathlib/AlgebraicGeometry: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `rational.*lift|finite.*closed.*point` found curve-boundary finiteness,
  individual smooth local lifts and unrelated rational realizations, not the
  simultaneous theorem. Searching the item id found no existing declaration.
- The proposed declaration name was searched in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures`, and `lean/Sheaf`: no match.

## Second reading by Q43

A separate pass by the same dispatcher-started worker reread the node and
signature; no second agent was started, as the dispatch brief forbids that.
The maintainer's independent review follows delivery. This pass checked all
four finite-type binders; the Over commuting triangle; surjectivity of f.left;
finite S consisting entirely of closed points; a finite-dimensional extension
with no normality or separability imposed in the conclusion; the type of each
list element as a section of X_K → Spec K; the universal quantifier over all
points above S; and equality, rather than inclusion, of the list image with
the entire inverse image of S. Both conjuncts use the identical K, algebra
map, projections and canonical base-changed morphism. The empty-list case
is admitted. No mathematical mismatch was found and no statement change was made. The first
compile required an explicit `: Scheme.{u}` annotation on the pullback in the
point quantifier, to prevent Lean from inferring a pullback in Type. Both the
sandbox and the final library module then compiled cleanly with scompile.py
(2.2 s and 1.8 s respectively), with no diagnostics. The node copy differs
from its source only in `lean`; every Lean line is at most 100 columns.
