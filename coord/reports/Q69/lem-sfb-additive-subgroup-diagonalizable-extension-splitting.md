## Worker report

The module `Sheaf.AlgebraicGeometry.AdditiveSubgroupDiagonalizableExtensionSplitting`
states `AlgebraicGeometry.additiveSubgroup_diagonalizable_extension_splits`.
Its sole theorem has proof `by sorry`; there are no new Lean definitions or other postponed
claims. One new definition node registers two existing coordinate definitions. Its docstring reproduces all eight proof steps of the DAG node. The node's
statement, proof and proof dependencies are unchanged.

Source read: Milne, Algebraic Groups (2017), Theorem 15.34(d), printed p.319
(PDF p.331), with the complete proof on that page, and Theorem 16.26(a), printed
pp.332--333 (PDF pp.344--345). The former applies to an arbitrary algebraic subgroup
of Gₐ with an action extending linearly to Gₐ over an algebraically closed field;
the latter explicitly applies it to the pullback extension. Neither requires the
kernel, middle group or diagonalizable quotient to be smooth or connected.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
  `IsAlgClosed` is exactly the algebraically closed part of the recorded
  def-weil-algebraic-closure match; an additional chosen algebraic closure is unnecessary.
- The finitely generated abelian group is `(M : Type u) [AddCommGroup M]
  [AddGroup.FG M]`. Its specified group scheme is the existing
  `diagonalizableGroup k M`, defined as the Hopf spectrum of `AddMonoidAlgebra k M`.
  The canonical Hopf structure has exactly the displayed monomial multiplication,
  comultiplication, counit and antipode. Finite generation gives finite type, and
  the construction is affine; these are properties of this specified D(M), not
  extra conditions on an arbitrary quotient group.
- `(N E : Grp (Over (Spec (.of k))))` supplies actual group objects over k and their
  group structures. `[IsAffine N.X.left]`, `[LocallyOfFiniteType N.X.hom]`,
  `[QuasiCompact N.X.hom]` and the corresponding E instances render the affine
  finite type hypotheses. Finite type is locally finite type plus quasi-compactness,
  as the dependency record instructs. No smoothness, reducedness or connectedness
  hypotheses occur.
- `(j : N.X ⟶ additive k) [IsClosedSubgroupScheme j]` realizes the specified closed
  additive subgroup, with its actual inclusion. `additive k` is Spec k[y] with the
  additive Hopf law from def-sc-gm-ga, not an abstract group with the same k-points.
- `(chi : (diagonalizableGroup k M).X ⟶ multiplicative k) [IsMonHom chi]`
  is precisely the group-scheme character. `multiplicative k` is Spec k[t,t⁻¹].
- `hstable` quantifies over every commutative k-algebra R, every d in D(R) and x in R.
  Its premise `∃ z, z ≫ j = additiveCoordinatePoint k R x` means x belongs to N(R).
  Its conclusion says chi(d)x belongs to the same subgroup, using the existing
  `multiplicativeCoordinateValue` to evaluate the Laurent coordinate. Thus it
  expresses exactly stability under scalar multiplication by chi.
- `(i : N ⟶ E)` is a bundled group-scheme homomorphism; the closed and normal
  subgroup scheme instances are the recorded dependency's own definitions.
  They retain injectivity on points over all k-algebras, a closed immersion of
  underlying schemes, and normality of the image.
- `(q : E ⟶ diagonalizableGroup k M)` is the specified quotient homomorphism.
  `hquot : IsFppfGroupQuotient i q` is the existing quotient presentation: its first
  clause is the scheme-theoretic kernel square; its local-surjectivity clause uses
  `Scheme.fppfTopology.over`; its canonical coequalizer is the pointwise right-coset
  presheaf; and its universal arrow is its fppf sheafification represented by D(M).
  The included torsor isomorphism identifies the canonical kernel-pair projections
  with (e,n) ↦ e and (e,n) ↦ ei(n). This is the standard torsor identification for
  the same quotient, not a demand for a pointwise or globally trivial torsor.
- `hconj` quantifies over every such R, e in E(R), x in R, and z in N(R) with
  coordinate x. It provides w in N(R) whose coordinate is chi(q(e))x and states
  `e * (z ≫ i.hom.hom) * e⁻¹ = w ≫ i.hom.hom`. Since j is a closed subgroup
  embedding, w is unique. This is the node's exact conjugation identity; the
  existential simply makes its otherwise implicit scalar element of N(R) explicit.
  Multiplication and inverse on Hom sets are the group-object operations from
  `CategoryTheory.GrpObj.Hom.group`, opened by the existing MonObj scope.
- The conclusion `∃ s : diagonalizableGroup k M ⟶ E,
  s ≫ q = 𝟙 (diagonalizableGroup k M)` gives a homomorphism of k-group schemes,
  not a section only of schemes or of k-points. Composition is Lean's left-to-right
  convention, so this equality is exactly q ∘ s = id_D.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`, as specified in the algebraic-closure node's match.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`; the group-scheme dependency's
  full specialization is documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
  Closedness uses `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.IsClosedImmersion`
  (the declaration namespace is `AlgebraicGeometry`).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.affine`, `additive`, `multiplicative`, and their canonical
  group structures. This is the existing def-sc-gm-ga dependency.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `diagonalizableGroup`.
  Added the already landed `def-sfb-diagonalizable-group` to stmt_deps.
- `Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient`:
  `StandardGroupSchemes.additiveCoordinatePoint`, `multiplicativeCoordinateValue`;
  the theorem `exists_additiveSubgroup_polynomial_quotient` remains a proof input.
  The new definition node `def-sfb-standard-group-coordinate-points` registers these
  plain coordinate definitions and is cited in stmt_deps. The quotient theorem is
  retained only in proof_deps; neither helper uses it or a .choose.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`; `affine_normal_quotient_geometry` supplies the quotient
  construction in the proof. The already landed definition node
  `def-sfb-fppf-group-quotient-presentation` is now cited in stmt_deps, while
  `lem-sfb-affine-normal-quotient-geometry` remains only in proof_deps.
- `WeilConjectures.RingTheory.FaithfullyFlat.Amitsur`:
  `Module.FaithfullyFlat.exact_amitsurComplex`, imported without public because it
  is only a proof dependency. Its augmentation exactness supplies both descent steps.

The statement dependencies added are the two landed definition nodes
`def-sfb-diagonalizable-group` and `def-sfb-fppf-group-quotient-presentation`, plus
the new existing:true coordinate definition node. Both theorem nodes identified in
the return are absent from stmt_deps and unchanged in proof_deps. No dependency
module is needed. There is no statement correction or mathematical dispute.

Edge cases checked before writing: M = 0 (trivial quotient); torsion M and specifically
M = Z/p in characteristic p (nonreduced D = μ_p); N trivial; N = Gₐ; N = α_p or
another finite nonreduced additive subgroup; finite étale additive subgroups; chi
trivial; arbitrary characteristic; nonreduced and zero test algebras. The character
group is finitely generated but need not be free or finite. No case is excluded.
In the zero algebra all coordinates and all affine points give the unique required
identities. A test algebra's universe is the field/scheme universe u, as in the
recorded subgroup API; there is no independent smaller test universe making the
hypotheses vacuous. The schemes themselves are in Scheme.{u}.

Searches (also recorded by msearch.py in searches.jsonl):

- LeanSearch: "Extensions of diagonalizable algebraic group schemes by subgroups of
  the additive group split over an algebraically closed field" returned eight
  abstract AddGroupExtension declarations; none constructs a group-scheme splitting.
- LeanFinder: "Over an algebraically closed field an extension of a diagonalizable
  group scheme by a closed subgroup of the additive group with linear scalar
  conjugation splits" returned GroupExtension.Splitting, conjugation of abstract
  splittings, the canonical semidirect-product splitting and unrelated field results.
  These do not assert the present existence theorem.
- Loogle: "GroupExtension.Splitting, GrpObj" returned no hits, with GrpObj unknown to
  that search service; the relevant GrpObj declaration was inspected directly instead.
- msearch grep in Mathlib/AlgebraicGeometry: "diagonalizable|extension.*splitt|
  splitt.*extension" returned no hits. Direct rg over all Mathlib, WeilConjectures,
  Sheaf and dag/lean_names_upstream.json found no theorem with the proposed name or
  the target combination of additive kernel and diagonalizable splitting.
- Direct rg over Sheaf and WeilConjectures for diagonalizable/group-algebra constructions
  found the landed DiagonalizableGroup module and its DAG node, which are reused.
  Inspection found the already landed quotient interface and polynomial-quotient
  coordinate helpers, which are reused too. No private copy is introduced.
- The item has no released repair note. The current blueprint latest tree has no
  separate item text; the node's explicit source is the Milne theorem read above.

Validation: every compiler invocation uses scompile.py. The initial compile identified
that Hom-set group operations require the existing `CategoryTheory.MonObj` scope;
opening that scope fixes the presentation without changing the signature. Final
compile and delivery preflight results are recorded below.

## Second reading by Q69

This is the author's second reading, not an independent-agent review: the dispatcher
brief prohibits starting other agents and assigns independent review to the maintainer.
With the node and module open, I checked the algebraically closed field, FG abelian
character group, exact Hopf-spectrum D(M), affine finite-type N and E, actual closed
embedding in Gₐ, homomorphic character, closed normal inclusion in E, fppf quotient
with its schematic kernel, scalar stability on all test algebras, the precise
conjugation identity, and a bundled group-homomorphic right inverse.
The existential w in hconj is the unique scalar-multiple point by the injective j;
it does not add a new action or an arbitrary map. The conclusion composes s then q,
which is the required order. The canonical quotient interface does not require
surjectivity on R-points or a scheme section as an assumption. The finite torsion
and nonreduced cases survive every binder. No mismatch with the node was found.
No definitions, arbitrary choices, added smoothness, or omitted conclusion clauses
remain. Only the existing scoped point-group instance needed adjustment after the
first compiler run. The definition nodes for the three reused interfaces are cited in stmt_deps;
all original node fields other than stmt_deps and lean are preserved.

Final scompile.py: PASS for both the sandbox probe and the actual library module;
no errors or warnings (1.6 s and 1.7 s respectively).

## New nodes

`def-sfb-standard-group-coordinate-points` records the two existing plain definitions
`AlgebraicGeometry.StandardGroupSchemes.additiveCoordinatePoint` and
`AlgebraicGeometry.StandardGroupSchemes.multiplicativeCoordinateValue` in
`Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient` with existing:true.
The first is contravariant Spec of polynomial evaluation y ↦ x; the second evaluates
the Laurent coordinate t under the coordinate algebra map of g. Its sole statement
dependency is def-sc-gm-ga, which supplies the underlying groups, affine schemes and
coordinate maps. The source is Milne Examples 2.1--2.2, pp.39--40, Example 14.40,
p.292, and Theorem 15.34(d), p.319; the current blueprint def-sc-gm-ga also specifies
these exact polynomial and Laurent coordinates. LeanSearch returned Laurent evaluation
and general affine coordinates; LeanFinder returned general affine-space coordinate
maps; Mathlib grep returned no specialized definitions. The project grep found precisely
the two existing definitions. Blueprint search returned the underlying group node but
no coordinate interface node. All search outputs are recorded in mathlib_searches.
This registers existing data, introduces no module, and assumes no quotient theorem.
The ancestor query returned None, as for the item's existing blueprint.from.node.

## Returned delivery repair

H2, immutable returned head 533ef8693436: removed
`lem-sfb-affine-normal-quotient-geometry` and
`lem-sfb-additive-subgroup-polynomial-quotient` from stmt_deps. Replaced the former
by the existing Q95 definition node `def-sfb-fppf-group-quotient-presentation` and
the latter by the new existing:true coordinate definition node described above.
Both theorem nodes remain in proof_deps, with the original proof steps unchanged.
The item Lean file and signature are byte-identical to the reviewed delivery.
The sandbox node was refreshed from current main before reapplying only lean and
the repaired stmt_deps. This is a definition-ownership correction, not a change to
the mathematical statement or hypotheses.

Second reading of the repair: opened the quotient definition node, its full predicate,
the coordinate helper definitions and their docstrings, the item node and its Lean
signature. The quotient node matches precisely the predicate in hquot. The new node's
first clause is map k (Polynomial.aeval x); its second is the algSpec preimage of g
applied to LaurentPolynomial.T 1. The returned report's incorrect claim that these
helpers require theorem nodes in stmt_deps has been removed. Neither definition
uses a theorem's chosen object. No mathematical or Lean change was needed. The
original clause and edge-case review remains applicable, including nonreduced D,
N = Gₐ or α_p, and the zero test algebra. No other numbered return point was given.

Repair validation: scompile.py passed (sandbox 1.6 s; library 1.7 s), with no errors
or warnings. The first dry run required the current schema field import_flags on
the new node; added its empty list and reran the dry run.
