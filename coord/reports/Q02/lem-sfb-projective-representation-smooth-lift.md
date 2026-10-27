## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveRepresentationSmoothLift` states
`AlgebraicGeometry.ProjectiveRepresentationSmoothLift.smooth_lift` with one `sorry`.
It also supplies two concrete compositions of the existing open/reduction maps and a
`NeZero` instance obtained directly from the already proved `Module.finrank_pos`.
No new mathematical theorem or construction is selected from a bare existence claim.
The natural-language statement and its proof are unchanged.

Source read: Milne, Algebraic Groups (2017), Proposition 18.22 and its proof, printed
pp.392–393; Definition 18.1, p.387; Proposition 18.6(a), p.388. The proof of 18.22 forms
the pullback of SL(V) along the projective representation; 18.6(a) explicitly supplies
the reduced neutral-component step. The source and the accepted node distinguish the
possibly nonreduced pullback from its smooth reduced neutral component.

Hypotheses and terminology, clause by clause:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Nonzero finite-dimensional F-vector space V: `V : Type v`, `AddCommGroup V`,
  `Module F V`, `FiniteDimensional F V`, and `Nontrivial V`. Its universe v is independent
  of u. Every matrix rank is `Module.finrank F V`; `spaceRank_neZero` derives positivity,
  rather than adding a positive-rank hypothesis.
- GL(V), SL(V), and scalar Gm: a choice of basis identifies V with F^n, where
  n=dim_F(V). The statement uses exactly the previously constructed
  `GeneralLinearGroup (LinearGroupSchemes.Index n) F`,
  `LinearGroupSchemes.specialLinear F n`, `LinearGroupSchemes.inclusion F n`,
  and `ProjectiveMatrixCentralCover.scalar F n`. No condition depends on the basis.
  Conversely every input V has such a basis, so this matrix encoding excludes no V.
- PGL(V): `P : Grp (Over (Spec (.of F)))`, quotient map `π`, and `IsMonHom π`.
  `hscalar` says π kills the scalar-orbit relation on every test F-scheme.
  `hquotient` says every scalar-invariant natural map from GL to an fppf sheaf factors
  uniquely through π. Representable presheaves are fppf sheaves by subcanonicity, so
  these are exactly the sheafification universal property of GL/Gm, with π fixed.
  This is a specification of the quotient in the node, not an additional hypothesis
  on a projective representation. It works also for rank one; the existing stronger
  `ProjectiveMatrixCentralCover.Presentation` is restricted to rank at least two and
  therefore cannot be used as the sole interface. Its scalar map is reused directly.
- All algebraic groups affine finite type: `IsAffine P.X.left`,
  `LocallyOfFiniteType P.X.hom`, `QuasiCompact P.X.hom`, and the corresponding three
  instances on G. The corresponding three properties on E and H are conclusions.
- Smooth connected G: `[Smooth G.hom] [ConnectedSpace G.left]`.
- Group schemes and homomorphisms: `Grp`, `GrpObj`, morphisms of `Over (Spec (.of F))`,
  and `IsMonHom`; the input projective representation is `a : G ⟶ P.X` with
  `[IsMonHom a]`.
- P(V) as one-dimensional quotients and O(1) are explanatory conventions in the node;
  neither occurs in an input, output, or assertion of this lifting lemma. No alternative
  projective-space or line-bundle convention is introduced by this module.

Conclusions, clause by clause:

- E=G×_PGL SL: `∃ (E : Grp ...) (p : E.X ⟶ G) (r : E.X ⟶ specialLinear ...),`
  with `IsMonHom p`, `IsMonHom r` and `IsPullback p r a (inclusion ... ≫ π)`.
  The universal property fixes the group law and both projections, up to the unique
  isomorphism of pullbacks. E is not an arbitrary group with two arbitrary maps.
- H=(E_red)^0: the quantified open `U : E.X.left.Opens` has underlying set
  `connectedComponent (GrpObj.onePoint E.X)`. `reducedOpen E.X U` is definitionally
  `Over.mk (U.toScheme.nilradical.subschemeι ≫ U.ι ≫ E.X.hom)`.
  This is (E^0)_red, canonically the same closed subscheme as (E_red)^0: reduction
  preserves the space and commutes with restriction to an open. The output inclusion
  `reducedOpenι` is exactly the composite of those two inclusions.
- Restriction of the group law: `∃ gH : GrpObj (reducedOpen E.X U)` with
  `IsMonHom (reducedOpenι E.X U)`. The inclusion is a closed immersion, hence a mono,
  so this condition uniquely fixes the restricted group structure, including inverse
  and unit. No arbitrary group structure on H is admitted.
- Smooth connected H: `Smooth (reducedOpen E.X U).hom` and
  `ConnectedSpace (reducedOpen E.X U).left`, alongside its affine finite-type clauses.
- Projection q is the first projection restricted to H: every occurrence is the
  actual composite `reducedOpenι E.X U ≫ p`. Its `IsMonHom` evidence is existentially
  bound before taking its group-scheme kernel. No separate unconstrained q is introduced.
- Faithful flatness: `(reducedOpenι E.X U ≫ p).left.appTop.hom.FaithfullyFlat`, the
  exact contravariant coordinate-ring map F[G]→F[H]. This is the recorded ring-hom
  faithful flatness, not surjectivity only on field points.
- Finite multiplicative kernel: `∃ (M : Type u) (_ : AddCommGroup M) (_ : Finite M)`
  and `e : GrpObj.ker q ≅ (diagonalizableGroup F M).X` with `IsMonHom e.hom`.
  The latter is a group-scheme isomorphism; its inverse respects multiplication because
  e.hom does. The existing `diagonalizableGroup` is Hopf Spec of `AddMonoidAlgebra F M`;
  its basis multiplication, coproduct, counit and antipode are exactly those in the node.
- The second projection restricts to rho: its actual composite is `reducedOpenι E.X U ≫ r`,
  and `IsMonHom` of this composite is an output.
- Scalar kernel as a closed subgroup of mu_n: the output `j : GrpObj.ker q ⟶ roots F n`
  has `IsClosedSubgroupScheme j`. Its displayed normalization equates
  `j ≫ rootsInclusion F n ≫ scalar F n` to the kernel inclusion followed by H→E→SL→GL.
  This identifies the subgroup as the scalar kernel scheme-theoretically, with its full
  nilpotent structure, not merely as an abstract embedding in a cyclic group of F-points.
- Projectivization: the final equality is exactly `rho ≫ (SL inclusion ≫ π) = q ≫ a`.
- No prime-to-characteristic assumption occurs anywhere in the signature.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraic-closure node's match explicitly names this predicate).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`; and
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` together with
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `IsMonHom`,
  `GrpObj.ker`, `GrpObj.kerι`, `IsClosedSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, the `Over` encoding.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `roots`,
  `rootsGroup`, `rootsInclusion`, with their polynomial/Laurent quotient definitions.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: `Index`, `specialLinear`, `inclusion`;
  its upstream GL comes from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`.
- `Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover`:
  `ProjectiveMatrixCentralCover.scalar`, reused directly through the new definition node
  with `existing: true`. This public import exposes the existing plain definition.
  `Presentation` and `exists_presentation` remain proof-route material only; the theorem
  node is not in the lifting item's statement dependencies.
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`: `diagonalizableGroup`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme`, `Scheme.IdealSheafData.subschemeι`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint` and the
  neutral-component interface. The existing neutral component is not redefined.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.

The added statement dependencies are the already landed definitions
`def-sc-general-linear-group`, `def-sfb-diagonalizable-group`,
`def-weil-pbc-scheme-reduction`, `def-sc-group-scheme-subgroup`, and the new definition-node binding
`def-sfb-scalar-matrix-inclusion` with `existing: true`. The theorem
`lem-sfb-projective-matrix-central-cover` remains only in the accepted proof dependencies.

Proof imports include the recorded `locallyAlgebraicGroup_identityComponent`,
`GrpObj.finiteTypeGroup_neutralComponent_translates`,
`affineGroupHom_faithfullyFlat_iff_surjective_points`,
`Scheme.Hom.GeometricFiber.exists_apply_default_eq`, and
`Smooth.geometricallyReduced`, plus the pullback, finite, closed-immersion, proper,
quasi-finite and surjective-base-change Mathlib interfaces. The two proof dependencies
`lem-sfb-projective-frames-pgl` and `lem-sfb-split-torus-subgroups-diagonalizable` have no
Lean record and supply no import yet. They remain proof dependencies of the node.
The docstring records all seven accepted proof steps, including the rank-one case,
component-surjectivity argument, faithful flatness, and scheme-theoretic kernel computation.

Edge cases checked:

- dim(V)=1: GL_1=Gm, PGL_1=1, SL_1=1; the universal-property interface still applies,
  E≅G, H≅G, kernel 1=D(0)=mu_1. No `2 ≤ finrank` restriction appears.
- V=0 is excluded precisely by `Nontrivial V`, as the node requires.
- Trivial G and trivial a: E can be nonreduced (mu_p in characteristic p). H is the
  actual reduced neutral component; the statement does not claim E is smooth or reduced.
- n divisible by the characteristic: roots retain their polynomial quotient algebra;
  every sheaf and kernel condition uses all test schemes, including nonreduced ones.
- Empty test schemes are included. Connected G is nonempty by the definition of
  ConnectedSpace; the empty scheme is not inadvertently an admissible connected group.
- Finite M may be the zero additive group. There is no positive-order restriction on M.
- Universes: field and schemes use u; V uses arbitrary v; matrix indices are the
  existing `ULift (Fin n)` in u, so arbitrarily presented finite-dimensional V are allowed.

Searches made before writing (all with the prescribed `msearch.py`):

- LeanFinder, "A projective representation of a smooth connected algebraic group lifts
  to SL after a smooth connected multiplicative isogeny": eight hits, including
  `Rep.diagonal_succ_projective`, `Rep.free_projective`, `Matrix.ProjectiveSpecialLinearGroup`
  and `Projectivization.generalLinearGroup_smul_def`; none states this scheme-theoretic lift.
- Loogle, `AlgebraicGeometry.GrpObj,AlgebraicGeometry.GeneralLinearGroup`: zero hits;
  reports unknown identifier `AlgebraicGeometry.GrpObj` (the correct internal name is
  `CategoryTheory.GrpObj`, read directly in the source).
- Mathlib grep, `projectiveLinear|ProjectiveLinear|multiplicativeIsogeny` in
  AlgebraicGeometry: zero hits.
- LeanSearch, "The projective linear group scheme is the fppf sheaf quotient of GL by
  scalar matrices including rank one": eight hits, abstract matrix PSL and linear-algebra
  projectivization, no PGL group scheme or scalar quotient specification.
- LeanFinder, "The universal fppf sheaf quotient of the general linear group scheme by
  scalar matrices": eight Picard-group/module hits; none is the required notion.
- `tools/blueprint_refs.py search 'scalar quotient'`: zero blueprint matches.
- DAG grep for scalar quotient/sheaf quotient/scalar subgroup found the matrix central
  cover and frames nodes among the related statements; their recorded interfaces were read.
- Project and Mathlib `rg` searches for `projectiveLinear`, `IsScalarQuotient`,
  `projectiveRepresentation`, `ProjectiveRepresentation`, `multiplicativeIsogeny`, and
  the exact item id found no existing lifting statement. They did locate the GL/SL,
  scalar, finite diagonalizable, Hopf diagonalizable, and neutral-component interfaces
  used above. `FiniteDiagonalizableGroupScheme.lean` was read too; the explicit Hopf
  scheme `diagonalizableGroup` is used to match the node's actual group algebra.

Validation: `scompile.py Q02 lem-sfb-projective-representation-smooth-lift` compiles
both the sandbox and final module names cleanly. The initial missing `NeZero` instance
was repaired using `NeZero.of_pos (Module.finrank_pos ...)`, without an extra hypothesis.
No `STATEMENT-DISPUTED` issue and no statement correction.


## Repair of the returned deliveries

1. The original H12/H4 return (5462e02911c9) required a definition-node dependency
for the scalar map rather than citing the central-cover theorem as a statement
prerequisite. The item retains `def-sfb-scalar-matrix-inclusion` in stmt_deps;
`lem-sfb-projective-matrix-central-cover` occurs only in proof_deps. The signature
uses only the existing plain scalar definition, not exists_presentation's conclusion.

2. The return of immutable head 241835c2f50d identified the extracted declaration as
a duplicate of the live scalar declaration. Following its explicit instruction to
import and reuse the existing declaration, this repair removes the sandbox module
ScalarMatrixInclusion, removes the sandbox modification of ProjectiveMatrixCentralCover,
and removes its dependency-node override. The new definition node now records
`existing: true`, `module: Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover`,
`declaration: AlgebraicGeometry.ProjectiveMatrixCentralCover.scalar`, with no file.
The lifting module imports that existing module publicly. No scalar declaration is
added, moved, renamed, or copied, and the central-cover library module is untouched.

The existing live declaration and full coordinate body were checked using
`scompile.py --source Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover`.
It evaluates the GL coordinate algebra at the invertible Laurent scalar tI, exactly
the definition used in hscalar, hquotient and the scalar-kernel clause. The old
extraction would have preserved this body, but the current repair follows the latest
return by retaining the sole declaration in its live location.

Comparison with main and returned work: the retained lifting theorem signature is
byte-identical to the reviewed signature and to lean.statement. The accepted natural
statement, seven-step proof, and proof dependencies are unchanged from main. The only
Lean source delivered now is ProjectiveRepresentationSmoothLift; the new scalar node
only binds an existing definition. Existing-definition reuse is expressly permitted
by brief-stage2 section 5, so no helper module is needed and no declaration collision
can be hidden by renaming. The prescribed wrapper rebases the packet on current main.

## New nodes

`def-sfb-scalar-matrix-inclusion` records the already existing scalar map of Milne
Example 5.49, printed p.111. Its `lean.existing` is true and it names the live scalar
definition directly. The coordinate map sends x_ij to t delta_ij and det inverse to
t^(-r), hence on all test algebras it is z -> zI. Rank one and nonreduced algebras
are included; rank zero is the same existing coordinate construction with trivial
target. The definition depends only on the existing field, group-scheme, Gm and GL
nodes. It does not assume, restate or prove the central-cover theorem.

The three recorded searches are retained verbatim in mathlib_searches. Their verdicts
now correctly record reuse: Mathlib has abstract matrix scalar maps, while the exact
group-scheme map is the existing ProjectiveMatrixCentralCover.scalar. Source and DAG
searches found no separate definition node owning this notion. The definition node
therefore adds the missing DAG binding, with no duplicate mathematical definition.
The source, complete blueprint via chain, edge cases and ordinary group-scheme
universe convention remain as in the prior reviewed packet.

Validation for this repair compiles the lifting module through scompile.py against
the live existing scalar declaration; deliver2.py also checks the existing scalar
binding by a server declaration probe. The dry run checks that no new module declares
scalar and that only the lifting module, its node, the existing-definition binding,
and the report are delivered.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
