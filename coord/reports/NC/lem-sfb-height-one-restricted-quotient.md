## Worker report

The delivery states `AlgebraicGeometry.exists_heightOne_restricted_quotient` in
`Sheaf.AlgebraicGeometry.GroupScheme.HeightOneRestrictedQuotient`. Its only proof is
`sorry`. The real-data helper `restrictedTangentMatrixSpan` is the scalar-extended
matrix view of the given tangent subalgebra; it introduces no independent
mathematical notion and is listed in `lean.declarations`. No statement, proof plan,
or dependency is changed. No dependency module or new DAG node is needed.

Sources read: Milne, Algebraic Groups (2017), printed pp.222--223,
Propositions 11.35--11.37 and Corollary 11.38; printed p.378,
Proposition 17.80 and its proof; Definition 10.39 and Proposition 10.38,
printed pp.205--207. The current blueprint's direct-image proof paragraph (3)
was also read. This item is a supporting node, not the blueprint unit statement.

Hypotheses, clause by clause:

- The field and its algebraic closure are `[Field k]` and `AlgebraicClosure k`.
  The characteristic is `[Fact p.Prime] [CharP k p]`; positive characteristic of a
  field is prime, so this does not exclude a source case.
- `J : Grp (Over (Spec (.of k)))` is the group scheme. Its affineness, finite type,
  smoothness and connectedness are respectively `IsAffine J.X.left`,
  `LocallyOfFiniteType J.X.hom` with `QuasiCompact J.X.hom`, `Smooth J.X.hom`,
  and `ConnectedSpace J.X.left`. Group identity sections ensure nonemptiness.
- The fixed faithful closed representation is `ρ : GeneralLinearGroup.RationalHom
  J.X n` with `[IsClosedSubgroupScheme ρ]`. This class supplies the homomorphism
  and closed immersion. The finite index type `n` encodes the matrix size without
  fixing a rank. Its universe is the same as the field and the group schemes.
- The tangent space is the existing `GrpObj.Lie J.X`, with its canonical
  commutator bracket. The existing `GrpObj.lieIdentityTangentEquiv` identifies
  this with the recorded `schemeTangentSpace` at the identity, with the structural
  residue-field identification. No arbitrary Lie structure is hypothesized.
- `h : LieSubalgebra k (GrpObj.Lie J.X)` supplies precisely a k-linear subspace
  closed under brackets. `hp` says that the differential image of every x in h
  has its matrix pth power again in that image. In a faithful closed rational
  representation this is exactly closure under the canonical restricted power:
  rational differentiation takes the p-fold composite of the left invariant
  derivation of x to `(ρ.differential x)^p`, and the differential is injective.
  This is an equivalent expression of the prescribed operation, with no chosen
  restricted structure and no new differentiation assumption.
- `restrictedTangentMatrixSpan ρ h R` is the R-span of the entrywise scalar
  extensions of the matrices of h. It is exactly the image of `R tensor_k h`.
  Since the faithful differential is injective and k is a field, extension to
  every k-algebra is injective. Therefore matrix conjugation on this image is
  the actual adjoint representation on the scalar-extended tangent space.
- `hAd` requires invariance under conjugation by every `g : points J.X R` for
  every commutative k-algebra R. This is group-scheme adjoint stability, not
  merely invariance under k-points or geometric points. The condition for g
  inverse makes the inclusion an equality.
- The introductory definitions of central tangent vectors, nilpotent groups,
  and tori do not impose extra assumptions in this particular lemma. The node
  never assumes J is nilpotent or that h is central. No such binder was added.

Conclusions, clause by clause:

- `∃ (H Q : Grp ...) (i : H ⟶ J) (q : J ⟶ Q)` supplies the subgroup, target,
  inclusion and quotient homomorphism. `IsClosedSubgroupScheme i.hom.hom` and
  `IsNormalSubgroupScheme i.hom.hom` are the recorded closed/normal predicates.
- `IsFinite H.X.hom` is finiteness of H. Its coordinate ring is
  `Γ(H.X.left, ⊤)`, and `IsLocalRing` and the nilpotence of
  `RingHom.ker (GrpObj.unitSection H.X).appTop.hom` express infinitesimality.
  Pullback of functions along the identity is the counit; its codomain is
  Γ(Spec k), canonically k, so its kernel is exactly the augmentation ideal.
  The displayed `∀ a ∈ ... , a ^ p = 0` is the height-at-most-one assertion.
- `(GrpObj.differential i.hom.hom).range = h` means Lie(H)=h inside Lie(J),
  without a type equality between different Lie algebras.
- `IsAffine Q.X.left`, `LocallyOfFiniteType Q.X.hom`, `QuasiCompact Q.X.hom`,
  `Smooth Q.X.hom` and `ConnectedSpace Q.X.left` are exactly the stated target
  properties. The finite H is automatically affine and finite type over k.
- `IsFppfGroupQuotient i q` is the existing quotient predicate, including the
  scheme-theoretic kernel square. Thus the kernel is the specific H with its
  specific inclusion i. It also states the fppf quotient universal property,
  the intended meaning of quotient homomorphism, rather than an arbitrary map
  with a coincidentally matching differential kernel.
- `IsFinite q.hom.hom.left` and
  `q.hom.hom.left.appTop.hom.FaithfullyFlat` say exactly that the target-to-source
  coordinate map gives a finite faithfully flat module. Affineness of J and Q
  identifies scheme finiteness with finiteness of this coordinate module.
- The injectivity of `x ↦ x ≫ q.hom.hom` for every algebraically closed field
  Ω over k is precisely radiciality on geometric points as defined in the item.
- `((GrpObj.differential q.hom.hom).ker : LieSubalgebra ...) = h` is the tangent
  kernel, with the Lie ideal coerced to its underlying Lie subalgebra.
- `topologicalKrullDim Q.X.left = topologicalKrullDim J.X.left` is the exact
  Krull-dimension equality.
- The final implication has both assumptions of the final clause: conjugation
  acts as the identity on the matrix span over every R, and every element of
  the span over `AlgebraicClosure k` is conjugate by an invertible matrix to a
  diagonal matrix. The latter quantifies over the whole geometric scalar
  extension, not just the scalar extension of each k-rational vector.
- Its conclusions assert `(a ≫ i.hom.hom) * b = b * (a ≫ i.hom.hom)` for every
  k-algebra R, H(R)-point a and J(R)-point b, and the recorded
  `MultiplicativeType.IsMultiplicativeType H`. Hence centrality includes
  nonreduced R and multiplicative type includes nonsmooth finite groups.

Dependency declarations used and read:

- `Field`, Mathlib.Algebra.Field.Defs; `AlgebraicClosure`,
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure.
- `CategoryTheory.GrpObj`, `Grp`, `IsMonHom`, Mathlib.CategoryTheory.Monoidal.Grp;
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`, respective Mathlib
  AlgebraicGeometry.Morphisms modules; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic; `topologicalKrullDim`,
  Mathlib.Topology.KrullDimension.
- `MultiplicativeType.IsMultiplicativeType`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType, with its actual base change
  functor, split torus including rank zero, and closed-subgroup definition.
- `schemeTangentSpace`, WeilConjectures.AlgebraicGeometry.SchemeTangentSpace;
  the canonical group tangent implementation and the linear comparison
  `GrpObj.lieIdentityTangentEquiv`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv.
- `LieRing`, `LieAlgebra`, `LieSubalgebra`, Mathlib.Algebra.Lie.Basic/Subalgebra.
  `GrpObj.Lie`, `GrpObj.differential`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic/Differential.
- The general-linear dependency records
  Sheaf.AlgebraicGeometry.LinearGroupSchemes, whose documentation explicitly
  reuses upstream GL. Accordingly that module is imported, while the GL
  `GeneralLinearGroup`, `RationalHom`, `RationalHom.points`,
  `RationalHom.differential` and `lieAlgebraEquivMatrix` come from the upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear(.Lie) modules.
  There is no private second definition of GL or its differential.
- Proof imports: Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra;
  Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
  (`IsFppfGroupQuotient`, `affine_normal_quotient_geometry`);
  WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
  (`IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact`);
  WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
  (`Scheme.Hom.topologicalKrullDim_eq_of_surjective`);
  Mathlib.LinearAlgebra.Eigenspace.Pi
  (`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`).
  The two proof nodes `lem-sfb-restricted-rational-differentiation` and
  `lem-sfb-height-one-integration-hom-correspondence` have no recorded Lean
  declarations. Their modules cannot be imported yet; they are proof-only,
  not prerequisites to type this statement. The maintainer can add their
  proof imports after their statements land. The full eight-step proof is
  retained in the theorem docstring, including their uses.

Edge cases: h=0 is allowed by the binders and all invariance conditions. Its
integration is H=1 and q=id, with nilpotent zero augmentation ideal, height at
most one, zero tangent kernel and equal dimensions. No nonzero h or nontrivial
kernel assumption appears. Empty matrix indices give the trivial GL and are
harmless (the assertion extends to this representation of the trivial group).
Characteristics 2 and all other primes are allowed. k need not be perfect,
algebraically closed, infinite, or characteristic zero. Geometric semisimplicity
is checked after extending the entire subspace. Arbitrary nonreduced test
algebras and the zero test algebra are included. The test algebra universe
matches the field/scheme universe, so it does not create a vacuous smaller
universe. The fixed algebraic closure has the same universe. Finite type group
schemes always have a faithful representation with a finite index in this
universe. Nilpotent augmentation ideal is ideal-power nilpotence, not merely
elementwise nilpotence.

Searches (all msearch queries used group NC and this item):

- LeanFinder: “An adjoint invariant restricted Lie subalgebra of a smooth
  connected affine group scheme determines a finite radicial quotient with
  height one infinitesimal kernel”: 8 hits, abstract Cartan/Engel/Lie quotient
  or ring infinitesimal results; no group-scheme quotient statement.
- Loogle: `LieSubalgebra, Derivation, IsTriangularizable` (syntax rejected by
  Loogle; not treated as evidence); the subsequent valid query `"isogeny"`
  succeeded with 0 hits.
- LeanSearch: “Restricted tangent subalgebra of a group scheme in a faithful
  representation is closed under matrix pth powers and adjoint invariant under
  algebra valued points”: 8 abstract Lie/module/manifold hits; no match.
- LeanFinder: “Scalar extension of matrix subspace is span of scalar extended
  matrices and conjugation stabilizes Lie subalgebra”: 8 hits, root-system
  conjugation and LieSubmodule.baseChange_top; no existing helper for this
  canonical differential image. The helper is only Submodule.span of that image.
- msearch grep: `restricted.*Lie|height.?one|infinitesimal.*group` in
  AlgebraicGeometry, and `IsRestricted|IsInfinitesimal|IsHeightOne|AdjointStable`
  globally: no quotient/height-one interface; the latter gives restricted power
  series, an unrelated notion.
- rg of WeilConjectures/AlgebraicGeometry/GroupScheme and Sheaf, by restricted
  Lie, height-one, adjoint, and the exact node id: found the canonical Lie,
  differential, and AffineGroupDualNumberCalculus adjoint package, but no target
  theorem. The latter packages adjoint data with normalization in a theorem;
  here matrix conjugation expresses that same action directly without choosing
  data from an existence theorem. rg for the proposed declaration names in
  WeilConjectures, Sheaf and dag/lean_names_upstream.json found no duplicates.

Validation: scompile.py compiled the module both as a sandbox and under its
library module name, cleanly, in 2.0/2.1 seconds. The initial compile found a
parenthesis typo and redundant IsMonHom instance; both were repaired. All
universes and variables are explicit; `autoImplicit false` is set. No local
notation, local instance, arbitrary chosen construction, or additional sorry
helper theorem is present. No statement dispute or node correction is needed.

## Second reading by NC

I reread the node and final module clause by clause in this dispatcher session;
this is the author's second reading, not an independent agent review. The
maintainer's review remains independent, as the assignment requires.

The field/positive-characteristic and smooth connected affine finite-type
hypotheses match exactly. Closed faithful representation is supplied, rather
than an assumed arbitrary matrix map. LieSubalgebra supplies the subspace and
bracket condition; matrix pth closure supplies restricted closure. Invariance
and triviality quantify over every commutative test algebra. The scalar span
is the full geometric h after base change, which prevents accidentally testing
semisimplicity only on k-rational elements. The final conclusion has the
closed normal subgroup, finiteness, locality, ideal nilpotence and pth-power
height, differential image h, smooth connected affine finite-type Q, fppf
quotient with its kernel square, finite faithful flatness, geometric-point
injectivity, tangent kernel and dimension. Both hypotheses and both conclusions
of the final central multiplicative-type clause are present. No h≠0 condition
excludes the stated trivial case.

The second reading checked that `ker` of a Lie hom is a Lie ideal whereas h is
a Lie subalgebra, so the kernel equality explicitly coerces it. The redundant
homomorphism typeclass was removed after the compiler's overlap diagnostic.
The helper uses an actual span and no postponed data. No other mismatch was
found, and no changes were made to the informal node.
