## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousCotangentAssociatedBundle states
AlgebraicGeometry.HomogeneousCotangent.homogeneous_cotangent_associated_bundle. Its only
postponed proof is that theorem, with the complete seven-step DAG proof in its docstring.
Every definition contains real data. The item statement, proof and proof dependencies
are unchanged. Added statement dependencies are the new descent-frame definition and the
already recorded tangent-space and canonical-differential-map nodes used by the signature.

Clause-by-clause reading:

- The field is `F : Type u`, `[Field F] [IsAlgClosed F]`. There is no characteristic binder.
- `G H : Grp (Over (Spec (.of F)))` and `i : H ⟶ G` supply scheme groups and a genuine
  homomorphism. Smoothness, connectedness and affineness of G are the corresponding
  instances; finite type is `LocallyOfFiniteType` plus `QuasiCompact`. H is smooth and
  `IsClosedSubgroupScheme i.hom.hom` is exactly the recorded subgroup predicate.
- Q is an F-scheme with `IsSeparated Q.hom`, `LocallyOfFiniteType Q.hom` and
  `QuasiCompact Q.hom`. The map q is flat and surjective. Finite presentation is the
  convention's three predicates: locally of finite presentation, quasi-compact and
  quasi-separated. `htorsor` is the cartesian square with maps pr_G and (g,h) ↦ gi(h),
  hence exactly G × H ≅ G ×_Q G. Faithful flatness and this relation give the represented
  fppf quotient; no independent quotient assumption or local section is added.
- `Smooth Q.hom ∧ Smooth q.left` are the first two conclusions. The action `a : ModObj G.X Q`
  is a geometric group-scheme action. Its first formula on every test F-scheme pins it to
  left multiplication on the quotient, including on nonreduced tests.
- `GrpObj.Lie G.X` and `GrpObj.Lie H.X` are the existing tangent-at-identity modules.
  Their canonical identification with the specified dual-number tangent spaces is the
  imported `GrpObj.lieIdentityTangentEquiv`. The map from Lie H is the existing
  `GrpObj.differential i.hom.hom`; its injectivity is asserted explicitly. `lieImage i`
  is its actual linear range, not an arbitrary subspace. `quotientLie i` is the actual
  module quotient. The equivalence t from that quotient to the recorded tangent space
  at q(e), with scalars restricted by the structural residue map, gives surjectivity and
  exactness. The following formula pins its composite with mkQ to postcomposition by q
  on actual dual-number tangent points, after the canonical residue-field identification.
  Thus all three arrows of the short exact sequence are specified, not existential maps.
- The basis b of the quotient has `ULift (Fin d)` as its index, so d is exactly its
  dimension (and also the dimension of its dual), not a free rank parameter. The lift
  avoids restricting the scheme universe. No finiteness hypothesis on tangent spaces
  was assumed; the basis is part of the conclusion.
- r is an actual rational H-representation into GL_d, with `IsMonHom r`. Its formula at
  every rational h identifies its action with the existing differential of `conjBy` on
  the quotient. The next formula identifies t with the stabilizer differential. The
  first arrow is the canonical differential of a group homomorphism, which commutes
  with these conjugations by functoriality. Consequently this is an H-equivariant exact
  sequence. These formulas determine scheme morphisms, not just abstract point actions:
  H is smooth of finite type over the algebraically closed F, so H(F) is schematically
  dense, also after any F-algebra extension. The coefficient identities therefore hold
  universally, including on nonreduced test algebras. This density argument uses neither
  characteristic zero nor connectedness of H. It is an equivalent characterization of
  the specified rational action, not a weakening to rational-point representations.
- rV is also a scheme homomorphism, and the equality after EVERY commutative F-algebra
  extension says rV(h) = transpose(r(h inverse)). In the basis dual to b this is exactly
  (h ell)(v) = ell(Ad(h inverse)v), including the sign/inverse convention of the node.
- θ is a frame of q* of the ACTUAL `Q.hom.relativeDifferentials`. The new
  `IsDescentFrame` says θ_gh(w) = θ_g(hw), equivalently (g,w)h = (gh,h inverse w).
  Its equations quantify over every F-algebra, not only fields. This is the associated
  bundle isomorphism expressed in the fully faithful descent category: to identify a
  sheaf E with G ×^H W is precisely to give this frame respecting the fixed descent
  datum. No arbitrary sheaf or arbitrary isomorphism is substituted for Ω, and no
  associated bundle is chosen from mere existence. The general frame definition can
  equally be used with any descended E.
- `IsEquivariantFrame G q a d θ` intertwines the canonical differential pullback of
  each left translation with the frame on G. It holds on all algebra-valued g and
  vectors, for every rational k. Because G is smooth affine finite type over F,
  G(F) is schematically dense universally; the identity is thus the equality of
  algebraic action morphisms, including all algebra-valued k. The differential map
  is the RECORDED canonical relative differential map, transported from tensor to
  ordinary pullback by left-adjoint uniqueness. This specifies the natural cotangent
  action rather than assuming an unconstrained linearization.
- The pairing formula at η[G] fixes the identification of the stabilizer cotangent
  fibre with the dual of the quotient: v applied to dq*(ell) is ell([v]). Thus the
  cotangent isomorphism is the canonical normalized one, rather than an arbitrary
  associated-bundle isomorphism. This also fixes the direction of the action.
- rTop has matrix entry det(rV(h)) over every algebra. Thus it is precisely the
  representation on the top exterior power of V in the wedge of the dual basis.
  θTop frames q* of the recorded `Scheme.Modules.exteriorSheaf Ω d`, and its
  `IsDescentFrame` gives the sheaf of G ×^H exterior^d V. The determinant formula
  on EVERY open and every tuple of sections pins the top-wedge comparison to the
  wedge of θ; it is not an unconstrained line isomorphism. Its empty wedge gives 1.
- `Q.hom.relativeDifferentials.IsFiniteLocallyFreeOfRank d` is constant rank d.
  `SmoothOfRelativeDimension d Q.hom` is the recorded smooth/pure-fibre-dimension
  convention (Stacks 02G2). Over Spec F its nonempty fibre is Q itself, so this is
  the stated pure dimension d. Q is nonempty because q(e) exists.

Dependency declarations read and reused:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Mathlib.CategoryTheory.Monoidal.Grp: GrpObj, Grp; and the recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsClosedSubgroupScheme.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth, SmoothOfRelativeDimension;
  FiniteType/FinitePresentation/Flat/Separated provide the standard properties.
- WeilConjectures.AlgebraicGeometry.Modules.Differentials:
  Scheme.Hom.relativeDifferentials and relativeDifferentialsCongr.
- Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf:
  Scheme.Modules.exteriorSheaf and exteriorSheafSection.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: schemeTangentSpace and
  its canonical additive/residue-field-module instances.
- WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv:
  GrpObj.lieIdentityTangentEquiv; Lie.Ring: tangentPoint; Lie.Differential:
  differential; GroupScheme.Basic: conjBy and onePoint. These are the already
  existing Lie/tangent interfaces, not new copies of these notions.
- Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap:
  Scheme.Hom.relativeDifferentialsPullbackMap. TensorPullbackAdjunction:
  exists_tensorPullbackAdjunction; Mathlib Modules.Sheaf: pullback,
  pullbackPushforwardAdjunction, pullbackComp, pullbackCongr.
- WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf: pullbackFreeIso,
  freeSectionsEquiv; Modules.FreeGenerator: pullbackSection;
  Modules.FreeComplexExact: freeSectionsEquivOpens.
- GeneralLinear.Lie: GeneralLinearGroup.RationalHom, RationalHom.points.
  The new definition uses this existing rational representation interface.

The recorded proof modules are imported privately: Mathlib Proper and
LocalFlatDescent, upstream Mathlib/Morphisms/Smooth,
SmoothRelativeDifferentialsFiniteLocallyFree, Descent, and the landed
SmoothDifferentialsFreeRankFibreDimension. The two proof-only nodes
lem-sfb-rational-tangent-differential-fibre-duality and
lem-trf-relative-differential-sheaf-base-change have no recorded Lean yet and
therefore no module to import. Their notions are not assumptions of this theorem;
the canonical constructions actually needed for the statement already exist.

Edge cases: H=G makes the quotient tangent zero and d=0; θ has zero coordinates,
while θTop has rank one. Fin 0 has empty determinant 1, so the degree-zero
normalization is O_Q and sends 1 to 1. H=1 gives the usual translation frame
of Ω_G; finite smooth (possibly disconnected) H is allowed. No division by the
characteristic occurs. The empty Q cannot satisfy the hypotheses because e maps
through q. All commutative F-algebras are tested in universe u, the same as F
and schemes; this includes the coefficient and coordinate algebras and their
nonreduced extensions. There is no smaller independent test universe.

Searches (all run through msearch.py where applicable): LeanFinder query
"The cotangent bundle of a smooth homogeneous space G/H is the associated bundle
of the dual of Lie G modulo Lie H" returned only differential-geometric tangent
bundles. Loogle "AlgebraicGeometry, associated, cotangent" returned zero hits
(unknown namespace query); it is not evidence of absence by itself. LeanSearch
"associated vector bundle descent homogeneous space cotangent representation"
returned topology/manifold bundles and standard-smooth algebraic cotangents.
Mathlib grep "associatedBundle|associated_bundle|homogeneous.*cotangent|cotangent.*homogeneous"
returned zero hits. The same rg in WeilConjectures/ and Sheaf/ returned no exact
statement, and grep of the item id in WeilConjectures/ returned none. Broader
searches found the associated CHARACTER line bundle presentation and rational
representation interfaces, which were read; the former does not cover general
finite-dimensional representations. DAG search and blueprint_refs.py search
"associated bundle" found no general descent-frame node. Further searches for
the new frame are recorded verbatim in its mathlib_searches.

Source checked directly: local Milne PDF, printed pp.142--143 and pp.389--390,
including the torsor cartesian square, fpqc descent footnote, stabilizer fibre
construction, and inverse right-action convention. The vector and exterior-power
extension is already explicit in this item's accepted seven-step proof.
No STATEMENT-DISPUTED fault or statement correction.

## New nodes

`def-sfb-associated-vector-bundle-frame` introduces free, frameAt, framedVector,
and IsDescentFrame in its own module. It specifies the actual trivial bundle,
canonical pullback of its frame, and the universally tested right descent
relation for an existing rational H-module. Its source is Milne 18c and Stacks
023T. It does not construct a second representation or pullback. LeanSearch
returned topological bundles; LeanFinder returned general free-pullback and
condensed-module constructions; Mathlib grep found no declaration. Source/DAG
searches found only the rank-one character specialization. The definition has
no sorry and its data are explicit; in the item the actual Ω and exterior Ω
are the descended objects, so no object is selected from mere Nonempty.

## Second reading by Q22

I reopened the node and both modules for a separate clause audit. The fixes from
that rereading were: make q-invariance explicit in IsDescentFrame before the
transported equality; use η[G] in the canonical fibre pairing rather than the
definitionally different affine Spec F point; expose the action import publicly;
spell finite type/presentation by the project's conjunctive conventions; and
remove a named ordinary/tensor comparison in favor of its existing adjunction
expression to avoid introducing a second general comparison notion. I checked
all the clauses against the correspondence above, including the contragredient
inverse, all-algebra descent, characteristic independence, and the empty wedge.
No other worker was started, as the dispatcher explicitly forbids it; the
independent reading is the maintainer's delivery review, not a claimed second
agent review here.
