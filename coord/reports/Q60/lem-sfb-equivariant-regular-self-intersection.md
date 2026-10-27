## Worker report

Q60, 2026-10-24. The delivery states
`AlgebraicGeometry.EquivariantCoherent.equivariant_regular_self_intersection`
in `Sheaf.AlgebraicGeometry.EquivariantRegularSelfIntersection`. Its only theorem proof is
`sorry`. The definitions have real quotient, sheaf, functor and comparison data; no data is
postponed. The original item's statement, proof, sources and proof dependencies are unchanged.
Three new definition nodes are added to its statement dependencies.

Hypothesis-by-hypothesis correspondence:

- `F : Type u`, `[Field F]` is the field. `G Y W : Over (Spec (.of F))` are the actual
  schemes over F, using the allowed bundled-over convention.
- `[GrpObj G]` is the recorded group-scheme definition. `[ModObj G Y]`, `[ModObj G W]`
  are Mathlib's scheme group actions. `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom]`
  and `[QuasiCompact G.hom]` say affine finite-type group scheme, without any smoothness,
  connectedness, characteristic or reductivity restriction.
- `[IsSeparated Y.hom]`, `[LocallyOfFiniteType Y.hom]`, `[QuasiCompact Y.hom]` say exactly
  separated finite type. No extra hypothesis is imposed on W: it is already closed in Y.
- `i : W ⟶ Y`, `[IsModHom G i]`, `[IsClosedImmersion i.left]` give the equivariant closed
  immersion, over F.
- `c : ℕ` and `hregular` express a uniform bound. For EVERY `w : W.left` there is an
  affine open `U : Y.left.affineOpens` containing `i.left w` and a list `f` of its ring
  sections, with `f.length ≤ c`, the EXACT recorded `RingTheory.Sequence.IsRegular`
  predicate, and `Ideal.span {x | x ∈ f} = i.left.ker.ideal U`. The condition is at points
  of W only, including the empty list and the vacuous condition for empty W. The theorem
  holds for any witnessing bound c, equivalent to the node's existence of a uniform bound.
- The `HasDerivedCategory.{w}` family is the project's explicit derived-model convention;
  w is independent of u, and no universe equality is imposed.

Clause-by-clause correspondence:

- `ActionGroupoidModel` uses the actual action/pr2 arrows, the literal identity and inverse,
  and composition pinned on every test scheme to multiplication of the group coordinates.
  `Scheme.IsGroupoid` supplies the remaining coordinate, identity, inverse and associativity
  equations. The model is asserted to exist in the conclusion, not an extra input hypothesis.
- `Coherent D` is the full subcategory of the RECORDED `Scheme.GroupoidModule` with the
  exact `RingedSpace.IsCoherent` property. This uses the dependency's newly exposed exact
  coherence interface (01BV), not merely quasi-coherence plus finite type. The groupoid
  category already enforces quasi-coherence, identity and actual pullback cocycle.
  `linearization` has direction `a* M ≅ pr2* M`; its inverse is the geometric fibre action.
- `GZero D` is the actual free abelian quotient by equivariant isomorphism and ALL equivariant
  short-exact-sequence relations. Exactness is checked on the underlying module arrows.
  `classOf` is the canonical quotient map. There is no rationalization or completion.
- `RationalModule` has an actual finite-dimensional ModuleCat object and an F-linear
  coordinate coaction, satisfying the existing `HopfAction.Counital` and `Coassociative`
  equations. Its relation subgroup uses equivariant linear isomorphisms and injective,
  surjective exact pairs. `RepresentationGZero` is the analogous integral quotient.
  `coordinateHopf` only transports the existing canonical `affineCoordinateHopfAlgebra`
  from its unbundled-asOver interface to the given bundled Over object; it is not an
  arbitrary Hopf structure. `IsRepresentationRing r` requires the original additive group,
  tensor multiplication and the trivial one-dimensional unit, and existence of their
  normalized representatives.
- `IsAssociated` identifies the underlying bundle with the ACTUAL pullback of `tilde V`
  from Spec F. On every finite presentation `ρ(v)=Σ vi⊗ci`, the inverse linearization
  sends the pr2-pullback of the constant v section to `Σ ci · a*(vi)`. Coefficients are
  pulled back by the first projection to G. This fixes the y-to-gy convention.
  `IsRepresentationAction F D r m` is an actual Module structure, normalized by tensoring
  with these associated bundles. It also asserts existence of associated and tensor
  representatives, so the normalization is not vacuous.
- `immersionTor i M q = H^(-q)(derivedPullback i (M[0]))`, using the recorded derived
  extension-of-scalars functor, is Tor on W. `IsTor` identifies the representative with this
  object AND intertwines the actual induced linearization. The latter is built from the
  equivariant action/projection squares, `recordedDerivedPullbackComposition`, and exact
  derived-pullback cohomology comparisons. `FlatDerivedModel` retains the original universal
  counit normalization, preventing arbitrary flat comparisons. All four flat models are
  asserted to exist, not assumed as additional geometry.
- The first two conjuncts after gysin/push/lambda give a coherent equivariant realization
  for every q and vanishing for `c < q`. The next conjunct normalizes `gysin` on every
  representative family by `Σ q : Fin(c+1), (-1:ℤ)^q.val • classOf (T q)`.
  `gysin : GZero DY →+ GZero DW` says this formula descends to an additive homomorphism.
  The following equality for every `a : RepresentationGZero ...` and `b : GZero DY`
  is exactly R(G)-linearity using the two already normalized module structures.
- `IsPushforward i N M` identifies M with the actual sheaf pushforward by requiring its
  adjoint is invertible and its counit equivariant. Existence for every N and normalization
  `push [N] = [M]` specify the usual induced additive pushforward, not an arbitrary map.
- `IsIdeal i.left K` realizes the kernel ideal module, with an equivariant inclusion into
  the canonically linearized structure sheaf. `IsPullback i K N` realizes the induced
  conormal `i* I = I/I²`, using the actual pullback and its equivariance square.
  `IsLocallyFree` and the coherence already in N give locally FINITE free. Exterior
  representatives use the existing sheafified exterior-power construction, with comparisons
  normalized on wedges and its induced equivariance on all opens. Existence, local freeness
  and zero above c are stated. The lambda endomorphism is normalized by the alternating sum
  of tensoring EVERY coherent module with these exterior representatives. Existence of all
  coherent tensor representatives is already part of `IsRepresentationAction`.
- `∀ alpha, gysin (push alpha) = lambda alpha` is the formula for every integral class,
  not only generator classes. `lambda` is the operator denoted by multiplication with
  `λ₋₁(N∨)` in the node; no ring structure on coherent G-zero is assumed.
- The final conjunct is for every coherent equivariant E with `IsLocallyFree (underlying E)`:
  an induced pullback representative exists and for every such representative
  `gysin [E] = [Ew]`. Coherence makes the locally free module locally finite free.

Dependency declarations used (full signatures and docstrings were read):

- Mathlib `Field`; `CategoryTheory.GrpObj`, `ModObj`, `IsModHom`, cartesian monoidal
  operations in `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod/Grp/Over`.
- `Mathlib.AlgebraicGeometry.Scheme`, `IsClosedImmersion`, finite-type and separated
  morphism predicates; `RingTheory.Sequence.IsRegular` in
  `Mathlib.RingTheory.Regular.RegularSequence`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing
  `AlgebraicGeometry.RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`.
  The original `IsQuasiCoherentFiniteType` was inspected; the final delivery uses the exact
  coherent predicate now exposed by the recorded dependency.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`;
  `Sheaf.AlgebraicGeometry.SchemeGroupoidModule`: `Scheme.GroupoidModule` and its morphisms.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`, `tensorPullbackSection`.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`:
  `Scheme.Modules.module_pullback_tensor`, with its section normalization;
  `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit`; `WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower`:
  `Scheme.Modules.exteriorPower`, `wedge` (existing sheafification construction).
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure` and `DerivedPullback`:
  the shared derived categories and actual derived extension of scalars;
  `DerivedPullbackRecordedComposition`: `recordedDerivedPullbackComposition` and
  `recordedDerivedPullbackCounit`. ExactFunctor supplies the exact-functor-derived,
  single-object and homology comparison isomorphisms.
- `Sheaf.RingTheory.HopfActionModuleData`: `Counital`, `Coassociative`,
  `tensorCoefficients`; `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`:
  `HopfAction.affineCoordinateHopfAlgebra`; Mathlib `tilde`, `tilde.toOpen`;
  `WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison`:
  `Scheme.Modules.tensorPullbackTopSection`.
- Available proof-dependency modules are imported plainly in the theorem module, including
  regular Koszul resolution, annihilated pushforward, noetherian coherence, finite
  pushforward and canonical conormal flat base change. The two proof-only Tor-calculus and
  coefficient-Tor DAG nodes have no recorded Lean module and are not needed to TYPE this
  theorem; their mathematical arguments remain fully recorded in the theorem docstring.

Edge cases checked: empty W makes hregular vacuous and every module class on W zero;
no nonempty hypothesis is imposed. For c=0 the sum is indexed by Fin 1, the conormal is zero,
exterior degree zero is the unit, and clopen/codimension-zero immersions are included.
The empty regular list in a nonempty affine chart uses the recorded proper-quotient regular
predicate; a point-containing affine chart is nonempty. W=Y and i=id give the identity
formula. Zero representations/modules are allowed, including the exact-sequence relations.
The action may be trivial; G may be nonreduced in positive characteristic. The construction
uses action and projection flatness over a field, with no invariant regular generators.

Searches: `msearch.py` LeanFinder, Loogle, LeanSearch and grep calls are recorded verbatim
in the new nodes' `mathlib_searches` and the sandbox search log. The coherent-G-zero query
returned generic monoid group completions and abstract-group/sheaf exact-sequence results;
none states this quotient or self-intersection formula. The rational-coaction query returned
`Coalgebra.Repr` (a finite expression of a coalgebra element), `CoalgCat.ofComonObj` (coalgebra
objects), and abstract-monoid `FDRep`; none is a rational coordinate-comodule Grothendieck
ring. Loogle `"comodule", "coaction"` and the RingTheory grep gave zero hits. Searches of
Mathlib AlgebraicGeometry, `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json`
and DAG definitions found the groupoid and Hopf interfaces reused above but no required
G-zero, representation quotient or normalized immersion-Tor notion. Blueprint searches
`equivariant coherent` and `Tor linearization` gave zero matches. `rational representation`
gave five algebraic-group/Lie-algebra nodes, specialized to characteristic zero or matrix
representations, not this arbitrary-field group-scheme coaction quotient.

The recorded `def-wf-algebraic-representations` was also checked: its
`GeneralLinearGroup.standardRepresentation` is the representation of k-points of a
closed matrix subgroup on k^n. It does not supply the required coordinate comodules
for arbitrary affine group schemes or their exact-sequence quotient. The coordinate
Hopf structure is reused from the newly recorded `def-sfb-affine-coordinate-hopf-algebra`.

No statement correction, STATEMENT-DISPUTED claim or source fault is asserted. The node
correctly labels its equivariant self-intersection prerequisite as agent-supplied; the
unavailable Thomason paper is not claimed to have been consulted. Local source checks used
Stacks `lemma-regular-koszul-regular`, `lemma-H1-regular-quasi-regular`, `definition-tor`,
and `lemma-conormal-functorial-flat` in the supplied literature.

## New nodes

- `def-sfb-equivariant-coherent-gzero`, module `EquivariantCoherentGZero`: actual action
  groupoid/coherent category, integral quotient, canonical equivariant tensor, pullback,
  pushforward, ideal, unit and exterior operation predicates. It reuses the landed groupoid
  category rather than creating another identity/cocycle formalism.
- `def-sfb-equivariant-immersion-tor`, module `EquivariantTorLinearization`: actual derived
  immersion Tor and counit-normalized induced linearization. This definition asserts no
  coherence, boundedness or self-intersection theorem.
- `def-sfb-rational-representation-gzero`, module `RationalRepresentationGZero`: actual
  finite-dimensional coordinate comodules, exact-sequence quotient, tensor-normalized ring
  structure and associated-bundle action predicates. It supplies the missing group quotient
  rather than using representations of the abstract group of rational points.

All new nodes share the item's chapter/unit and ancestry and contain the required searches.
The item cites all three directly. No dependency node is modified.

## Second reading by Q60

I reread the item and the four Lean files clause by clause after drafting. As this dispatcher
brief expressly prohibits starting agents, this is my own second reading; the maintainer's
independent delivery review remains separate.

The reading caught an important interface update: the coherent dependency now exposes the
exact 01BV predicate, so I replaced the draft's quasi-coherent/finite-type restriction with
`RingedSpace.IsCoherent`. It also checked that the same isomorphism to the structure sheaf
both normalizes its unit linearization and receives the ideal inclusion; otherwise the ideal
predicate could have admitted an incorrect twist. In the representation bundle formula I
checked that the INVERSE of beta acts on pr2 constants, giving y-to-gy. In Tor I checked both
recorded composition directions and the final flat-homology inverse. In lambda I checked
that tensoring is over O_W and the classes belong to DW, whereas the gysin input belongs to
DY; these are explicit in the final signatures. The finite sum contains q=0 and q=c. Every
operation-normalization predicate is accompanied by existence of representatives in the
theorem, so none of its formulas can be vacuous. No hypothesis or conclusion of the source
node was dropped or changed.

Validation: all four files were compiled separately with `scompile.py`, within the
60-second limits. The scoped heartbeat annotation concerns the large dependent signature;
it does not change the time limit or any mathematical hypothesis. Delivery preflight and
its fresh per-file compile are run through `deliver2.py --no-push`.
