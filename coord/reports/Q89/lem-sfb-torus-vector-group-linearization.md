## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusVectorGroupLinearization`
states `AlgebraicGeometry.torus_vectorGroup_linearization`, with its sole proof
`sorry`. Its helper `AlgebraicGeometry.additivePowerPointCoordinate` has actual
data: compose the product projection with the point, pull back the polynomial
coordinate X, and apply `Scheme.ΓSpecIso`. There is no chosen unspecified map.

Source read: Conrad--Lichtenstein, Linear Algebraic Groups I, Appendix D.3,
proof of Theorem D.3.2, printed pp.86--87, at
https://math.stanford.edu/~conrad/252Page/handouts/alggroups.pdf . The paragraph
beginning “Now we are in the case that U is a vector group” explicitly obtains
an isomorphism with Ga^N making the torus action linear. In characteristic p
it invokes CGP B.4.3 and splitness of the trivial-action factor. The theorem
docstring contains all six steps of the node's coordinate/Frobenius-module proof.
No node statement was corrected, and no mathematical defect was found.

Hypothesis and clause correspondence:

- Field k: `(k : Type u) [Field k]`, using `Field` (def-weil-field).
- Nonnegative d and s: `(d s : ℕ)`, with no positivity assumptions.
- C an affine finite-type k-group: `C : Grp (Over (Spec (.of k)))`,
  `[IsAffine C.X.left] [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]`.
  These are the recorded group and finite-type conventions, without assuming
  perfectness, characteristic zero, or algebraic closedness.
- C isomorphic as group scheme to Ga^d: `hC : Nonempty ((∏ᶜ fun _ : Fin d ↦
  Grp.mk (StandardGroupSchemes.additive k)) ≅ C)`. Products are in group schemes,
  not products of sets or of rational points. This determines the additive law.
- E = Gm^s: `MultiplicativeType.splitTorus k s`, the recorded finite tensor
  product of the multiplicative group, with the trivial group in rank zero.
- Algebraic action and action identities: `action : ModObj E.X C.X`.
  Its data are a morphism E × C -> C in Over(Spec k); its two axioms are the
  identity and multiplication action diagrams. No abstract point action is used.
- Action by group automorphisms after every algebra extension: `hAut` states
  preservation of multiplication for every commutative k-algebra R and every
  e, x, y over R. The action identities and the inverse e^(-1) already give
  invertibility, so a separate invertibility hypothesis would be redundant.
- W of dimension d: use the witness W = `Fin d → k`. Its scalar extension has
  coordinate module `Fin d → R`; the finite product of Ga is V(W). This is the
  particular W used in the node's own proof, not a restriction on C or its action.
- Group-scheme isomorphism a: the first existential variable is the isomorphism
  `a : (∏ᶜ fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k)) ≅ C`.
  It is not required to equal the initial isomorphism in hC and therefore may
  change additive polynomial coordinates, not merely a basis of a fixed module.
- Algebraic group homomorphism rho: the second existential variable `ρ` maps
  E.X to `GeneralLinearGroup (ULift.{u} (Fin d)) k`; `IsMonHom ρ` is exactly the
  group homomorphism condition. GL is the affine group scheme, not GL(k).
- Equivariance for every R, e, w: for an arbitrary `x : Spec R -> C` write
  w = a^(-1)(x). The conclusion equates every coordinate of a^(-1)(e.x) with
  the matrix product rho_R(e) a^(-1)(x), as a sum over `Fin d`. Since a is an
  isomorphism, x ranges over exactly the images of all w. Product projections
  and the affine-line coordinate separate points, giving precisely
  a_R(rho_R(e)w) = e.a_R(w), without any missing nilpotent tests.
- V(W)(R) and GL(W)(R): the product of the recorded additive groups represents
  coordinatewise addition on R^d; `GeneralLinearGroup.homMulEquiv` identifies
  GL's R-points with invertible d-by-d matrices. ULift only aligns the index
  universe with k and R; it changes neither cardinality nor matrix entries.
- The “equivalently” coaction sentence describes this same linear representation,
  rather than imposing additional independent data. The coordinate functions
  of the group-scheme homomorphism rho are its coaction matrix over O(E).
  The multiplication and unit conditions in `IsMonHom ρ` are exactly the two
  displayed coaction identities, using the actual Laurent Hopf law of E.
- The opening conventions for subgroups, fppf quotients, smoothness, connectedness,
  and geometric connectedness introduce no hypotheses or conclusions here:
  the theorem has no subgroup, quotient, or independent smooth/connected object.
  In particular none is added as an extra assumption. The existing source modules
  for the recorded subgroup, smoothness, and connectedness dependencies are imported.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, group homomorphisms;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (conventions only).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, and
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (conventions only).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `additive`,
  `additiveGroup`, `multiplicative`, `multiplicativeGroup`, with their coordinate
  comultiplication, counit and inverse. The full signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`; added its owning, already
  landed `def-sfb-tori-multiplicative-type` to stmt_deps.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` publicly exposes the existing
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `GeneralLinearGroup`, its group instance and `GeneralLinearGroup.homMulEquiv`.
  Added its owning, landed `def-sc-general-linear-group` to stmt_deps. The existing
  construction also covers dimension zero, as that node's record explicitly notes.
- Mathlib's `ModObj`, `Pi.π`, and finite products in `Grp` supply the action and
  the vector-group product without any replacement definition.
- Proof-only imports: recorded standard graded algebras, prime Frobenius,
  multivariate polynomials, and field characteristic. The two proof dependencies
  `lem-trf-additive-polynomial-monomial-classification` and
  `lem-sfb-torus-equivariant-frobenius-module-basis` have no Lean record yet;
  their nonexistent modules are not imported. They are not statement prerequisites.

Edge cases checked before writing: d = 0 gives the empty product group, GL of the
zero module, and an empty list of coordinate equations, which is sufficient since
C is isomorphic to that trivial group. s = 0 gives the trivial acting group.
Characteristic 2, arbitrary imperfect fields and finite fields are permitted.
Nonreduced R and the zero ring are explicitly included by `[CommRing R]` without
`Nontrivial R`. Testing all algebras of the scheme universe includes the universal
coordinate algebras and therefore detects all morphism identities; larger test
algebras follow from the same polynomial identities. No instance equates unrelated
universes. `set_option autoImplicit false` enforces explicit binding.

Searches actually run with `msearch.py Q89 lem-sfb-torus-vector-group-linearization`:

- LeanFinder: “Every algebraic action of a split torus on an additive vector group
  can be linearized by additive polynomial coordinates”: 8 hits, including
  Rep.coe_linearization_obj (free module on a set), polynomial Galois actions,
  LinearEquiv.ofAEval and Hilbert 90; none states algebraic-group linearization.
- Loogle: `ModObj, IsScalarTower`: no hits, unknown identifier ModObj in the
  remote search index. Local source inspection supplies Mathlib's actual ModObj.
- LeanSearch: “Every action of a split torus by automorphisms of a vector group
  is conjugate by an additive polynomial automorphism to a linear representation”:
  8 hits, including Action.ρAut, GroupExtension.Splitting.conjAct,
  AddAut.applyMulAction and Representation.ofMulDistribMulAction; none is the
  algebraic vector-group linearization theorem.
- Mathlib grep: `vectorGroup|VectorGroup|lineariz|ModObj` in AlgebraicGeometry:
  zero hits. Global `torus.*linear|linear.*torus|vectorGroup|VectorGroup`: one
  unrelated UnitAddTorus Fourier-analysis comment.
- `rg` of `lean/WeilConjectures` for the item id and torus/vector-group linearization:
  no matching theorem. `rg` of `lean/Sheaf` found the characteristic-zero
  commutative-unipotent classification, which has no action or equivariance and
  excludes positive characteristic; it is not this statement. It confirms the
  established use of categorical powers of Ga.
- Further local source searches located the existing splitTorus, general-linear
  scheme, ModObj and product-projection APIs. The helper's full name and theorem
  name were checked against the source trees; there is no duplicate declaration.

Validation: `scompile.py Q89 lem-sfb-torus-vector-group-linearization` compiled both
its sandbox module and final library module cleanly (20.7 s and 5.5 s reported).
Only theorem proofs are postponed; the coordinate helper is a real construction.

## Second reading by Q89

This is the dispatch worker's final self-reading, not a claimed independent review;
the brief assigns the independent review to the maintainer after delivery. I reopened
the node and Lean file and checked the hC group isomorphism, the internal action
identities, multiplication preservation over arbitrary R, and the rho morphism's
IsMonHom condition. I checked the direction of a carefully: substituting x = a(w)
in the coordinate conclusion gives a^(-1)(e.a(w)) = rho(e)w, exactly the requested
formula after applying a. The original hC does not constrain the existential a.
No characteristic or perfectness hypothesis has slipped in. Empty product and
zero matrix indices remain allowed. The coaction paragraph is an equivalent
description of the represented GL morphism, not an omitted independent assertion.
The helper only evaluates the existing product coordinates. No new nodes or
replacement dependency modules are needed. During compilation I corrected a
projection field-access syntax and opened the recorded scoped group instances;
neither changed the mathematical statement.

Dry run: deliver2.py --no-push returned OK at commit 318399ae2fb: preflight and
per-file compilation passed, with no files pushed at that step.
