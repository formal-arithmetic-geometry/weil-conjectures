## Worker report

The delivery states both conclusions of lem-sfb-sl2-diagonal-kernel-detection in
Sheaf.AlgebraicGeometry.SL2DiagonalKernelDetection. Every theorem is postponed with
`sorry`; no mathematical theorem is proved. Definitions contain actual data.

Hypotheses and clauses, checked against the node:

- The algebraically closed base field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- S is exactly `LinearGroupSchemes.specialLinear k 2`, the existing determinant-one
  polynomial quotient scheme, with its recorded `specialGroup` structure and natural
  `specialPoints k 2 R` equivalence to determinant-one matrices. The two indices are
  ULift (Fin 2), as in the shared definition; no characteristic is restricted.
- D is `StandardGroupSchemes.multiplicative k` with `diagonalTorus k` as inclusion.
  Its actual coordinate map sends the four entries, in row order, to T(1), 0, 0, T(-1).
- A subgroup N is `(N : Over (Spec (.of k))) [GrpObj N] (i : N ⟶ specialLinear k 2)`.
  `[IsClosedSubgroupScheme i]` supplies the homomorphism, all-algebra injectivity,
  and closed immersion; `[IsNormalSubgroupScheme i]` is the recorded all-algebra
  normal-range condition. This is equivalent to conjugation factoring through N:
  every affine test scheme supplies precisely that condition, and affine tests cover
  S × N. We do not replace normality by normality on k-points.
- `hinter` quantifies over every `R : Type u` with `[CommRing R] [Algebra k R]`, an
  N-point n and a D-point d. Its premise says the two images in S agree, and its
  conclusion says their common image is the identity. Since both inclusions are
  monomorphisms and contain the identity, this is exactly that their fibre product
  is the trivial subgroup scheme. Affine tests characterize that assertion; it is
  not merely an assertion about the reduced intersection or about rational points.
- `IsIso N.hom` says N is Spec k over k; a group homomorphism from this trivial
  group scheme is necessarily the identity section. Thus it expresses N=1 as a
  subgroup, rather than an abstract isomorphism to some unspecified group.
- For the consequence M has `[AddCommGroup M] [Module k M] [FiniteDimensional k M]`.
  `GeneralLinearGroup (Module.Free.ChooseBasisIndex k M) k` is the existing GL(M)
  scheme in the basis `Module.Free.chooseBasis k M`. This is a coordinate model,
  not an additional hypothesis or replacement by only the abstract group GL(M)(k).
  Its algebra-valued points are matrices for automorphisms of R ⊗[k] M.
- `v` is a scheme morphism to that GL scheme, and `[IsMonHom v]` requires exactly
  a group-scheme homomorphism. `hD` is `IsClosedImmersion (diagonalTorus k ≫ v).left`.
  The second conclusion is exactly `IsClosedImmersion v.left`.
- There is no smoothness, reducedness, connectedness, or characteristic assumption
  on N and no positive-dimension restriction on M.

Dependencies read and used:

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field).
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`, the algebraically-closed
  component explicitly recorded by def-weil-algebraic-closure.mathlib_match.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, specialized to
  Over (Spec k), as def-sc-group-scheme instructs.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`, their superclasses and all-algebra signatures.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Sheaf.AlgebraicGeometry.LinearGroupSchemes: `specialLinear`, `Index`,
  `specialIdeal`, `SpecialAlgebra`, `specialGroup`, `specialPoints`, and
  `specialPoints_natural`, attached to def-sc-general-linear-group. That already
  landed definition node is added to stmt_deps, without changing its record.
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear:
  `AlgebraicGeometry.GeneralLinearGroup` and its canonical point identification.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `affine`, `map`, `multiplicative`.
- Mathlib.LinearAlgebra.FreeModule.Finite.Basic: finite Fintype instance on
  `Module.Free.ChooseBasisIndex k M`; the existing chosen basis identifies GL(M).
- The stated proof dependencies are imported non-publicly:
  WeilConjectures.AlgebraicGeometry.SchemeTangentSpace (`schemeTangentSpace`),
  WeilConjectures.Mathlib.RingTheory.Nullstellensatz
  (`exists_algHom_ker_eq_of_isMaximal`, clause 1, without IsReduced),
  Mathlib.RingTheory.FiniteType (`Algebra.FiniteType.isNoetherianRing`),
  Mathlib.RingTheory.LocalRing.Module (`IsLocalRing.map_mkQ_eq_top`), and
  Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
  (`rational_tangent_cotangent_duality`). The kernel definitions are already
  imported through GroupScheme.Defs, including `GrpObj.ker`, `GrpObj.kerι`, and
  the normal and closed kernel subgroup instances. The final faithful closed
  immersion node has no recorded declaration yet, so has no import to add.

Edge cases checked before drafting: in characteristic two the infinitesimal scalar
centre μ2 is nontrivial on dual numbers and violates hinter, as it must; looking only
at k-points would incorrectly admit it. The first Frobenius kernel also violates
hinter. N=1 satisfies the premise. N=SL2 fails it on nonidentity diagonal points.
Zero test algebras are allowed; nothing requires a test algebra to be a field or
reduced. The ring and scheme universes agree with the recorded group-scheme API;
test algebras have the same universe as k, not a potentially smaller independent
universe. M=0 has an empty chosen basis and GL(0)=1: hD is then impossible, and the
implication remains valid. The diagonal coordinate construction uses no division
by two, and tt⁻¹=1 holds for arbitrary test algebras. The Laurent generator really
is invertible, so the diagonal image has precisely the advertised unit parameter.

Searches (through the mandated msearch.py wrapper):

- leanfinder: "A closed normal subgroup scheme of SL2 meeting the diagonal torus
  trivially is trivial" gave 8 hits on abstract modular/congruence subgroups, not
  scheme kernels or the representation consequence.
- loogle: `Matrix.SpecialLinearGroup, "ker"` gave six results, including
  range_toGL_eq_ker_det, toGLKerEquiv and toPGL_ker; none is this statement.
- grep `SpecialLinear|specialLinear|diagonalTorus` in Mathlib/AlgebraicGeometry:
  zero hits. Local rg over WeilConjectures and Sheaf found the already landed
  LinearGroupSchemes module; it has SL and GL but no diagonal torus inclusion or
  kernel-detection result. An item-id search in WeilConjectures found no declaration.
- leansearch: "The diagonal torus embedding Gm into the special linear group
  scheme SL2" gave eight abstract-matrix and topological-embedding hits.
- leanfinder: "The diagonal multiplicative group closed subgroup scheme of SL2
  given by diag(t, inverse t)" gave matrix centres/congruence groups, no morphism.
- grep `diagonal.*[Tt]orus|[Tt]orus.*diagonal` in Mathlib/AlgebraicGeometry: zero hits.
  The DAG keyword search found consumers of this notion but no defining node;
  `tools/blueprint_refs.py search 'diagonal torus'` returned zero blueprint nodes.

Read the latest blueprint unit and the actual Milne Section 20g source, especially
the cocharacter t ↦ diag(t,t⁻¹) in the proof of Proposition 20.25. No correction to
the assigned statement is needed, and there is no STATEMENT-DISPUTED finding.
The existing SL/GL node and new torus definition are added to stmt_deps solely
because these already specified objects now have explicit owning declarations.

Both delivery files compiled individually through scompile.py in dependency order,
with no errors or unexpected warnings. The first compile exposed missing scope for
the existing point-group identity notation; `open scoped MonObj` repaired it. No
local notation, local instance, private declaration, auto implicit or diagnostic
command remains.

## New nodes

`def-sfb-sl2-diagonal-torus` defines the missing canonical inclusion Gm → SL2 by
its Laurent substitution. It reuses the already defined two schemes rather than
constructing new copies. Its module gives the polynomial map, the named postponed
proof that it kills the determinant ideal, the quotient lift, and Spec of that
lift. The source is Milne Section 20g, pp.415--418. The LeanSearch, LeanFinder and
grep searches above (recorded in the node) found no such morphism. The determinant
relation lemma belongs to this definition node and has its complete elementary
proof in its docstring; no arbitrary map or existence choice supplies its data.
The inherited ancestor is null, confirmed with blueprint_refs.py ancestor, and
the new node retains the assigned item's full explicit route and via chain.

## Second reading by NN

A separate second pass by this worker, without delegation as the dispatcher
requires, compared the finished Lean with the original node and the new definition.
The checks were each hypothesis and clause listed above: algebraic closure, actual
SL2, actual diagonal torus, closed and normal scheme subgroup, fibre-product
triviality on all algebras, triviality as a subgroup, arbitrary finite-dimensional
M including zero, homomorphism v, closed immersion on D, and closed immersion of v.
No omitted hypothesis or conclusion was found. The only elaboration repair was
opening the existing MonObj scope for 1; no mathematical statement changed.
The coordinate-map second pass checked the index 0/1 ordering and T(1),T(-1)
exponents, and verified that the sole postponed relation proves well-definedness,
not unspecified data. This is a self-review, not a claim of an independent reader;
the maintainer's independent review is still required by this dispatch protocol.
