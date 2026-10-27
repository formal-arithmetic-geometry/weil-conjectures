## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TriangularDiagonalKernel` states
`AlgebraicGeometry.triangular_diagonal_kernel` and
`AlgebraicGeometry.smooth_unitriangular_iff_geometric_unipotent`. Both proofs are
`sorry`; there are no definitions or instances with postponed data. The second
theorem is the final, independent comparison clause of this same DAG statement.
The node's natural-language statement and proof are unchanged. Its `stmt_deps`
adds the two already-landed definition owners
`def-sfb-solvable-group-structure` and
`def-sfb-fppf-group-quotient-presentation`, because their exact existing predicates
occur in the signatures. No new nodes or dependency modules are needed.

Sources read: Milne, Algebraic Groups (2017), printed pp.325--326, 332--333 and
283 (PDF pp.337--338, 344--345 and 295), including Proposition 16.2(c) implies
(d), Note 16.10, Theorem 16.26(a) with diagram (118), and Corollary 14.12. The
current `literature/blueprint/latest` unit `sk-thm-sf-ctf-stability/_section.md`
and its direct-images proof were also read; this node is supporting input down
the recorded alteration route, not the blueprint unit's own statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `{k : Type u} [Field k]` in both theorems. |
| Affine group schemes of finite type over k | `Grp (Over (Spec (.of k)))`; `[IsAffine J.X.left]`, `[LocallyOfFiniteType J.X.hom]`, `[QuasiCompact J.X.hom]`; the same properties of V and D are conclusions. The comparison theorem has these three hypotheses on G. |
| n at least one | `(n : ℕ) (hn : 0 < n)`; the comparison embedding likewise has `∃ n, 0 < n`. |
| J a closed subgroup of B_n | `r : J.X ⟶ GeneralLinearGroup (ULift (Fin n)) k`, `[IsClosedSubgroupScheme r]`, and `hupper` on every commutative k-algebra: entry (i,j) is zero whenever j<i. |
| B_n consists of all upper triangular invertible matrices | The ambient `GeneralLinearGroup` supplies invertibility. Factoring the closed GL_n immersion through the upper-triangular closed subscheme is equivalent to `hupper` on all algebras; no choice of a merely pointwise subgroup over k is substituted. This is the same established encoding used in the landed `charZero_commutative_unipotent_vectorGroup` and adjoint-kernel statements. |
| U_n has diagonal entries one | The diagonal-one conditions below are tested on all algebras, together with the same upper-triangular equations, inside the existing GL_n. No second definition of U_n is introduced. A closed GL_n immersion satisfying these equations factors as a closed immersion into U_n, because the coordinate-ring map factors through the quotient by these equations and remains surjective. |
| delta is a group-scheme homomorphism to (G_m)^n | `δ : J ⟶ ∏ᶜ (fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.multiplicative k))`; this is Mathlib's finite product in group objects. |
| delta(g) is the tuple of diagonal entries | For every A, x and i, the Laurent coordinate `T 1`, evaluated via `WithConv.ofConv (Spec.mapMulEquiv.symm (x ≫ δ.hom.hom ≫ (Pi.π ... i).hom.hom))`, equals matrix entry (i,i) under the existing `GeneralLinearGroup.homMulEquiv`. It therefore fixes the actual diagonal map, including on nilpotent test algebras. |
| V = ker delta, scheme-theoretically | `IsPullback iV.hom.hom (toUnit V.X) δ.hom.hom η[...]`; the square is in schemes over k, so it is the actual scheme-theoretic kernel, not just a kernel of geometric points. |
| V = J intersect U_n | The all-algebra equivalence `(∃ v, v ≫ iV.hom.hom = x) ↔ ∀ i, matrix(x) i i = 1`. Together with the kernel square and the faithful closed inclusion, this identifies the closed intersection on every algebra. |
| V closed and normal in J | `IsClosedSubgroupScheme iV.hom.hom ∧ IsNormalSubgroupScheme iV.hom.hom`. |
| V is scheme-theoretically unipotent | `IsClosedSubgroupScheme (iV.hom.hom ≫ r)` and, for every A-point of V, diagonal entries one and lower entries zero. This gives the specified closed embedding into U_n as explained above, with no smoothness assumption. |
| The fppf quotient D = J/V is represented | Existential group scheme D and homomorphism q with `IsFppfGroupQuotient iV q`, the existing predicate retaining the kernel square, actual fppf local surjectivity, represented sheaf, torsor map, and sheafification universal property of the pointwise coset presheaf. |
| delta induces a closed immersion D into the torus | Existential `d` to the same finite product, `q ≫ d = δ`, and `IsClosedSubgroupScheme d.hom.hom`. |
| If k algebraically closed, q admits a group-scheme section | `IsAlgClosed k → ∃ s : D ⟶ J, s ≫ q = 𝟙 D`. No closedness or smoothness hypothesis is added to D. |
| Multiplication (v,d) maps to v s(d) and is a scheme isomorphism | `IsIso (lift (fst V.X D.X ≫ iV.hom.hom) (snd V.X D.X ≫ s.hom.hom) ≫ μ[J.X])`. Its source is the product in schemes over k; this is exactly V times_k D. Isomorphisms in Over are precisely isomorphisms of schemes over k. The map is specified by multiplication, rather than an arbitrary product isomorphism. |
| In that case, smooth connected J gives smooth connected V and D | Inside the algebraically closed implication: `Smooth J.X.hom → ConnectedSpace J.X.left → Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧ Smooth D.X.hom ∧ ConnectedSpace D.X.left`. |
| For smooth groups, scheme-theoretic unipotence equals the geometric matrix condition | The second theorem assumes smooth affine finite-type G. Its left side is a closed GL_n embedding whose matrices over all algebras have diagonal one and zero lower entries. Its right side is the recorded `SolvableGroupStructure.IsUnipotent G`, which is smoothness plus existence of a faithful closed matrix representation with `(matrix(x)-1)^N=0`, `0<N`, over every algebraically closed extension field. Smoothness is a hypothesis of this theorem and is not imposed on the first theorem's V. |
| fppf means sheafification for faithfully flat finitely presented algebra covers | `IsFppfGroupQuotient` uses `Scheme.fppfTopology.over (Spec k)` and the explicit coset coequalizer/sheafification unit. Affine refinement identifies this with the specified algebra covers; no surjectivity on raw A-points is asserted. |

Dependency declarations read and reused:

- `Field`, Mathlib.Algebra.Field.Defs; `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (algebraic-closure node's match).
- `CategoryTheory.GrpObj`, `Grp`, and bundled group homomorphisms,
  Mathlib.CategoryTheory.Monoidal.Grp; group-scheme conventions and the full
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`
  signatures and docstrings in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear: the existing
  coordinate Hopf algebra and its natural identification with invertible
  matrices. The recorded general-linear node now imports these via
  Sheaf.AlgebraicGeometry.LinearGroupSchemes; that module is imported, not a
  private redefinition of GL or a substitution of its SL declaration.
- `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes: the recorded Laurent Hopf
  algebra G_m. `Spec.mapMulEquiv` is in
  Mathlib.AlgebraicGeometry.Group.Affine; `Pi.π` and the group-object product
  come from Mathlib's category-theory limits and GrpLimits APIs.
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact; `Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth. Finite type is the recorded
  conjunction, not an unrecorded new class.
- `SolvableGroupStructure.IsUnipotent`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure: its complete signature
  and body were read, including smoothness and all algebraically closed
  extensions. It is used only for the smooth comparison clause.
- `IsFppfGroupQuotient`,
  Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry: its
  complete definition is reused as the newly recorded definition owner
  def-sfb-fppf-group-quotient-presentation prescribes.

Proof-dependency imports: the existing kernel API
WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp,
Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization,
Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry (also a
statement import for its quotient predicate),
Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra, and
Mathlib.RingTheory.FinitePresentation (`Algebra.FinitePresentation.of_finiteType`).
The full signatures/docstrings of the recorded proof declarations were read.
The split-torus subgroup, coordinate filtration, additive-subgroup splitting,
and geometric-unitriangular embedding proof nodes currently have no Lean
records; they are named in the complete proof docstrings, with no invented
imports. They are not needed to type this statement and no wait is introduced.

Edge cases checked before writing:

- n=1: U_1 and V are trivial; J can be any closed subgroup of G_m, including
  nonreduced mu_p. The quotient is J and the splitting/product assertion
  retains it. No nontrivial-coordinate or positive-dimension hypothesis occurs.
- Trivial J and trivial D are included, as are finite and disconnected J.
  ConnectedSpace explicitly requires nonemptiness; group schemes have an
  identity section. Empty group schemes over a field are not group objects.
- In characteristic p, alpha_p in U_2 has V=alpha_p and trivial D; its
  scheme-theoretic unipotence is retained without asserting smoothness.
  For diagonal mu_p, V is trivial and D=mu_p; the conditional smoothness
  clause is not applicable. These distinguish the first theorem from the
  smooth-only geometric-point comparison.
- The A-points include all nonreduced algebras and the zero algebra. Upper
  and diagonal equations over the zero algebra are consistent (0=1 there).
  The universal-algebra tests, not field points, determine the intersection.
- Arbitrary characteristics and imperfect fields are retained in the kernel
  and quotient assertion. Only the specified splitting implication uses
  algebraic closedness; no perfectness or characteristic-zero binder occurs.
- Index `ULift.{u} (Fin n)` follows the upstream GL common-universe convention;
  it is the same n-element ordered index set, with inequalities on `Fin n`.
  Fields, algebras and schemes share u as in all the recorded interfaces,
  and u is arbitrary. Every variable and universe is explicitly bound.
- In the smooth comparison, a dimension-zero faithful representation allowed
  by the existing IsUnipotent predicate only describes the trivial group;
  it has a positive-size embedding in U_1. Thus positivity on the left
  excludes no group admitted by the right.

Searches made for an existing exact statement:

- msearch leanfinder: "The diagonal homomorphism of a triangular algebraic
  group has normal unipotent kernel, represented fppf quotient in a split
  torus, and splits over an algebraically closed field". Eight hits, on
  Lie triangularizability, semisimple rings, Jordan decomposition and
  formally smooth split algebra maps; none state this group-scheme result.
- msearch loogle: `AlgebraicGeometry.IsClosedSubgroupScheme,
  CategoryTheory.GrpObj.ker`. Zero hits; the project-specific subgroup
  identifier is unknown to the Mathlib service.
- msearch grep: `triangular|unipotent|FppfQuotient` under AlgebraicGeometry.
  Zero hits.
- msearch leansearch: "the diagonal map on a triangular group scheme has a
  normal unitriangular kernel and the extension by its torus image splits
  over an algebraically closed field". Eight hits, including abstract
  `GroupExtension.Splitting`, Lie triangularizability, ordinary subgroup
  kernels and diagonal immersions; none is the scheme-theoretic theorem.
- rg of `triangular_diagonal_kernel|smooth_unitriangular_iff_geometric_unipotent|
  lem-sfb-triangular-diagonal-kernel` in lean/WeilConjectures and lean/Sheaf:
  only proof-plan citations in PerfectSolvableUnipotentTorus and
  GroupScheme/BorelMaximalTorusConjugacy, no declaration of the result.
- rg of triangular/unitriangular/IsUnipotent in the project and upstream
  algebraic-geometry trees found the existing SolvableGroupStructure
  definition, ToriMultiplicativeType, and the all-algebra matrix encoding
  of CharZeroCommutativeUnipotentVectorGroup and AdjointKernelCentralQuotientUnipotent.
  None provides this kernel, diagonal map, quotient and splitting theorem.
- rg of `IsUnitriangular|Unitriangular|isUnitriangular` in Mathlib's
  AlgebraicGeometry and LinearAlgebra/Matrix found no scheme definition;
  no new private notion is introduced here, only explicit equations in GL.
- DAG searches for unitriangular/unipotent definitions found the recorded
  smooth IsUnipotent owner and unrelated representation/ind-group notions;
  the needed quotient owner already exists and is cited.

No STATEMENT-DISPUTED flag or source-based statement correction is needed.
Compilation uses scompile.py only. An initial coordinate-evaluation projection
syntax error was repaired by writing `WithConv.ofConv` explicitly. The next
wrapper run exhausted local disk space, then its normal current-server
confirmation compiled the module cleanly in 3.2 seconds, with no errors or
unexpected warnings. The final packet is checked again by deliver2.py.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
