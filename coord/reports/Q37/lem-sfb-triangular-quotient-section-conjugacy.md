## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.TriangularQuotientSectionConjugacy
states AlgebraicGeometry.triangular_quotient_section_conjugacy, with its entire
proof postponed as `sorry`. There are no new definitions or helper theorems.
The statement of the DAG node is unchanged. Its stmt_deps gains the already
landed definition node def-sfb-fppf-group-quotient-presentation, whose existing
predicate expresses the quotient explicitly required by the item.

Source checked directly: literature/milne-algebraic-groups_iAG2017.pdf,
Theorem 16.27(a), printed p.333, and Summary 16.29(b), printed p.334.
The latter explicitly assumes a smooth multiplicative-type quotient and states
conjugacy by a kernel rational point over an algebraically closed field.
The item already retains this smoothness condition. No correction is required.

Hypotheses and clauses, in node order:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- All groups are group schemes over F: `J V D : Grp (Over (Spec (.of F)))`.
  The bundled Grp objects carry the existing GrpObj structure on their X fields.
- Affine, finite type: each of J, V and D has `IsAffine _.X.left`,
  `LocallyOfFiniteType _.X.hom`, and `QuasiCompact _.X.hom`. These render
  precisely the node's standing convention for all its groups.
- n >= 1: `(n : ℕ) (hn : 1 ≤ n)`.
- The ambient GL_n is the existing `GeneralLinearGroup (ULift.{u} (Fin n)) F`.
  Lifting the finite index type is the upstream size convention, and preserves
  all n indices, including n = 1.
- J is a closed subgroup of B_n: `j` embeds J in GL_n, with
  `[IsClosedSubgroupScheme j]`. The binder `htriangular` says that every
  matrix obtained with `GeneralLinearGroup.homMulEquiv` has entry (a,b) zero
  whenever b < a, over every commutative F-algebra A. An invertible matrix
  satisfying these equations is precisely an invertible upper triangular
  matrix. Thus this is the closed subgroup inclusion in B_n followed by
  B_n -> GL_n, without introducing a second construction of B_n.
- V = J intersect U_n scheme-theoretically: `i : V ⟶ J` is a closed subgroup
  inclusion, and `hintersection` says that a J(A)-point factors through i
  exactly when each diagonal entry of its matrix is 1. Triangularity already
  supplies the lower-entry equations. This is equality of the intersection
  functor on every algebra, not just equality of rational or geometric points.
  Since both closed subfunctors are represented, affine Yoneda identifies
  their schemes. It includes nilpotent equations on nonreduced test algebras.
- q represents J/V: `(q : J ⟶ D) (hquotient : IsFppfGroupQuotient i q)`.
  The reused predicate records the kernel square, fppf local surjectivity,
  represented sheaf condition, canonical torsor coordinates (g,v) -> (g,gv),
  and the sheafification universal property for the right-coset presheaf.
  Affine tests recover exactly A -> J(A)/V(A) with fppf algebra covers.
- Smooth D: `[Smooth D.X.hom]`. There is no smoothness hypothesis on J or V.
- Two group-scheme homomorphism sections: `(s₁ s₂ : D ⟶ J)` in the bundled
  group-object category, with `hs₁ : s₁ ≫ q = 𝟙 D` and the identical hs₂ clause.
- One rational conjugator in V: the conclusion quantifies
  `v : 𝟙_ (Over (Spec (.of F))) ⟶ V.X`. The monoidal unit in this cartesian
  over-category is Spec F with its identity structure map, so this is V(F).
- Equality of morphisms s₂ = Int(v) s₁: the first conjunct is equality of
  the actual maps D.X -> J.X. In the existing Hom group, multiplication is
  pointwise multiplication in J, inverse is composition with the inverse
  morphism, and `toUnit D.X ≫ v ≫ i.hom.hom` is the constant map with value v.
- Explicit formula on every A and d: the second conjunct quantifies every
  commutative F-algebra A and every `d : Spec A ⟶ D.X` over F, and asserts
  `d ≫ s₂ = v_A * (d ≫ s₁) * v_A⁻¹` using the underlying maps.
  Here `v_A` is literally `toUnit (Spec A over F) ≫ v ≫ i.hom.hom`, hence
  scalar extension of the same single v; it is not a point chosen for each A.
- The node excludes no characteristic or disconnected/nonreduced group:
  there is no CharZero, IsReduced, ConnectedSpace, or extra smoothness binder.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (the algebraically
  closed notion recorded in def-weil-algebraic-closure, not an arbitrary
  extra algebraic extension). The AlgebraicClosure record and its explanation
  of this component were read.
- Mathlib.CategoryTheory.Monoidal.Grp: `Grp`, `GrpObj`, bundled group
  homomorphisms; Mathlib.CategoryTheory.Monoidal.Cartesian.Grp: `Hom.group`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`; this is the recorded subgroup
  declaration, including injectivity on algebra points and closed immersion.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`,
  inherited from the closed subgroup instances.
- Sheaf.AlgebraicGeometry.LinearGroupSchemes (the recorded module for
  def-sc-general-linear-group) publicly imports the existing upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear:
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`. Their full
  definitions and naturality docstring were read; no GL copy is made.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry:
  `IsFppfGroupQuotient`, registered by the added, already landed definition
  node. Its full signature, five conjuncts, source and docstring were read.

Proof-only imports retain the recorded plan: HomomorphismFactorization for
lem-sfb-algebraic-group-homomorphism-factorization, and
Mathlib.AlgebraicGeometry.AlgClosed.Basic for
lem-weil-pbc-closed-point-residue-field-base (`residueFieldIsoBase` and
`SpecMap_residueFieldIsoBase_inv`). The other three proof dependencies
(split-torus-subgroups-diagonalizable, unitriangular-coordinate-filtration,
smooth-diagonal-additive-crossed-vanishing) have no recorded Lean module,
so there is no import for them. They are named in the complete six-step
natural-language proof docstring. They are proof dependencies, not missing
objects required to type this statement.

Edge cases checked before writing:

- n = 1: the lower-entry condition is empty; V has diagonal 1 and is trivial,
  so the conclusion becomes equality of sections. n = 0 is excluded as in
  the node, rather than being silently admitted or replacing the bound.
- V trivial, J diagonal, or D trivial: the rational identity conjugator gives
  the expected equal sections.
- Nonreduced and nonsmooth J or V are permitted; membership tests use all
  algebras, not just fields. Smooth D is retained even in positive
  characteristic, avoiding the known infinitesimal-quotient counterexample.
- Disconnected smooth D and disconnected J or V are not excluded.
- The zero algebra is allowed among the test algebras. All point conditions
  still describe the same represented closed subfunctors on the empty test.
- Universe u is arbitrary; test algebras share the scheme universe, as in
  the existing group-scheme and quotient interfaces. No independent smaller
  algebra universe or forced equality of different site universes is added.

Searches for an existing theorem:

- msearch.py leanfinder: "Any two algebraic group scheme homomorphism sections
  of a smooth diagonal quotient of an upper triangular group are conjugate
  by a unitriangular kernel rational point". Eight hits, including
  Rep.diagonalHomEquiv_apply and diagonal_SpecMap; none asserts conjugacy.
- msearch.py loogle: `"GroupExtension", "IsConj"`. Five hits:
  GroupExtension.IsConj, its setoid, refl, symm and trans. These define
  conjugacy or its formal properties for abstract groups; none states that
  every pair of algebraic-group sections is conjugate by one kernel point.
- msearch.py grep: `triangular.*section|section.*triangular|unipotent.*conjug|conjug.*unipotent`.
  One hit in Mathlib/LinearAlgebra/Matrix/SchurComplement.lean, unrelated.
- msearch.py leansearch: "Conjugacy of homomorphism sections of a triangular
  algebraic group scheme modulo its unitriangular subgroup with smooth quotient".
  Eight hits, including GroupExtension.IsConj and Splitting.conjAct; no theorem.
- rg over lean/WeilConjectures and lean/Sheaf for triangular/unitriangular and
  section/conjugacy combinations. Existing matrix-point, subgroup and fppf
  quotient interfaces were found and reused. BorelMaximalTorusConjugacy only
  mentions this item in its proof plan and does not state it.
- rg for this item id in lean/WeilConjectures: no declaration.
- The proposed full declaration name was checked in both project roots and
  the upstream name index; no existing declaration has this name.

No STATEMENT-DISPUTED flag and no node fault was found. The initial compiler
probe required opening the existing CategoryTheory.MonObj scope to enable
Hom.group; this was an elaboration-scope correction and changed no mathematics.

## Second reading by Q37

The worker separately reread the node and the completed signature, following
its clauses in order. No second agent was started, as the dispatcher brief
forbids starting agents. The maintainer's independent delivery review remains
separate from this worker rereading.

The rereading verified the closed immersion for j, all-algebra lower-entry
condition, closed immersion for i and the two-direction membership equivalence,
the actual specified quotient i,q, smoothness on D alone, both bundled
homomorphism sections and both section equations, and the single existential
rational v used in the two conclusions. It checked that composition in Lean
runs left-to-right, so s_i ≫ q is q composed with s_i. It also checked the
conjugation direction: s₂ equals v s₁ v⁻¹, with v rather than v⁻¹ on the left.
There are no local definitions or local instances in the public signature.
The hintersection equivalence tests every algebra and so retains the
scheme-theoretic intersection even in nonreduced cases. No mismatch required
a statement change, dependency repair, or new node.
