## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.HomogeneousCoherentAcyclicity`
states `AlgebraicGeometry.isZero_moduleCohomology_of_homogeneous_nontrivial`.
Its only theorem proof is `sorry`; there are no new definitions or helper theorems.
The accepted stage-1 statement and proof are preserved. The extra statement dependency
`def-sc-group-scheme-translate` already has its upstream Lean record and supplies the
right translation used in the statement. No statement correction is needed.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Abelian variety A/k: `(A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]`.
  The last class is properness, smoothness and connectedness; the separate `GrpObj`
  supplies exactly the group-scheme structure required by its recorded definition.
- Invertible O_A-module P: `(P : A.left.Modules) [Scheme.Modules.IsInvertible P]`.
  This is the dependency's locally free rank-one notion, without an extra coherence
  or algebraic-equivalence hypothesis.
- Every a in A(k): `∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ A`.
  The monoidal unit of this over category is Spec k with its identity structure map,
  so these are precisely rational points over k.
- The map x ↦ x+a: `(GrpObj.mulRight A a).left`. Its source definition is
  `lift (𝟙 A) (toUnit A ≫ a) ≫ μ[A]`, so this uses right translation directly.
- Translation invariance under tensor inverse image:
  `Nonempty ((Scheme.Modules.tensorPullback (GrpObj.mulRight A a).left).obj P ≅ P)`.
  Nonempty expresses existence of an isomorphism, without imposing compatibility
  or choosing a linearization.
- P not isomorphic to O_A:
  `¬ Nonempty (P ≅ SheafOfModules.unit A.left.ringCatSheaf)`.
  This is nonisomorphism, rather than mere inequality of module objects.
- Every integer i ≥ 0: `(i : ℕ)` parametrizes exactly all nonnegative integers.
- H^i(A,P)=0:
  `IsZero ((RingedSpace.moduleCohomology A.left.toRingedSpace i).obj P)`.
  This is a zero object in modules over global functions, equivalent to vanishing
  of the cohomology group. The exact module-cohomology functor recorded by
  `pqf-def-cohomology` is used; no abelian-sheaf Ext cohomology is substituted.
- No characteristic or dimension restriction, or algebraic triviality assumption:
  none appears among the binders. The universe u is explicitly declared and every
  variable is bound, with both auto-implicit options disabled.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; imported through the field-theory module.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  field notion named in the algebraic-closure dependency's Mathlib match.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` (and its separate group-object convention).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public re-export of
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. The explicit functor takes
  inverse image, extension of scalars and sheafification; it is the recorded
  dependency, not a second definition or the unrelated legacy pullback interface.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, whose full signature
  and docstring identify the degree functors as
  `AlgebraicGeometry.RingedSpace.moduleCohomology`. The underlying functor and its
  global-sections definition were read in
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`:
  `AlgebraicGeometry.GrpObj.mulRight`, the recorded translation dependency.

All recorded proof-dependency modules are imported with plain imports, including
both global-sections modules named by `lem-pc-h0-proper-variety`. The seesaw node
`lem-sfb-rigidified-product-seesaw` has no recorded module, so none can be imported
for it; its use remains documented in the natural-language proof. No proof
dependency interface is changed in this delivery.

Edge cases checked before writing: degree zero is included; dimension zero is
allowed (the nontrivial invertible-module hypothesis then has no examples); the
trivial line is deliberately excluded, since H^0(A,O_A) contains k; an elliptic
curve with a nontrivial degree-zero line gives the usual nonvacuous example; a
positive-degree line on an elliptic curve fails translation invariance. The empty
scheme cannot be an abelian variety with its rational identity. Positive
characteristic is unrestricted: the matrix argument divides only by a nonzero
scalar, never by dim H^i. No fixed upper cohomology bound is imposed.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py ... leanfinder`: "A nontrivial translation invariant invertible module
  on an abelian variety has zero coherent cohomology in all degrees". Eight hits,
  all about group cohomology, resolution Ext, or cotangent H1; no match.
- `msearch.py ... leansearch`: "Nontrivial homogeneous invertible modules on abelian
  varieties have vanishing coherent cohomology". Eight hits, including
  `CommRing.Pic.instFreeOfSubsingleton`, group-cohomology definitions and theorems,
  and `Module.nontrivial_dual_iff`; no geometric acyclicity theorem.
- `msearch.py ... loogle`: `"IsAbelianVariety", "cohomology"`. Zero hits.
- `msearch.py ... grep`:
  `homogeneous.*(invertible|line bundle)|translation.invariant.*(invertible|line bundle)|abelian.variety.*cohomology`.
  Zero Mathlib hits.
- `rg` of the project and upstream `lean/WeilConjectures` and `lean/Sheaf` for the
  node id and homogeneous acyclicity: no statement match. Targeted searches in
  abelian-variety and group-scheme modules found the existing translations and
  unrelated polarization statements, which are reused or distinguished.
- Exact-name `rg` in Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json`:
  no pre-existing `isZero_moduleCohomology_of_homogeneous_nontrivial`.
- The neighboring DAG node `lem-sfb-abelian-picard-zero-cohomology` assumes algebraic
  triviality, unlike this node; it supplies no existing Lean declaration here.

Read Milne I Proposition 8.4(b),(c), printed pp.35–36 (PDF pp.41–42), confirming
that translation invariance supplies the multiplicative identity used in step 2.
The module docstring contains every accepted proof step: global constants,
seesaw and dual cancellation, higher-direct-image comparison and finiteness,
and the finite-matrix contradiction. The acyclicity argument is correctly
attributed as agent-supplied rather than as Milne's printed proposition.

Validation: `scompile.py Q101 lem-sfb-homogeneous-coherent-acyclicity <module>`
passed both sandbox and library module-mode checks (5.6 s and 7.9 s), with no
errors or unexpected warnings. The prior unchanged-item stage-1 failure is not
relevant to this stage-2 Lean record; the current node has no Lean declaration.

## Second reading by Q101

A separate second pass by this worker reopened the node and Lean signature;
no independent worker is claimed, since the dispatcher explicitly prohibits
starting other agents and reserves independent review to the maintainer.
The field, group scheme, proper/smooth/connected class, invertibility,
rational-point quantifier, explicit right tensor translation, nonisomorphism,
and vanishing in every nonnegative degree match clause by clause as listed above.
In particular the cohomology is the recorded module-valued right derived functor,
not the source's distinct underlying-abelian-sheaf `H`. The conclusion is `IsZero`
on a bundled module, where it expresses vanishing correctly. No compatibility of
the translation isomorphisms and no algebraic-triviality hypothesis was introduced.
No signature mismatch was found and no statement change was made. The only added
DAG edge cites the already recorded right translation used in the signature.
