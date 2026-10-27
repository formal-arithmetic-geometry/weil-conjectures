## Worker report

Module `Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleIsogenySource` states
`AlgebraicGeometry.semisimpleGroupScheme_of_faithfullyFlat_finite_kernel` with a single
`sorry` proof. No definition is duplicated, and the mathematical node statement is unchanged.
The existing landed definition node `def-sfb-semisimple-group-scheme` is added to
`stmt_deps` to cite the predicate already used throughout this family.

Source read: Milne, Algebraic Groups (2017), Lemma 19.14, printed p.400 (PDF p.412),
semisimple case. It says that an isogeny G' → G of connected group varieties with
semisimple G has semisimple G'. Its proof sends a smooth connected normal solvable
subgroup into G; its image is trivial, so the subgroup is finite, hence trivial.
The latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof were read;
this supporting lemma changes neither that unit nor its route.

Clause-by-clause rendering:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group schemes H1,H2: `(H1 H2 : Over (Spec (.of F))) [GrpObj H1] [GrpObj H2]`.
  The Over structure supplies each structure map and makes f a morphism over F.
- Smooth: `[Smooth H1.hom] [Smooth H2.hom]`.
- Connected: `[ConnectedSpace H1.left] [ConnectedSpace H2.left]`; these include
  nonemptiness, as required by the recorded connectedness node.
- Affine: `[IsAffine H1.left] [IsAffine H2.left]`.
- Finite type: `[LocallyOfFiniteType Hi.hom] [QuasiCompact Hi.hom]` for each i.
- Homomorphism f: `(f : H1 ⟶ H2) [IsMonHom f]`, not an arbitrary scheme map.
- Faithfully flat: `hflat : f.left.appTop.hom.FaithfullyFlat`; appTop is the
  contravariant coordinate map F[H2] → F[H1]. RingHom.FaithfullyFlat equips its
  target with the induced algebra/module structure and asks for Module.FaithfullyFlat,
  i.e. flat tensor extension that detects zero modules.
- Scheme-theoretic kernel: `GrpObj.ker f`, the actual pullback along the unit section.
- Finite-dimensional kernel coordinate algebra:
  `hfinite : @Module.Finite F Γ((GrpObj.ker f).left, ⊤) _ _
  (GrpObj.ker f).hom.ΓAlgebra.toModule`.
  The explicit module is the canonical F-action induced by its structure map; over
  a field Module.Finite is precisely finite-dimensionality. No arbitrary action,
  choice of algebra, cardinality of points, or extra kernel property is substituted.
- Semisimple target: `hH2 : IsSemisimpleGroupScheme H2`.
- Conclusion: `IsSemisimpleGroupScheme H1`.
- Semisimple, solvable, and derived clauses use the existing definitions in
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`. IsSemisimpleGroupScheme contains
  smoothness, connectedness, affineness, local finite type and quasi-compactness,
  and requires every smooth connected solvable normal closed subgroup to be terminal
  over F. IsSolvableGroupScheme means `∃ n, GroupSchemeDerivedLength G n`.
  A successor uses IsDerivedGroupScheme; its factorization/minimality conditions
  are exactly the smallest closed subgroup through which groupSchemeCommutator
  factors. That commutator is `fst * snd * fst⁻¹ * snd⁻¹`. The zero step is terminality.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the dependency's
  AlgebraicClosure record also explicitly identifies IsAlgClosed as its closed-field
  clause. The construction AlgebraicClosure itself is not required here.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.IsMonHom`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: IsSubgroupScheme,
  IsClosedSubgroupScheme, IsNormalSubgroupScheme, reused inside the semisimple predicate.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: GrpObj.ker,
  the pullback with the unit.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: Smooth.
- `Mathlib.Topology.Connected.Basic`: ConnectedSpace.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: LocallyOfFiniteType;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: QuasiCompact.
- `Mathlib.AlgebraicGeometry.Scheme`: Scheme and Scheme.Hom; affineness via IsAffine.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: IsSemisimpleGroupScheme,
  IsSolvableGroupScheme, GroupSchemeDerivedLength, IsDerivedGroupScheme,
  groupSchemeCommutator. The entire definition module and its recorded node were read.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`: Scheme.Hom.ΓAlgebra,
  defined by the canonical ΓSpecIso and the structure map appTop, with its toModule.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: RingHom.FaithfullyFlat.

The statement modules are reached by the two public imports. The sole proof dependency
`lem-sfb-semisimple-isogeny-invariance` has no lean record or mathlib_match and no
existing theorem was found. It introduces no missing notion needed to type this item;
its unavailable proof-module import is omitted, as the stage-2 import rule applies to
proof dependencies that are already stated. Its exact specialization and all matching
hypotheses are recorded in the theorem docstring, following the node's complete proof.
No helper or dependency module is needed.

Edge cases checked before writing: identity isogeny; trivial source and target;
positive characteristic including SL_p → PGL_p with nonreduced kernel μ_p;
noncentral finite kernels are not excluded by any binder; G_m × S → S fails the
finite-dimensional-kernel condition as it should. The kernel is a closed subgroup of
an affine group, so its global sections really are its coordinate algebra. Empty
schemes are excluded by connectedness (and cannot be group schemes over a field).
The derived-length zero case permits the trivial group. No characteristic or kernel
order restriction occurs. All type variables and the universe u are explicit,
and `set_option autoImplicit false` guards this.

Searches for an existing declaration:

- msearch.py leanfinder: "A faithfully flat homomorphism of smooth connected affine
  algebraic groups with finite kernel and semisimple target has semisimple source".
  Eight hits, concerning smooth algebras and semisimple rings/modules; no group-scheme theorem.
- msearch.py loogle: `"IsSemisimple", "isogeny"`: zero hits.
- msearch.py grep: `isogeny|IsSemisimpleGroupScheme`: zero Mathlib hits.
- rg of WeilConjectures and Sheaf for semisimple, isogeny and the item id, plus grep
  of the item id in WeilConjectures: no theorem matching this statement. Found the
  reusable semisimple definition module, the central-isogeny multiplicativity theorem
  (a different conclusion), and CentralTorusDerivedProduct (a consumer of this lemma).
- rg of dag/lean_names_upstream.json and both source trees for the chosen declaration
  name: no collision. The invariance node has no Lean record. The live-source wrapper
  check for Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleIsogenyInvariance reports
  that module unavailable, consistent with the node record and source search.

Validation: scompile.py Q12 lem-sfb-semisimple-isogeny-source on the delivered module
passed both sandbox and library compilation, each in 1.5 seconds, without warnings.
No statement dispute or source correction is required. The reference example
CompactObject.lean is now withdrawn; its path was read, and the current module-mode
header requirements and the landed Semisimple/SemisimplePerfect modules were followed.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
