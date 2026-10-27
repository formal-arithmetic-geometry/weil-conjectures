## Worker report

The module states `AlgebraicGeometry.isTorus_of_central_extension`, with its only
proof `sorry`. It defines no new notion. The node statement and dependencies are
unchanged. Source read: Milne, Algebraic Groups (2017), Lemma 16.43, printed p.340;
Theorem 12.23 and the preceding torus criterion, printed p.240; Theorem 17.82,
printed p.379. The module docstring gives the five steps of the recorded proof.
No statement dispute or correction is needed.

Each hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary field k | `{k : Type u} [Field k]`, with no characteristic restriction |
| k-group schemes E, T, S | `E T S : Over (Spec (.of k))`, each with `GrpObj` |
| All groups affine | `[IsAffine E.left]`, `[IsAffine T.left]`, `[IsAffine S.left]` |
| All groups of finite type | `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism |
| E smooth | `[Smooth E.hom]` |
| E connected | `[ConnectedSpace E.left]`, which includes nonemptiness |
| Closed torus subgroup T → E | `i : T ⟶ E`, `[IsClosedSubgroupScheme i]`, and `hT : MultiplicativeType.IsTorus (Grp.mk T)`; closed subgroup supplies `IsMonHom i` |
| q a group homomorphism E → S | `q : E ⟶ S` and `[IsMonHom q]` |
| S is a torus | `hS : MultiplicativeType.IsTorus (Grp.mk S)` |
| q faithfully flat | `[Flat q.left] [Surjective q.left]`, precisely flat and surjective on underlying spaces |
| q finitely presented | `[LocallyOfFinitePresentation q.left] [QuasiCompact q.left] [QuasiSeparated q.left]` |
| T central on every k-algebra A | `hcentral`, quantifying over `A : Type u`, `CommRing A`, `Algebra k A`, and all points t and e, with `(t ≫ i) * e = e * (t ≫ i)` |
| Points over A | Morphisms from `StandardGroupSchemes.affine k A`, the existing algebra spectrum over k; multiplication is the existing `MonObj` scoped point-group multiplication |
| Scheme-theoretic kernel exactly T with its given inclusion | `hker : ∃ f : Grp.mk T ≅ Grp.mk (GrpObj.ker q), f.hom.hom.hom ≫ GrpObj.kerι q = i`; thus not merely an abstract isomorphism or equality on field-valued points |
| Kernel is fibre over identity | `GrpObj.ker q` is by definition `pullback q η[S]` in the slice; `GrpObj.kerι q` is its first projection |
| Torus means split over algebraic closure, some r ≥ 0 | The existing `MultiplicativeType.IsTorus` uses `baseChange (K := AlgebraicClosure k)` and `∃ n : ℕ, Nonempty (... ≅ splitTorus ... n)` |
| Conclusion E is a k-torus | `MultiplicativeType.IsTorus (Grp.mk E)` |

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, `Grp.mk`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `Hom.group`;
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj.ker`,
  `GrpObj.kerι` (def-sc-group-scheme). Imported through the recorded group-scheme interface.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, including its `IsSubgroupScheme` and `IsMonHom` inheritance
  (def-sc-group-scheme-subgroup).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`
  (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (def-weil-connected-scheme).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.IsTorus`, `baseChange`, `splitTorus`
  (def-sfb-tori-multiplicative-type).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.affine`,
  `multiplicative`, `multiplicativeGroup` (def-sc-gm-ga); the torus definition
  uses this precise multiplicative group, and the theorem uses its canonical affine test schemes.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`
  (def-weil-algebraic-closure), used by the torus predicate.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst` (def-pc-fibre-product), through the canonical kernel definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat` (def-weil-flat-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation` (def-sbc-locally-finite-presentation).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
  These implement def-weil-pbc-scheme-conventions, whose record is a convention
  rather than a separate declaration. Its finite-presentation conjunction is explicit.

Statement dependencies are public imports, directly or via the defining module.
The stated proof dependencies are imported non-publicly:
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`GeometricallyConnected.of_connectedSpace_of_section`),
`Mathlib.AlgebraicGeometry.Morphisms.Proper`
(`IsProper.isStableUnderBaseChange`; smooth base change is in the public Smooth import),
`Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.of_comap_surjective`, with the base-change instance
`Module.FaithfullyFlat.instTensorProduct` imported through its Basic dependency),
`Mathlib.GroupTheory.FiniteAbelian.Basic`
(`AddCommGroup.equiv_free_prod_directSum_zmod`), and
`Sheaf.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension`
(`commutative_multiplicativeType_extension`).
`Flat.SpecMap_iff` is in the public Flat import. The two proof-only nodes
lem-sfb-diagonalizable-group-geometric-criteria and
lem-sfb-multiplicative-extension-action-rigidity currently have no Lean record;
there is no module to import for them, and neither is required to type this statement.

Edge cases checked before writing:

- Rank zero is included by `splitTorus k 0`, the trivial group; trivial kernel,
  trivial quotient, and the entirely trivial sequence are not excluded.
- Positive characteristic and imperfect fields are permitted. No rational-point
  density or algebraic-closedness hypothesis is imposed.
- Nonreduced test algebras are included by `CommRing A` with no reducedness assumption.
  Centrality is not restricted to k-points or field-valued points.
- The empty scheme is excluded by the node's own connectedness hypothesis; group
  schemes also have their identity section. No extra nonemptiness binder is added.
- The universe u is explicit and shared by k, the schemes, and their test algebras,
  matching the recorded subgroup interface and its affine Yoneda tests. There is
  no independently smaller algebra universe that could make centrality vacuous.
- `hker` preserves the inclusion, so an unrelated torus abstractly isomorphic to the
  kernel cannot satisfy the hypothesis with the wrong subgroup embedding.

Searches for an existing statement:

- msearch.py leanfinder, query “A central extension of algebraic tori over a field
  is a torus”: 8 hits, including abstract `GroupExtension`, cyclic-center quotients,
  Hilbert 90 and root data; no algebraic-group-scheme theorem matching the node.
- msearch.py loogle, query `"torus", "extension"`: 0 hits.
- msearch.py grep, query `torus|multiplicative.type|central.extension`, subdirectory
  `AlgebraicGeometry`: 0 Mathlib hits.
- msearch.py leansearch, query “A smooth connected affine group scheme that is a
  central extension of two tori is a torus”: 8 hits (abstract group extensions,
  Lie groups, analytic tori, and Lie algebra extensions); no matching statement.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`
  for `central.extension|centralExtension|IsCentral|IsTorus|is_torus|isTorus`:
  existing torus definition and maximal-torus/centralizer consumers, but no matching
  central-extension theorem. `rg` over both full roots for the new declaration
  and module names found no collision. Search for the blueprint item id in the
  upstream root found no declaration.

Validation: prescribed scompile.py passed both sandbox and actual module-name
compiles, with no errors or non-sorry warnings. One elaboration repair was required:
an isomorphism's `.hom` is a morphism in `Grp`, so extracting its underlying slice
morphism uses `.hom.hom.hom` on the isomorphism, rather than `.hom.hom`.

## Second reading by Q90

A separate reading pass by this worker reopened the node and final source; no
second agent was started, as the dispatch brief forbids it. The maintainer supplies
the independent review. The table above checks every hypothesis and conclusion.
In particular, this pass checked all three finite-type assumptions, all three
finite-presentation conditions on q, pointwise centrality over every commutative
algebra, and the inclusion-compatible kernel isomorphism. The node is unchanged,
no definition was copied, and the sole theorem remains postponed by `sorry`.
The only source edit after the first compile corrected the kernel isomorphism's
projection depth; it did not change its mathematical meaning.
