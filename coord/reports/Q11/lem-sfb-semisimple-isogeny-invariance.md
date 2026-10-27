## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SemisimpleIsogenyInvariance` states
`AlgebraicGeometry.isSemisimpleGroupScheme_of_faithfullyFlat_finite_kernel`.
Its only proof is `sorry`; it introduces no definitions or auxiliary theorems.
The node's mathematical statement is unchanged. Added the already landed definition node
`def-sfb-semisimple-group-scheme` to `stmt_deps` to cite its exact predicates, as authorized
by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES).

Clause-by-clause correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The two F-group schemes are `G1 G0 : Over (Spec (.of F))` with `GrpObj` instances.
  The scheme universe is the field universe, as in the recorded group-scheme interface;
  `u` is arbitrary.
- Affineness is `[IsAffine G1.left] [IsAffine G0.left]`.
- Finite type is `[LocallyOfFiniteType Gi.hom] [QuasiCompact Gi.hom]` for each i.
- Smoothness is `[Smooth Gi.hom]` and connectedness is `[ConnectedSpace Gi.left]`.
  These include the nonempty clause in the recorded connectedness definition.
- The homomorphism is `(f : G1 ⟶ G0) [IsMonHom f]`; its base compatibility is encoded
  by the Over morphism, and multiplication/unit compatibility by IsMonHom.
- Faithful flatness is `(hff : f.left.appTop.hom.FaithfullyFlat)`. RingHom.FaithfullyFlat
  equips the codomain F[G1] with the module structure induced by f* : F[G0] → F[G1]
  and asserts Module.FaithfullyFlat for exactly that action.
- Finite scheme-theoretic kernel is `[IsFinite (GrpObj.ker f).hom]`. GrpObj.ker is
  the pullback of f and the target unit section in Over (Spec F), not a kernel on
  rational points. IsFinite for its structure map means finite coordinate algebra
  over F: IsFinite gives affineness and a finite ring map on the sole affine base.
  Over a field this is exactly finite-dimensionality. The recorded def-sc-group-scheme
  explicitly specifies this encoding. No reducedness or centrality instance is imposed.
- Target semisimplicity is `(hG0 : IsSemisimpleGroupScheme G0)` and the conclusion is
  `IsSemisimpleGroupScheme G1`. The imported predicate includes exactly smooth,
  connected, affine, finite type and triviality of every smooth connected solvable
  normal closed subgroup. Solvability is finite termination of GroupSchemeDerivedLength;
  IsDerivedGroupScheme says smallest closed subgroup factoring the commutator morphism.
  Triviality is terminality over Spec F, not a rational-point cardinality condition.

Dependencies read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, class signature and docstring.
- `def-weil-algebraic-closure`: the algebraically closed clause is `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, with its polynomial-splitting definition and
  equivalent root formulation. A chosen algebraic closure is not needed here.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp;
  `CategoryTheory.IsMonHom`, Mathlib.CategoryTheory.Monoidal.Mon;
  `CategoryTheory.GrpObj.ker`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp;
  `AlgebraicGeometry.IsFinite`, Mathlib.AlgebraicGeometry.Morphisms.Finite.
  These are publicly supplied by WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-finite-type-morphism`: AlgebraicGeometry.LocallyOfFiniteType and
  AlgebraicGeometry.QuasiCompact in their recorded Mathlib morphism modules.
- `def-sbc-smooth-morphisms`: AlgebraicGeometry.Smooth,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth, the affine-local smooth-ring-map class.
- `def-weil-connected-scheme`: ConnectedSpace, Mathlib.Topology.Connected.Basic,
  extending PreconnectedSpace with Nonempty.
- `def-sc-group-scheme-subgroup`: AlgebraicGeometry.IsSubgroupScheme,
  IsClosedSubgroupScheme and IsNormalSubgroupScheme in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; signatures and pointwise
  injectivity/normality definitions read in full. Used through the semisimplicity predicate.
- Added `def-sfb-semisimple-group-scheme`: AlgebraicGeometry.IsSemisimpleGroupScheme,
  IsSolvableGroupScheme, GroupSchemeDerivedLength, IsDerivedGroupScheme and
  groupSchemeCommutator, Sheaf.AlgebraicGeometry.GroupScheme.Semisimple. All five
  definitions and their source docstrings were read, and none is copied here.

Proof dependencies with recorded declarations are imported privately:
`Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage`
(affineGroupHom_exists_faithfullyFlat_closedImmersion),
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (IsClosedImmersion),
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`
(Smooth.geometricallyReduced), `Mathlib.RingTheory.Artinian.Module`
(IsArtinianRing.equivPi), and `WeilConjectures.Mathlib.RingTheory.Nullstellensatz`
(exists_algHom_ker_eq_of_isMaximal and the other two recorded clause declarations).
The proof-only node `lem-sfb-solvable-normal-image-geometry` currently has neither
Lean record nor Mathlib match; consequently there is no module to import for it.
It is not needed to type this statement, and is retained in the proof plan and proof_deps.
The theorem docstring carries all five proof steps of the DAG, including this input.

Source checked directly by pdftotext of PDF pages 411–413, especially PDF page 412 /
printed p.400, Milne Lemma 19.14 and its proof. It gives exactly target-semisimple
implies source-semisimple. The inherited blueprint.from.place sentence claiming the
PDF reverses G and G-prime is incorrect (also noted by the stage-1 review); no
mathematical correction or statement_change is required, and that metadata was not edited.

Edge cases checked before writing: the identity isogeny, the trivial group, and
positive-characteristic Frobenius isogenies. The kernel can be nonreduced (for example
central μ_p in SL_p → PGL_p), and no separability or prime-to-characteristic condition
is present. Finite smooth connected subgroups over an algebraically closed field are
trivial; the finite kernel itself is not assumed smooth. Empty schemes cannot carry
the unit section of an F-group scheme, consistently with ConnectedSpace. A nontrivial
torus cannot map faithfully flat with finite kernel to the trivial group; the finite
kernel hypothesis excludes that false extension. Non-surjective subgroup inclusions
are excluded by faithful flatness. All u are allowed. No statement dispute remains.

Searches performed with the prescribed msearch.py (Q11, this item):

- leanfinder: “A faithfully flat homomorphism of smooth connected affine algebraic groups
  with finite kernel and semisimple target has semisimple source”. Eight results:
  smooth-algebra flatness, ring/module semisimplicity and cotangent results; no match.
- loogle: “AlgebraicGeometry.IsSemisimple, AlgebraicGeometry.IsSolvable,
  CategoryTheory.GrpObj.ker”. Zero hits; unknown identifier AlgebraicGeometry.IsSemisimple.
- grep: “IsSemisimpleGroupScheme|semisimple.*isogeny|isogeny.*semisimple”. Zero Mathlib hits.
- leansearch: “A smooth connected affine group scheme with finite kernel over a
  semisimple group is semisimple”. Eight hits concerning abstract finite simple groups,
  smooth morphisms, modules and Lie algebras; no scheme-theoretic theorem.
- rg in lean/WeilConjectures and lean/Sheaf for semisimple, solvable, derivedSubgroup,
  isogeny, and specifically semisimple.*isogeny / isogeny.*semisimple. Found the existing
  semisimplicity definition and SemisimpleCentralIsogenyMultiplicative, whose theorem
  assumes both groups semisimple and adds centrality, so it does not state this item.
- grep -rn for the item ID in lean/WeilConjectures returned no matches. The upstream
  name index has no matching semisimple-group predicate or new theorem name.
- rg in dag/nodes for IsSemisimpleGroupScheme / IsSolvableGroupScheme located the
  existing definition node, which is cited rather than duplicated.

Validation: scompile.py checked the sandbox form and the final module form separately
against the live server library, in 1.7 s and 1.8 s, with no diagnostics.

## Second reading by Q11

The dispatcher forbids starting another agent; this is an explicit second pass by the
same worker, not a claim of independent review. The maintainer's delivery review supplies
that independence. Reopened the exact node and module and checked the field, all group
geometry binders, the Over homomorphism, coordinate-ring action, pullback kernel and
semisimplicity implication against the clause list above. The existing semisimplicity
predicate was unfolded by reading its source: it retains scheme-theoretic solvability,
normality and terminality. No extra centrality, reducedness, characteristic-zero or
rational-point hypothesis is present. Repeated geometry binders for G0 match the node's
stated setting, although hG0 also entails them. The finite morphism encoding is the one
specified in the recorded group-scheme dependency, and equivalent to finite-dimensional
kernel coordinate algebra. No mismatch or new declaration was found in this second pass.
