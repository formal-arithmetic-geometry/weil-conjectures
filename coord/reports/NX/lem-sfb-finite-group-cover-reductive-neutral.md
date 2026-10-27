## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.FiniteCoverReductiveNeutral states
AlgebraicGeometry.finiteGroupCover_reductive_neutral. Its single theorem has `sorry`;
there are no new definitions or auxiliary assertions. The node's mathematical statement,
proof and proof dependencies are unchanged.

Clause-by-clause reading:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The affine F-group schemes U,V are `Grp (Over (Spec (.of F)))` with
  `[IsAffine U.X.left]`, `[IsAffine V.X.left]`. Bundled group objects use the
  recorded GrpObj group diagrams, including identity and inverse.
- Finite type is `[LocallyOfFiniteType ...] [QuasiCompact ...]` for both structure
  morphisms. No connectedness is assumed of U or V.
- The homomorphism is `(q : U ⟶ V)`. Finiteness is `[IsFinite q.hom.hom.left]`;
  between affine schemes this is precisely module finiteness of the coordinate
  ring map. Underlying-space surjectivity is `[Surjective q.hom.hom.left]`.
- Smoothness of U is `[Smooth U.X.hom]`.
- U^0 is the existing `GrpObj.identityComponent U.X`, whose underlying scheme is
  the open subscheme of the connected component of `GrpObj.onePoint U.X`. The
  existing group structure and inclusion `GrpObj.identityComponentι` are used.
- The variable H and homomorphism i into V are identified with the actual reduced
  identity component by the scheme isomorphism e and inclusion equation hi.
  Its specified scheme is `(GrpObj.identityComponent V.X).left.nilradical.subscheme`;
  its inclusion is reduction immersion followed by identity-component inclusion.
  This is (V_red)^0: reduction preserves the underlying space and commutes with
  restriction to this open subset. The equation fixes both the structure map and
  the induced group law; neither H nor i is an arbitrary unrelated substitute.
  These are presentation data for the node's named H, not extra group-theoretic
  assumptions. Every H in the node has such a presentation.
- Reductivity of H is `ReductiveTorusCentralizer.IsReductive H`. Its existing
  definition requires smooth affine finite type, connectedness after algebraic
  closure, and triviality of every smooth connected normal unipotent closed
  subgroup after that closure. Smooth unipotence is tested by faithful matrices
  on geometric points, as in the node; it does not restrict the kernel of q.
- The first conclusion supplies `f : Grp.mk (GrpObj.identityComponent U.X) ⟶ H`.
  The equality `f.hom.hom ≫ i.hom.hom = identityComponentι U.X ≫ q.hom.hom`
  asserts that f is precisely the restriction of q. The two following conjuncts
  assert its finiteness and surjectivity.
- The final conjunct is `IsReductive (Grp.mk (GrpObj.identityComponent U.X))`.
  There is no separability, centrality, smoothness or reducedness condition on
  the finite kernel, and no characteristic restriction.

Dependencies read and used:

- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`,
  `IsAlgClosure`, and AlgebraicClosure.lean, `AlgebraicClosure`. The current
  theorem uses algebraic closedness; the existing reductivity predicate uses the
  canonical algebraic closure.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, `Spec` and `Spec.map`.
- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, `Grp`, and
  its homomorphisms; WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documents
  the specialization to schemes over a field and IsMonHom.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, `Smooth`.
- def-weil-connected-scheme: Mathlib.Topology.Connected.Basic, `ConnectedSpace`,
  including nonemptiness; it occurs in the identity-component and reductivity APIs.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  `IsOpenImmersion`; canonical identity-component inclusion is an open immersion.
- The existing identity-component construction is read in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic: `identityComponentOpens`,
  `identityComponent`, its GrpObj instance, and `identityComponentι` with IsMonHom.
- Added the already landed def-sfb-reductive-torus-centralizer-terminology to
  stmt_deps to cite the exact predicate in
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology,
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`. Its underlying
  `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent` definitions were read.
- Added the already recorded def-weil-pbc-scheme-reduction to stmt_deps to cite
  Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme: `Scheme.nilradical`,
  `IdealSheafData.subscheme`, and `IdealSheafData.subschemeι`.

All stated proof dependencies are imported privately, including the identity-component,
component-translate, homomorphism-factorization, flatness, reducedness and Artinian-ring
modules. lem-sfb-unipotent-normal-quotient-image currently has no Lean or Mathlib record,
so its proof import is omitted; it is not a statement prerequisite and no assertion of
that node is duplicated here. The theorem docstring carries all seven proof steps,
including its use. The parent consumer QuasiReductiveSpecialConnectedness uses a closed
reduced subgroup with precisely the neutral-component image; such a presentation gives
the H used here by the reduction universal property.

Source checked: https://arxiv.org/pdf/math/0405381, Proposition 4.3, first paragraph
of proof, printed p.8 (PDF page 8), specifically the equal-dimension unipotent-radical
argument. The source PDF is absent locally. The accepted DAG expands this into the
finite-cover specialization and the component restriction; neither the source nor
that expansion excludes an infinitesimal kernel.

Edge cases: the identity group and finite constant smooth groups give trivial neutral
components and are retained. Positive-characteristic Frobenius on G_m has kernel mu_p
and is retained. SL_2 to PGL_2 in characteristic 2 is retained. G_a to the trivial group
is excluded by the finite-morphism hypothesis. Group identity points exclude the empty
scheme, without an additional nonemptiness binder. No connectedness of V or reducedness
of V is imposed; its reduced component is presented exactly by e and hi. All universes
and variables are explicitly bound and autoImplicit is false.

Searches run for this item (2026-10-24):

- msearch LeanFinder, query "finite surjective homomorphism of smooth affine algebraic
  groups with reductive reduced identity component implies reductive identity component":
  eight unrelated reducedness/smoothness/affine-space results, no theorem match.
- msearch Loogle, query "IsReductiveGroupScheme, GrpObj.identityComponent": no hits,
  unknown identifier IsReductiveGroupScheme.
- msearch grep, query "reductive|Reductive", Mathlib AlgebraicGeometry: zero hits.
- msearch LeanSearch, query "Finite surjective algebraic group homomorphism preserves
  reductivity of the neutral component": eight ring-finiteness or abstract-group hits,
  no algebraic-group reductivity theorem.
- rg of lean/WeilConjectures and lean/Sheaf for reductivity, identityComponent and
  unipotence found the exact existing reductivity predicate and canonical identity
  component. The central-isogeny theorem additionally assumes a central kernel and
  does not give this result; the present theorem is not duplicated.
- rg of lean/WeilConjectures for the exact node id returned no matching declaration.
- DAG searches found the already landed reductive terminology and scheme reduction
  nodes, so no new definition node is introduced.

Validation: scompile.py compiled both the sandbox and named library module cleanly
against the live server library (9.6 s and 16.1 s). No errors or non-sorry warnings.

## Second reading by NX

No second worker was started: the dispatcher brief explicitly forbids it. The maintainer's
independent delivery review supplies the independent reading. The clause-by-clause
self-check above was made with the node and Lean file open; no statement correction
or mathematical discrepancy was found.
