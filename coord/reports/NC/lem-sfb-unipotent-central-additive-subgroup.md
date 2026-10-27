## Worker report

The module `Sheaf.AlgebraicGeometry.UnipotentCentralAdditiveSubgroup` states
`AlgebraicGeometry.exists_central_additive_subgroup_of_unipotent`, with one named theorem
and its proof `sorry`. It introduces no definitions. The natural-language statement and
accepted proof split are unchanged. `stmt_deps` gains the already landed definition node
`def-sfb-solvable-group-structure`, whose recorded `IsUnipotent` is reused rather than copied.

Clause-by-clause reading:

- A field k is `{k : Type u} [Field k]`. Perfectness is `[PerfectField k]` from
  Mathlib.FieldTheory.Perfect: the standard equivalent separability definition. Its
  characteristic-zero instance and positive-characteristic PerfectRing equivalence give
  exactly the node's characteristic-zero-or-surjective-pth-power condition.
- The k-group scheme V is `(V : Grp (Over (Spec (.of k))))`. This bundles precisely
  the recorded `GrpObj` structure on a scheme over k and group-scheme homomorphisms.
- Affineness is `[IsAffine V.X.left]`. Finite type is
  `[LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]`, the recorded conjunction.
- Smoothness is `[Smooth V.X.hom]`; connectedness is `[ConnectedSpace V.X.left]`.
  ConnectedSpace includes nonemptiness.
- Geometric unipotence is `hunipotent : SolvableGroupStructure.IsUnipotent V`.
  Its source definition was opened in full. It asks for a closed faithful representation
  into finite GL_n and `(rho(x)-1)^N = 0` for some positive N at every point over every
  algebraically closed extension. This is exactly the smooth affine situation of the node.
  Its smoothness conjunct repeats an already given hypothesis without restricting it.
- Nontriviality is `hnontrivial : ¬ Nonempty (V ≅ Grp.trivial _)`, in the category
  of group schemes over k. The trivial group object has underlying Spec k.
- The conclusion binds `(N : Grp (Over (Spec (.of k)))) (i : N ⟶ V)`.
  `IsClosedSubgroupScheme i.hom.hom` renders the closed subgroup inclusion with
  its existing compatibility and pointwise injectivity requirements.
- `Smooth N.X.hom ∧ ConnectedSpace N.X.left` renders both properties of N.
- `Nonempty (Grp.mk (StandardGroupSchemes.additive k) ≅ N)` gives an isomorphism
  a : Ga -> N in the category of k-group schemes, using the recorded additive Hopf law.
- The final universal quantification is over `(R : Type u) [CommRing R] [Algebra k R]`,
  `n : Spec R -> N` and `v : Spec R -> V`, all over k. Its equality
  `(n ≫ i.hom.hom) * v = v * (n ≫ i.hom.hom)` is exactly centrality in V(R).
- No dimension restriction, characteristic restriction, commutativity assumption on V,
  or field-only restriction on the algebra points appears.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj, Grp, Grp.mk, Grp.trivial.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsClosedSubgroupScheme,
  IsSubgroupScheme, IsMonHom; point groups come from the group-object API.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.Topology.Connected.Basic: ConnectedSpace.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  LocallyOfFiniteType and QuasiCompact.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: StandardGroupSchemes.additive,
  StandardGroupSchemes.additiveGroup. The underlying affine object and the coordinate
  comultiplication, counit and antipode were read, not inferred from their names.
- Sheaf.AlgebraicGeometry.SolvableGroupStructure: SolvableGroupStructure.IsUnipotent.
  Its GL_n uses WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear and
  GeneralLinearGroup.homMulEquiv, whose full signatures and docstrings were read.
- Mathlib.FieldTheory.Perfect: PerfectField.

The public import supplies statement dependencies transitively. Private imports retain the
three currently stated proof inputs: NilpotentConnectedCentralSeries,
CharZeroCommutativeUnipotentVectorGroup, BoundedExponentReducedPKernel. Their theorem
signatures and proof docstrings were opened. The other three proof nodes
lem-sfb-geometric-unipotence-unitriangular-embedding,
lem-sfb-unitriangular-coordinate-filtration and lem-sfb-perfect-exponent-p-vector-group
have no recorded Lean module on the read base, so there is no module to import for them.
They remain unchanged proof dependencies, and the theorem docstring includes all six
steps of the accepted proof with the node names.

Source checks: opened Milne's PDF via pdftotext, including Corollary 14.55 and its proof
on printed p.297, Proposition 14.54 on the same page, and the first paragraph of the
Proposition 14.32 proof and Corollary 14.33 on printed p.289. The latest blueprint's
direct-image stability statement and proof supply the inherited support-chain context.

Edge cases checked mathematically before writing: V = 1 is explicitly excluded, while
Ga is included; arbitrary positive dimensions are allowed, including noncommutative
unitriangular groups. Characteristic zero and every prime characteristic are included.
Smooth connected zero-dimensional groups over a perfect field are trivial, so the
nontriviality condition excludes them for the stated mathematical reason, without an
added dimension hypothesis. Nonreduced algebras and the zero algebra are included in
centrality, not merely geometric field points. The same arbitrary universe u is used for
the field, schemes and algebra tests, matching the recorded subgroup API; tests cannot
be vacuous from being placed in a smaller independent universe.

Searches made using the prescribed msearch.py wrapper:

- leanfinder, "Every nontrivial smooth connected unipotent algebraic group over a perfect
  field contains a central closed subgroup isomorphic to the additive group Ga": eight
  hits about Cartan subalgebras, special-linear centers, the absolute Galois group,
  root-pairing radicals and abstract nilpotence; none states the algebraic-group result.
- loogle, `"Unipotent", "Subgroup"`: zero hits.
- grep, `unipotent|Unipotent|AdditiveGroup`, AlgebraicGeometry: zero hits in Mathlib.
- leansearch, "Every nontrivial smooth connected unipotent group over a perfect field
  contains Ga in its centre": eight hits about abstract subgroup centers, upper central
  series and finite p-groups; no match.
- rg over lean/WeilConjectures and lean/Sheaf for unipotence and central additive
  subgroup terminology: found the reusable SolvableGroupStructure.IsUnipotent, existing
  standard group schemes, and the characteristic-zero vector-group proof input; no
  theorem with the item's statement. The exact blueprint-id search in WeilConjectures
  had no hits. The proposed theorem name has no upstream-name index match.

No STATEMENT-DISPUTED issue or source correction is needed. No new node or dependency
repair module is needed; the one added statement dependency already exists and is landed.

Validation: scompile.py compiled the delivered module on the server in 2.5 seconds,
with no reported errors or unexpected warnings. Its local attempt reported disk full,
then its built-in current-server-source fallback succeeded. The prescribed deliver2.py
--no-push dry run passed preflight and compilation (commit 2647f5b56ee).

## Second reading by NC

Self-check with the node and final Lean file open; no separate agent was started, as
required by the dispatcher. The maintainer supplies the independent delivery review.
Rechecked the field/perfectness binders, smooth connected affine finite-type assumptions,
faithful geometric matrix unipotence, exclusion of the trivial group scheme, all four
existence/property clauses for N and Ga -> N, and the commutation equality for all
commutative algebra points. All correspond exactly to the node as enumerated above.
The only bookkeeping addition is the existing node defining IsUnipotent in stmt_deps.
There are no private definitions, local notation, auto-bound variables or additional
hypotheses. No mismatch or statement correction was found.
