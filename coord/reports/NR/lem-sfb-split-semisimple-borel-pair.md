## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitSemisimpleBorelPair` states
`AlgebraicGeometry.split_semisimple_borel_pair`, with its proof left as `sorry`.
`IsSplitSemisimpleBorelPair` is a transparent conjunction packaging the properties
of these chosen maps in this theorem, not a replacement definition of any group-theoretic
notion. All its data are actual existing objects and maps; it contains no proof hole.

Hypothesis-by-hypothesis correspondence:

- The arbitrary field is `{k : Type u} [Field k]`.
- The k-group schemes are `G T : Grp (Over (Spec (.of k)))`. Their morphisms are
  morphisms of group objects, not arbitrary maps on rational points.
- Smoothness and connectedness of G are `hGsmooth : Smooth G.X.hom` and
  `hGconnected : ConnectedSpace G.X.left`.
- Affineness is `hGaffine : IsAffine G.X.left`; finite type is exactly
  `hGfinite : LocallyOfFiniteType G.X.hom` plus `hGqc : QuasiCompact G.X.hom`.
- Semisimplicity after algebraic closure is `hGsemisimple : IsSemisimpleGroupScheme`
  applied to the scalar extension of G to `AlgebraicClosure k`. The recorded definition
  uses absence of nontrivial smooth connected solvable normal closed subgroup schemes,
  with solvability given by termination of the scheme-theoretic commutator series.
  Its smoothness/affineness/finite-type clauses on that extension follow from the already
  stated properties of G; they do not add a mathematical assumption.
- The subgroup T is `iT : T ⟶ G`, with `hTclosed`. Splitness is `hTsplit`, an
  isomorphism with the recorded rank-r split torus, with r any natural number.
  Geometric maximality is `hTmaximal`, the existing maximal-torus predicate on the
  pulled-back inclusion over the algebraic closure, exactly as in the node.

Clause-by-clause correspondence (unfold `IsSplitSemisimpleBorelPair`):

- Existential B, U, iB, j, iU, p give the chosen groups, inclusions and projection.
  `j ≫ iB = iT` retains the given subgroup T, including its embedding.
- Closedness is asserted for iB, j and iU. Smoothness and geometric connectedness
  are asserted for T, B and U by `Smooth` and `GeometricallyConnected` on their
  structural morphisms. Normality of U in B is `IsNormalSubgroupScheme iU.hom.hom`.
- `IsSplitSolvable B` is the dependency's actual finite smooth connected descending
  series with closed normal successors and represented fppf G_a or G_m quotients.
- For EVERY algebraically closed extension `F : Type u`, the pulled-back inclusion
  iB satisfies the recorded `IsBorelGroupScheme`, which includes maximality among
  smooth connected solvable closed subgroups using the commutator-series definition.
- The following universally quantified V and iV clause says that every smooth
  connected normal closed unipotent subgroup of B_F factors through the actual
  inclusion iU_F. U_F itself has all these properties: the same pair properties are
  asserted for every field extension L, including L=F. Hence this is largestness,
  not only maximality or an upper bound with no radical properties.
- `SolvableGroupStructure.IsUnipotent U` is exactly smooth faithful matrix geometric
  unipotence. The recorded definition quantifies over algebraically closed extensions,
  requires a closed matrix representation and `(r(x)-1)^N=0` with `0 < N`.
- `j ≫ p = 𝟙 T` is the retraction onto the specified torus.
- `IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X]` identifies U with the
  SCHEME-THEORETIC kernel in schemes over k, retaining its specified inclusion.
- The `IsIso` clause uses the actual multiplication morphism
  `(fst ≫ iU) * (snd ≫ j) : U.X ⊗ T.X ⟶ B.X`, whose point formula is ut.
  With normality of U this is precisely the semidirect-product assertion: transporting
  the group law of B along this scheme isomorphism gives
  `(u,t)(u',t')=(u(tu't⁻¹),tt')`. This uses the given inclusions, so the action is
  conjugation, not an arbitrary or unspecified action. As in the existing
  `reductive_borel_pair_structure` interface, no second semidirect-product object is needed.
- The final `∀ (L : Type u) [Field L] [Algebra k L]` reapplies ALL pair properties
  to the images of these same five maps under the recorded scalar-extension functor.
  This explicitly preserves the kernel, retraction, inclusions, multiplication
  isomorphism, split-solvable series, unipotence and geometric assertions.
- There is no characteristic-zero, perfectness or simple-connectedness binder.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `CategoryTheory.GrpObj` and `Grp`,
  Mathlib.CategoryTheory.Monoidal.Grp; closed/normal subgroup predicates,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `IsSplitSolvable` and `SplitSolvableLength`,
  Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions (original statement dependency).
- `IsSemisimpleGroupScheme` and `IsSolvableGroupScheme`,
  Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.
- `IsBorelGroupScheme`, Sheaf.AlgebraicGeometry.GroupScheme.Borel.
- `ReductiveTorusCentralizer.IsMaximalTorus`,
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology.
- `MultiplicativeType.baseChange`, `splitTorus`, `IsTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType.
- `SolvableGroupStructure.IsUnipotent` and `IsFppfQuotient`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure.

The five existing definition nodes for these notions were added to stmt_deps;
none is redefined or repaired. `GeometricallyConnected` is Mathlib's definition.
Plain proof imports are the recorded modules of the currently stated proof dependencies:
`GeometricallyConnected.of_connectedSpace_of_section`,
`reductive_borel_pair_structure`, `semisimpleGroupScheme_isReductive`,
`RelativeSplitTorus.matrix_sheaf_classification`, `IsProper.isStableUnderBaseChange`,
`affine_normal_quotient_geometry`, and
`AffineGroupDualNumberCalculus.exists_compatible_calculus`.
The other proof dependencies currently have no Lean record and introduce no notion
needed for this statement; their six-step proof plan is retained in the docstring.

Source check: read the local Milne PDF at printed pp.433--435 (PDF pp.445--447).
Corollary 21.30 gives existence over k; 21.32--21.33 identify geometric Borels;
21.34 gives split solvability from the regular-cocharacter decomposition. The
recorded proof supplies the unipotent radical and base-change clauses via 13.33.
The auxiliary nodes are the existing definitions already used elsewhere in the library.

Edge cases checked: rank r=0 is allowed by `r : ℕ`, with the recorded empty-product
split torus; the trivial semisimple group is not excluded; U=1 and B=T are permitted;
`IsSplitSolvable` permits the zero-length series. No nonzero dimension or positive-rank
assumption is imposed. Faithful matrix unipotence allows all characteristics, including
SL_2 in characteristic 2; no differential of a character is used. Arbitrary imperfect
base fields are permitted. Field extensions and all subgroup tests use the same ambient
universe as the existing group-scheme/scalar-extension interfaces, with arbitrary u;
there is no independent smaller test universe. Nilpotent test algebras are retained by
the subgroup and scheme-kernel predicates, and the multiplication isomorphism is on
schemes, not just geometric points.

Searches (prescribed msearch.py, group NR and this item):

- LeanFinder: “A split maximal torus of a semisimple algebraic group is contained in
  a split Borel with unipotent radical and semidirect product decomposition” — 8 hits,
  Lie-algebra Cartan/Geck/root-space results, not this group-scheme theorem.
- Loogle: `"Borel", "IsSolvable"` — 0 hits.
- Mathlib grep: `Borel.*(torus|solvable)|[Ss]plit.*[Bb]orel`, AlgebraicGeometry — 0 hits.
- LeanSearch: “A split semisimple group has a Borel subgroup containing a split
  maximal torus over an arbitrary field” — 8 hits on semisimple modules, abstract
  simple groups and splitting fields; none matches the statement.
- rg in WeilConjectures/ and Sheaf/: `split_semisimple_borel`, the item id,
  `split.*[Bb]orel|[Bb]orel.*split`. Existing reductive_borel_pair_structure is over
  an ALGEBRAICALLY CLOSED field; SplitReductiveCharacteristic.Pair only packages
  part of the output and its theorem has a different hypothesis and additional
  Picard-sequence conclusions. Neither is this theorem. Their primitive notions
  have been reused. No upstream occurrence of the item id was found.
- Exact proposed names searched in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: neither new declaration exists.

No statement correction, new independent notion, dependency repair or disputed
statement is needed. The mathematical node statement and proof remain unchanged.

## Second reading by NR

Reread the node and final module side by side, checking every binder and conjunction
against the correspondence above. In particular, the geometric predicates quantify over
all algebraically closed extensions, the radical has a largestness factorization, the
kernel is a pullback and the scalar-extension clause uses the ORIGINAL maps. The
semidirect law is determined by the specified multiplication map and normality, as in
the library's existing interface. No clause was dropped and no characteristic assumption
was added. No independent agent was started, as required by the dispatcher's brief;
the maintainer performs the independent delivery review.

Validation: prescribed scompile.py completed successfully on 2026-10-24 for the
single delivered module, both sandbox and actual library-module phases, with no
errors or unexpected warnings. Only `lean` and the permitted additions of existing
landed definition nodes to `stmt_deps` differ from the base node. All Lean lines
are at most 100 characters and `autoImplicit` is disabled.
