## Worker report

The module `Sheaf.AlgebraicGeometry.ReductiveNormalSubgroupCentralNeutralTest` states
`AlgebraicGeometry.reductive_normalSubgroup_central_iff_neutralComponent_central`, with
one `sorry` proof. It introduces no definition, axiom, helper theorem or new node.
The original statement and dependency lists are unchanged.

Hypotheses and conclusions, clause by clause:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group schemes are `(G N : Grp (Over (Spec (.of k))))`, using the recorded
  `CategoryTheory.GrpObj` through the bundled `CategoryTheory.Grp`.
- Reductivity is exactly `(hG : ReductiveTorusCentralizer.IsReductive G)`.
  This existing predicate includes affine finite type, smoothness, geometric
  connectedness, and absence of smooth connected normal unipotent subgroups
  after algebraic closure. Over the algebraically closed k this is precisely
  the reductivity described in the item, without a new reductivity predicate.
- The inclusion is `(iN : N ⟶ G)`. Its closedness and normality are respectively
  `hclosed : IsClosedSubgroupScheme iN.hom.hom` and
  `hnormal : IsNormalSubgroupScheme iN.hom.hom`, using the recorded classes.
- The neutral component is `∃ U : N.X.left.Opens` with
  `(U : Set N.X.left) = connectedComponent (GrpObj.onePoint N.X)`.
  Thus the underlying scheme is the actual open subscheme `U.toScheme`,
  over k via `U.ι ≫ N.X.hom`. There is no reduction operation. This is the
  exact open-subscheme description supplied by the identity-component dependency.
- The group structure is `∃ gC : GrpObj (Over.mk (U.ι ≫ N.X.hom))`.
  The composite inclusion into G is
  `Over.homMk (V := N.X) U.ι ≫ iN.hom.hom`. Its two conclusions are
  `@IsClosedSubgroupScheme ... gC G.grp ...` and
  `@IsNormalSubgroupScheme ... gC G.grp ...`. These also assert compatibility
  of its group structure with G. Since iN is an inclusion, compatibility with
  N follows, so gC is the inherited subgroup structure, not an arbitrary group
  structure. Existentially naming U and its group structure avoids imposing
  extra finite-type binders on N merely to instantiate a chosen component API.
- The final `↔` has, on its left, every image of an A-point of N in
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A`, and, on its right,
  every image of an A-point of the open component in that same set.
  In both cases `A : Type u` is any commutative k-algebra. Expanding the
  recorded centralizer predicate quantifies over every commutative k-algebra
  B, every k-algebra map A to B, and every G(B)-point; it asserts `Commute`
  of the extended subgroup point with that point. This is exactly the
  node's further-extension condition: a k-algebra map A to B equips B with
  the requisite compatible A-algebra structure. Neither ring is required
  reduced, nonzero, finite type or a field. Test algebras use the same
  universe u as the scheme and base, as in the recorded subgroup and
  centralizer interfaces, with no independent smaller test universe.
- There are no smoothness, reducedness or additional connectedness hypotheses
  on N or its component, and no characteristic restriction.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (commutative division ring).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (all polynomials split,
  equivalent to the root condition in def-weil-algebraic-closure).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp` and its induced
  group-homomorphism category; these are the def-sc-group-scheme record.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, `IsSubgroupScheme`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive` and `centralizerPoints`.
- `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent`:
  `locallyAlgebraicGroup_identityComponent`; its conclusion supplies the
  very open U, connected-component equality and inherited group structure
  used here. `GrpObj.onePoint` is from its public upstream GroupScheme.Basic
  import. I also read upstream `identityComponentOpens`, `identityComponent`
  and `identityComponentι`: they use the open structure but require finite-type
  instances on N, which need to be derived from hG and hclosed in the proof.

Public imports expose the statement dependencies. Ordinary imports retain the
available proof plan: product irreducibility, central-torus/derived multiplication,
translations of components, kernels (already publicly imported by GroupScheme.Defs),
open factorization, faithfully flat ideal contraction and the finite-type/closed
immersion notions (already public through the statement imports). The proof-only
node lem-sfb-reductive-radical-quotient has no recorded Lean module yet and is
therefore not imported; its role is explicitly preserved in the proof docstring.

Source reading: opened Conrad's original PDF at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . Printed p.100,
Theorem 3.3.4 proof, explicitly gives the centrality equivalence for normal closed
subgroup schemes of a connected reductive group over an algebraically closed
field. Printed p.102, Proposition 3.3.8 proof, explicitly invokes normality of
the identity component in the ambient group. Both apply to scheme-theoretic,
possibly nonreduced subgroups. The six-step natural-language proof in the Lean
docstring follows all six node proof steps and names their input nodes.

Edge cases checked before writing:

- N trivial: the open component and both centrality conditions are trivial.
- N connected: U is top and the two centrality conditions agree; closedness
  and normality reduce to the hypotheses.
- N = G: the equivalence specializes to centrality of G versus its connected
  component, which is G. It does not falsely assert that G is commutative.
- G a torus, including rank zero: every subgroup is central and the assertion
  retains nonreduced subgroups such as mu_p in characteristic p.
- A finite nonreduced central subgroup, e.g. mu_p in SL_p: U is not replaced
  by its reduction; infinitesimal points remain in both centralizer tests.
- Finite disconnected subgroups: U may be just the identity component; no
  connectedness of N is assumed, and all components are covered by the proof.
- The zero test algebra is allowed and represents the empty test scheme.
  A group scheme over a field itself cannot be empty because of its unit.
- In positive characteristic a noncentral Frobenius kernel can be connected;
  neither side is incorrectly made true by testing only rational points.

Searches for an existing statement:

1. `msearch.py ... leanfinder` query: "A normal closed subgroup scheme of a
   reductive group is central if and only if its identity component is central".
   Eight hits, only abstract subgroup-center, commutator and central-series facts;
   no group-scheme centrality criterion.
2. `msearch.py ... loogle` query: `Subgroup.center, Subgroup.Normal`.
   Six hits, e.g. `Subgroup.normal_of_le_center`; none is the scheme theorem.
3. `msearch.py ... leansearch` query: "A normal subgroup scheme of a reductive
   group is central if its identity component is central". Eight abstract-group
   hits (center normality, center and normality definitions); no match.
4. `msearch.py ... grep` query:
   `identityComponent.*(normal|central)|normal.*identityComponent`.
   Mathlib returned zero hits.
5. `rg` of that pattern and the proposed declaration name in both
   `lean/WeilConjectures` and `lean/Sheaf`: only the reduced Hopf/matrix-group
   `Matrix.GeneralLinearGroup.normal_zeroLocus_identityComponent` and its use
   in monodromy; no centrality iff statement. That theorem assumes a radical
   ideal and is not a match for the unreduced scheme-theoretic criterion.
6. `grep -rn` of the item id in `lean/WeilConjectures`: no hits.
7. `rg` for `centralizerPoints`, central/neutral terminology and `IsCentral`
   in the project algebraic geometry modules found the existing centralizer
   definition and its uses (including AdjointKernelCentralQuotientUnipotent),
   which I reuse rather than introducing an IsCentral notion.

No statement fault, missing notion, dependency repair or disputed assertion found.

## Second reading by Q39

I reread the node alongside the finished signature, without starting another agent
(the dispatcher explicitly prohibits subagents). This is a separate self-check;
the maintainer's independent review remains pending. The field and algebraic
closedness, G and N, exact recorded reductivity, closed inclusion and normality
all match. The existential U is an open of N, identified with its identity
component, and its structure map is U.ι followed by N's structure map. Explicit
gC arguments give the inherited group structure to both closedness and normality
conclusions for the same composite into G. The two sides of the iff use the
same ambient centralizer of the identity inclusion, hence centrality in G,
not commutativity within N or within U. The further-extension quantifiers live
inside centralizerPoints and retain all nilpotent and zero test algebras.
No finite-type hypothesis on N, reducedness restriction, rational-point-only
condition or additional conclusion was inserted. No mismatch required changing
the node or its statement. The proof docstring contains the whole six-step
commutator, faithfully-flat descent and open-component assembly argument.

Validation: prescribed scompile.py completed successfully with no errors or unexpected
warnings. Library-mode compile: 2.2 seconds. The prescribed deliver2.py --no-push
reported `OK (dry run)` and confirmed preflight and compilation success.
