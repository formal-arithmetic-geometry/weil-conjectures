## Worker report

The module `Sheaf.AlgebraicGeometry.IrreducibleGroupQuasiCompact` states
`AlgebraicGeometry.compactSpace_of_irreducible_groupScheme`. Its only postponed proof is
this theorem, with `sorry`; there are no definitions or helper theorems. The declaration's
source and complete five-step natural-language proof are in its docstring. The node's
statement, statement dependencies, proof and proof dependencies are unchanged.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`, with arbitrary explicit universe u and arbitrary
  characteristic. This is precisely def-weil-field, using Mathlib's `Field`.
- The k-group scheme H is `(H : Over (Spec (CommRingCat.of k))) [GrpObj H]`.
  `Over` supplies the structure morphism H.hom. Its cartesian tensor is the fibre product
  over Spec k; `GrpObj` extends `MonObj` by inversion and the inverse equations.
  The multiplication, unit and associativity axioms are inherited from `MonObj`.
  This uses exactly the interface recorded in def-sc-group-scheme, not a pointwise
  topological-group structure on the points of H.
- Irreducibility of the underlying space is `[IrreducibleSpace H.left]`.
  `H.left` is the underlying scheme, coerced to its underlying topological space.
  The Mathlib class includes nonemptiness and preirreducibility; the open-intersection
  condition is equivalent to the node's condition on two closed subsets.
- The conclusion is `CompactSpace H.left`. Mathlib does not require Hausdorffness in
  this class. Its field `isCompact_univ` means compactness of the whole underlying space;
  `isCompact_iff_finite_subcover` in `Mathlib.Topology.Compactness.Compact` identifies
  this exactly with every open cover having a finite subcover.
- The final sentence explicitly excludes finite-type, smoothness and reducedness
  assumptions: the theorem has no such binders. Commutativity, separatedness,
  algebraic closedness and perfection are likewise not assumed.

The source was read in `literature/stacks-project/groupoids.tex`, at
`lemma-irreducible-group-scheme-over-field-qc` (Tag 0B7P): it states exactly this
implication for any field. The recorded DAG proof expands its argument without changing
its statement. No statement correction or disputed statement is needed.

Dependency declarations read and used:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs`, inherited through the public
  algebraic geometry imports.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, `Mathlib.CategoryTheory.Monoidal.Grp`;
  `CategoryTheory.MonObj` in `Mathlib.CategoryTheory.Monoidal.Mon` supplies the
  multiplication/unit diagrams. The full source documentation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` confirms this exact specialization
  to `Over (Spec (.of k))`. Unused terminology in that multi-notion definition node
  (finite group schemes, order, etaleness, kernels) is not a hypothesis here.
- def-weil-irreducible-components: `IsIrreducible`, `irreducibleComponents` and
  `IrreducibleSpace`, `Mathlib.Topology.Irreducible`. The class has precisely the
  nonempty irreducible-space meaning described by that node's mathlib_match.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. These definitions were read;
  their module is publicly imported as recorded. The present absolute quasi-compactness
  assertion uses `CompactSpace`, rather than asserting finite type or quasi-compactness
  of the identity map. In particular this is a substantive conclusion.

The additional public `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` import supplies
cartesian group-object infrastructure. Proof-only imports preserve the available DAG plan:
`Mathlib.AlgebraicGeometry.Geometrically.Integral` (def-pc-geometrically-irreducible),
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
(lem-sc-scheme-over-field-universally-open), `Mathlib.AlgebraicGeometry.Pullbacks`
(def-pc-fibre-product, lem-weil-pbc-fibre-product-affine-spectra and
lem-weil-pbc-open-fibre-product), `Mathlib.AlgebraicGeometry.PullbackCarrier`
(lem-weil-pbc-open-fibre-product and lem-weil-pbc-surjective-base-change), and
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`
(lem-weil-pbc-reduction-universal-homeomorphism). The public FiniteType import already
supplies Scheme, Spec and `compactSpace_iff_exists`, for def-pc-scheme,
def-weil-affine-spectrum and lem-weil-pbc-quasicompact-affine-surjection.
The two proof-only nodes lem-sfb-group-local-minimal-prime and
lem-sfb-scheme-large-algclosed-jacobson have no recorded Lean declaration or Mathlib match
in the read repository, so there is no module for either to import. They are not needed to
elaborate the statement. No statement dependency is missing or has an unusable interface.

Edge cases checked before writing:

- The trivial group Spec k is included and is compact.
- Nonreduced irreducible finite group schemes such as alpha_p and mu_p in characteristic
  p are included; nothing imposes reducedness or characteristic zero.
- Infinite-type affine group schemes, for example the additive group of the polynomial
  algebra on infinitely many primitive variables, are included. Its spectrum is
  irreducible and compact, so finite type would have been an unjustified restriction.
- The empty scheme is excluded by the actual irreducibility hypothesis and cannot carry
  the unit of a group scheme over a nonzero field; no extra nonemptiness assumption is
  added. Arbitrary reducible groups are not claimed compact by this theorem.
- The universe u is explicit, shared by the base field and schemes as in Mathlib's
  scheme-over-field API. There is no test-algebra quantifier in a smaller universe.
- `CompactSpace` imposes no separation condition, as necessary for scheme topology.

Searches made on 2026-10-24 (all prescribed msearch.py calls use group Q123 and this item):

1. leanfinder: `An irreducible group scheme over a field is quasi compact`.
   Eight hits: general quasi-compactness/affineness and integral-scheme irreducibility,
   including `compactSpace_iff_quasiCompact` and `Scheme.compactSpace_of_isAffine`.
   None asserts this implication for group schemes.
2. loogle: `CategoryTheory.GrpObj, CompactSpace`. Zero hits.
3. grep: `[Ii]rreducible|[Qq]uasi[Cc]ompact|CompactSpace`, subdirectory
   `AlgebraicGeometry/Group`. Four hits: three in Abelian.lean about irreducible images
   in a rigidity proof and one descent use of QuasiCompact in Smooth.lean; no match.
4. leansearch: `Irreducible group schemes over fields are quasi compact`. Eight hits
   describing QuasiCompact, affine/noetherian compactness and compact-space equivalences;
   no group-scheme implication.
5. Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`:
   `irreducible.*([Gg]roup|[Cc]ompact)|([Gg]roup|[Cc]ompact).*irreducible|compactSpace_of_irreducible`.
   No matching theorem. The identity-component consumer cites this DAG node in its proof
   docstring; the GL_n characteristic-zero component lemmas and other hits impose
   different hypotheses. Direct grep of this item id in WeilConjectures has no hits.
6. Exact proposed declaration name `compactSpace_of_irreducible_groupScheme` searched
   in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json: no existing name.

## Second reading by Q123

A separate reading pass by the same worker compared the completed file with the node and
Stacks Tag 0B7P. No other agent was started, as required by the dispatcher brief; the
maintainer supplies the independent review. The field binder, Over object with GrpObj,
nonempty irreducibility class, and CompactSpace conclusion match each clause listed
above. In particular, an algebraically closed base field is used only in the proof text,
not in the theorem's assumptions. The conclusion concerns H.left itself, not its
identity morphism. The arbitrary group object is not required commutative or reduced.
All variables/universes are explicit (`autoImplicit false`); there are no local instances,
local notations, private aliases or hidden data constructions. The five proof steps
include the geometric-irreducibility reduction, shear openness, rational intersection,
and affine-source surjection. No mismatch or correction was found in this pass.

## Validation

Every compile uses the prescribed scompile.py against the published server build.
Compiler and delivery results are recorded after validation below.

Server single-file compilation passed with no errors or warnings (3.2 seconds for the
library module after slot acquisition; the wrapper also checked its sandbox probe).
