## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.PerfectFieldSemisimpleCommutativeTest`
states `AlgebraicGeometry.perfectField_semisimple_iff_commutativeNormalSubgroups_trivial`.
It has one theorem with proof `sorry`, no new definitions, and a docstring containing
all six steps of the accepted split. The node's natural-language statement and
accepted proof are unchanged.

The inherited BLOCKED ending concerned stage-1 re-splitting. The current
`coord/brief-stage2.md` §0 explicitly distinguishes that from a stage-2 assignment.
The live item has an accepted stage-1 review and no Lean record; no released repair
note exists for this item. This delivery supplies its first Lean statement and
preserves that split.

Clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`. `[PerfectField k]` means exactly every
  irreducible polynomial over k is separable, as the class field
  `PerfectField.separable_of_irreducible` states. No characteristic restriction occurs.
- The group scheme is `G : Grp (Over (Spec (.of k)))`. Its bundled group structure
  is `GrpObj G.X`, with multiplication, identity and inverse as in the recorded
  group-scheme dependency. All schemes and test algebras use the field universe u;
  the algebraic closure also lies in `Type u`. There is no smaller independent
  test universe that could make the condition vacuous.
- Smoothness is `[Smooth G.X.hom]`; affineness is `[IsAffine G.X.left]`.
  Finite type is `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Geometric connectedness is the explicit `hconn : ConnectedSpace
  ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left`.
  This is precisely connectedness after extension to the fixed algebraic closure,
  as specified in the node, rather than an assumption that k is algebraically closed.
- The equivalence is `↔`. Clause (1) is `IsSemisimpleGroupScheme` applied to the
  same base-changed group. Reading that definition shows smoothness, connectedness,
  affineness, finite type, and triviality of every smooth connected solvable closed
  normal subgroup. Its additional structural conjuncts follow from the given
  hypotheses and the stipulated geometric connectedness. Its `IsSolvableGroupScheme`
  is finite `GroupSchemeDerivedLength`, using `IsDerivedGroupScheme` to require the
  smallest closed subgroup through which `groupSchemeCommutator` factors. Thus it
  uses the exact derived-series, scheme-theoretic meaning in the node.
- Clause (2) quantifies `∀ (N : Over (Spec (.of k))) [GrpObj N] [IsCommMonObj N]`.
  The first two binders give every k-group scheme, and `IsCommMonObj N` is the
  equality of multiplication with its swapped multiplication, not commutativity
  merely on k-rational points.
- The inclusion is `(i : N ⟶ G.X)` with `IsClosedSubgroupScheme i` and
  `IsNormalSubgroupScheme i`. The recorded classes include preservation of the
  group law and injectivity on every commutative k-algebra's points; closedness is
  a closed immersion and normality is normality of every such image.
- Its smoothness, connectedness, affineness and finite type are respectively
  `Smooth N.hom`, `ConnectedSpace N.left`, `IsAffine N.left`, and
  `LocallyOfFiniteType N.hom → QuasiCompact N.hom` as successive hypotheses.
- The conclusion is `IsIso η[N]`. Here `η[N]` is the group identity section from
  the tensor unit of `Over (Spec k)`, namely the identity k-scheme `Spec k`, to N.
  An isomorphism in the slice is exactly an isomorphism of the underlying schemes
  commuting with the structure maps. Thus this is the stated identity morphism
  being an isomorphism, retaining infinitesimal structure.
- No splitness or reductivity premise occurs, and the trivial group is included.

Dependencies and imports used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; this is the recorded
  Mathlib match, and `PerfectField` is Mathlib.FieldTheory.Perfect.
- `def-sc-group-scheme`: `CategoryTheory.Grp` and `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp; `CategoryTheory.IsCommMonObj`,
  Mathlib.CategoryTheory.Monoidal.Mon. These are publicly available through
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme`,
  `AlgebraicGeometry.IsClosedSubgroupScheme`, and
  `AlgebraicGeometry.IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. Read all three definitions,
  including their quantification over all commutative k-algebras.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-weil-algebraic-closure`: `AlgebraicClosure`,
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure; also read `IsAlgClosure` in
  Mathlib.FieldTheory.IsAlgClosed.Basic.
- Added already-landed statement dependencies `def-sfb-semisimple-group-scheme`
  and `def-sfb-tori-multiplicative-type`, under brief §5's authorization to cite
  landed notions. Their declarations are `AlgebraicGeometry.IsSemisimpleGroupScheme`
  (and its derived-series predicates) in Sheaf.AlgebraicGeometry.GroupScheme.Semisimple,
  and `AlgebraicGeometry.MultiplicativeType.baseChange` in
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. The latter is literally
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp`:
  canonical pullback with its transported group operations. Both definitions and
  their source docstrings were read in full. No new definition nodes are needed.
- The stated proof dependency `def-sfb-solvable-group-structure` is imported without
  `public` as Sheaf.AlgebraicGeometry.SolvableGroupStructure. The recorded subgroup
  and spectrum proof dependencies are already supplied by public imports. The four
  other proof dependencies (products, arbitrary-field derived group, radical base
  change, universal characteristic invariance) have no Lean records in the current
  snapshot, so there are no modules for them to import yet. They are proof inputs,
  not missing notions needed to state this theorem.

Edge cases checked against the definitions and source:

- G = 1 is allowed: its geometric radical is trivial, and every closed subgroup
  is trivial; no positive dimension or nontriviality assumption was added.
- A positive-dimensional smooth connected commutative group, such as G_m or G_a,
  fails the test via its identity inclusion, consistently with not being semisimple.
- Smoothness and connectedness of N are both retained. Milne Remark 19.4 gives
  the disconnected center of SL_2 and, in characteristic 2, its nonsmooth connected
  mu_2 as reasons neither can be omitted. `IsIso η[N]` detects scheme structure.
- Characteristic p is allowed for every perfect field. No Lie algebra criterion,
  reductivity, splitness or characteristic-zero premise is substituted.
- A group object has an identity section, so the empty scheme cannot occur. The
  connected-space encoding agrees with the node's nonempty convention.
- Using the fixed canonical algebraic closure excludes no case: the source defines
  semisimplicity after any fixed algebraic closure, and the chosen closure exists
  in the same universe. The subgroup test covers all u-small schemes, matching
  the ambient category of schemes in which G is given.

Source check: read the local Milne PDF by `pdftotext -layout`: 6.44 (printed p.135)
for geometric semisimplicity, Propositions 19.1 and 19.2(a) (pp.397--398) for radical
base change over a perfect field, Proposition 19.3 and its complete proof (p.398)
for the equivalence, and Remark 19.4 for the hypothesis edge cases. The Lean says
exactly this source statement in the affine finite-type setting of the node.
No statement correction or STATEMENT-DISPUTED flag is needed.

Searches actually run:

- `msearch.py`, leanfinder: "A smooth geometrically connected affine group scheme
  over a perfect field is semisimple if and only if all smooth connected commutative
  closed normal subgroups are trivial". Eight hits, all on Lie-algebra semisimplicity,
  Killing forms or related Lie-module properties; no algebraic-group criterion.
- `msearch.py`, loogle: `"GroupScheme", "semisimple"`. Zero hits.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry:
  `semisimple.*commutative|commutative.*semisimple|PerfectField`. Six hits, concerning
  the smooth locus over a perfect field, not this criterion.
- `rg -n` in lean/WeilConjectures and lean/Sheaf for
  `semisimple.*commutative|commutative.*semisimple|perfect_field_semisimple|perfectField_semisimple|lem-sfb-perfect-field-semisimple-commutative-test`:
  no hits before creating the module.
- Concept/name searches in both GroupScheme directories for `semisimple`,
  `Semisimple`, `Solvable`, `solvable`, and `IsDerived` found the existing
  Semisimple, SolvableGroupStructure and ToriMultiplicativeType definitions used
  here, and other specialized structure theorems; none gives this equivalence.
- The item's existing Mathlib search records were read and left unchanged.

Validation: `scompile.py Q21 lem-sfb-perfect-field-semisimple-commutative-test`
compiled the delivered module in both sandbox and library positions on the server
with no errors or warnings. All variables and universes are explicit, with
`set_option autoImplicit false`. Every line of the Lean module is at most 100 columns.
The single theorem's postponed proof is the only `sorry`.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
