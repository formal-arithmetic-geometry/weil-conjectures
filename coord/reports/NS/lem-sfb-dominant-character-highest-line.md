## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.DominantCharacterHighestLine`
states `AlgebraicGeometry.RationalHighestWeight.dominant_character_highest_line`.
Its sole proof is `sorry`. It introduces no definitions, constructions, instances,
or auxiliary theorems. The node statement and proof plan are unchanged; its only
changes are `lean` and the added statement dependencies
`def-sfb-rational-highest-weight-data` and `def-sfb-rank-one-root-interfaces`,
both already landed with Lean records. This repair also supplies a §1(B)
module and lean-only record repair for `lem-sfb-reductive-borel-pair-structure`.

The source was read directly in `literature/milne-algebraic-groups_iAG2017.pdf`
(pdftotext pages containing printed pp.463--470): Theorems 22.2--22.3,
Definition 22.16, Proposition 22.17, Theorems 22.18--22.20, and
Lemmas 22.24--22.26. In particular, primitive means a Borel eigenvector,
Theorem 22.20 supplies every dominant character, and its proof includes the
torus-times-simply-connected cover. The node asks only for a rational module
with such a line, not simplicity or uniqueness; neither is added.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Algebraically closed field F | `{F : Type u} [Field F] [IsAlgClosed F]` |
| Reductive F-group scheme | `G : Grp (Over (Spec (.of F)))` and `hG : ReductiveTorusCentralizer.IsReductive G` |
| Smooth, connected, affine, finite type, no nontrivial smooth connected normal unipotent subgroup | The recorded `IsReductive` predicate, using `SolvableGroupStructure.IsAlgebraic` and `IsUnipotent`; over algebraically closed F its geometric formulation is equivalent to the node's formulation |
| Specified maximal split torus | `T`, `iT`, `hT`, and `hsplit` |
| Specified Borel containing it | `B`, `iB`, `j`, `hB`, `hj : j ≫ iB = iT` |
| U is the unipotent radical | `U`, `iU`, `hUclosed`, `hUnormal`, `hUsmooth`, `hUconnected`, `hUunipotent`, and the universal maximality condition `hUmax` |
| Projection p with kernel U, identity on T, and semidirect decomposition | `p`, `hp`, `hker`, `hdecomp`, exactly the splitting interface of `reductive_borel_pair_structure` |
| Simple roots and coroots as in that dependency | The actual additive character/cocharacter Hom groups, `Φ`, `P : RootDatum ...`, `b : P.Base` |
| These roots belong to the given group and Borel | `aG`, `aB`, `haG`, `haB` pin the actions to conjugation; `hroot` identifies roots with actual characters; `hweights` makes them exactly the nonzero tangent character weights; `hpositive` pins positivity to Lie(B) |
| Pairing is the actual integer character/cocharacter pairing | `hpair`, composition equals the integer power of the identity of G_m |
| Coroots are those of the group, including central directions | `act : RankOneRoots.Weyl iT →* Aut T` and `hact` identify the Weyl action with conjugation by every normalizer representative on every test scheme; `s` and `hs` identify each simple reflection on every actual character with `P.reflection` |
| Character lambda | `lam : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)` |
| Nonnegative simple-coroot pairings | `hdominant : ∀ α : b.support, 0 ≤ P.toLinearMap (Additive.ofMul lam) (P.coroot α)` |
| Nonzero finite-dimensional vector space V | Existential `V`, its `AddCommGroup`, `Module F V`, `FiniteDimensional F V`, and `v ≠ 0`; a nonzero vector already implies V is nonzero |
| Rational G-action | The linear coaction `c` into `V ⊗[F] coordinateAlgebra G`, together with `HopfAction.Coassociative` and `HopfAction.Counital`, on the canonical coordinate Hopf algebra |
| Extended character lambda composed with p | `p ≫ lam`, whose regular character function is `characterElement (p ≫ lam)` |
| For every commutative F-algebra A and b in B(A), b(v tensor 1) is the character scalar times v tensor 1 | `(coordinateMap iB).toLinearMap.lTensor V (c v) = v ⊗ₜ[F] characterElement (p ≫ lam)`; this is the universal coaction equality, as explained below |
| Fv is B-stable with that character | The preceding equality fixes the character, and `IsStable ((coordinateMap iB).toLinearMap.lTensor V ∘ₗ c) (F ∙ v)` explicitly asserts line stability |
| U acts trivially on Fv | `v ∈ invariants c (iU ≫ iB)` says the restricted coaction takes v to v tensor 1; linearity gives the same identity on Fv |
| Every characteristic and the trivial group | No characteristic, root-rank, dimension-of-G, or nontrivial-group restriction |

The universal tensor equality is exactly the all-algebras eigenvector identity.
For a point b, pullback on global functions gives F[B] → A. Applying it to the
coefficient tensor factor gives b acting on v tensor 1 on the left, and the
value of lambda(p(b)) times v tensor 1 on the right. Conversely test the
original identity at A = F[B] and its universal point. Thus the displayed
coaction identity neither adds nor drops a hypothesis or a scalar extension.
It even covers test algebras in larger universes, since evaluation of the finite
tensor identity works in any F-algebra; it does not restrict the statement to
rational points or reduced rings. Tensor factor order is the node's V tensor A.

The explicit `IsAffine` instances for G, B, U supply coordinate rings. They are
already implied by reductivity and the closed subgroup inclusions; they are
not extra mathematical assumptions. The commutative-group-object witnesses for
T and G_m expose the character lattices, exactly as in the recorded Borel-pair
dependency. No assumption of semisimplicity, simple connectedness, root spanning,
or complete reducibility is imposed. The finite-lattice and reducedness
conclusions of the dependency need not be separate hypothesis binders because
the pinned actual roots already have those properties.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (full class signature and docstring).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; its splitting definition
  is equivalent to the node's root formulation. The node's algebraic-closure
  match also lists this declaration explicitly, so no closure is chosen here.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj`,
  `IsCommMonObj`, and group-object morphisms. Read also the terminology docstring
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`, full signature and proof
  docstring; its public dependencies provide the Borel, reductivity, torus and
  tangent-character notions. Its radical and root-datum clauses are used verbatim.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `coordinateAlgebra`, `coordinateHopf`, `coordinateMap`, `characterElement`,
  `IsStable`, `invariants` in `AlgebraicGeometry.RationalHighestWeight`, all read
  with definitions/docstrings. The existing `HasHighestWeight` predicate is
  deliberately not used: it asserts a one-dimensional entire invariant space,
  which this node does not require.
- `Sheaf.RingTheory.HopfActionModuleData`: `HopfAction.Coassociative` and
  `HopfAction.Counital`; read their actual tensor associativity and unit formulas.

Plain proof imports retain the already recorded proof dependencies:
`SimplyConnectedCharacterLattice`, `HomogeneousLineBundleSections`, the upstream
`Cohomology.DirectImage.FiniteFreeComplex`, Mathlib `Morphisms.Smooth`, and
`Geometrically.Connected`. The other proof dependencies have no recorded module
in the read repository: fundamental-ray-regular-power,
normal-big-cell-character-functions, reductive-torus-simply-connected-cover,
central-isogeny-borel-root-compatibility, central-kernel-cyclic-representation-descent,
and split-lattice-torus-projection. They remain explicit in the proof docstring
and unchanged in `proof_deps`; none is needed for elaborating the statement.
No import cycle is introduced. The maintainer may add those proof imports when
the remaining statements land. The Weyl-compatible Borel-pair dependency module is described below; no new node is needed.

Edge cases checked before writing:

- Trivial G: T, B, U are trivial; Φ and the simple-root support are empty,
  dominance is vacuous, and V = F, v = 1 with trivial coaction has all clauses.
- A torus with positive-dimensional center: roots can be empty without the
  character lattice being zero. No root-spanning or semisimple condition occurs;
  a one-dimensional representation of the arbitrary character works.
- Lambda = 1 (additively zero): V = F with trivial action is allowed.
- Arbitrary positive characteristic: no `CharZero`, separability of an isogeny,
  or division by a regularizing exponent is used in the statement or proof plan.
- Nonreduced A: the coefficient identity tests the full scheme action and
  detects infinitesimal group elements. A = 0 gives equality in the zero tensor
  module automatically. No `Nontrivial A` is assumed.
- V = 0 cannot witness the conclusion because `v ≠ 0` is required. No assertion
  that all U-invariants form a line or that V is irreducible is added.
- Universes: F and the group schemes have arbitrary `u`; an existential
  finite-dimensional vector space can always be represented in `Type u` by
  finite coordinates. There is no small-test-algebra quantifier making a
  hypothesis vacuous, because the conclusion is the universal coefficient identity.

Searches (2026-10-24):

- msearch LeanFinder: “Every dominant character of a reductive algebraic group
  occurs on a Borel stable line in a finite dimensional rational representation”.
  Eight hits concern finite abstract groups or characteristic-zero Lie modules;
  no algebraic-group existence statement in arbitrary characteristic.
- msearch Loogle: `Representation, Comodule, GrpObj`; zero hits, with unknown
  identifier `Comodule` reported by the search service.
- msearch Mathlib grep: `dominant.*character|highest.*weight|structure.*Comodule`.
  Six hits in Lie comments or highest-weight Young tableaux, no matching theorem.
- msearch LeanSearch: “A dominant algebraic group character is the weight of a
  Borel stable line in a finite dimensional rational representation”. Eight hits
  concern abstract representation characters, Lie weights or character spaces.
- `rg` in `lean/WeilConjectures` for rational representations/coactions and the
  item id: existing general-linear representation API, no matching theorem.
- `rg` in `lean/Sheaf` for the same notions and dominant/highest combinations:
  found and reused `RationalHighestWeightData`; `SimpleModuleDualHighestWeight`
  starts from a given simple representation and does not supply this existence
  theorem. `RhoSectionModules` cites this item in its proof, not as an existing
  statement. No competing declaration named `dominant_character_highest_line`
  is present in Mathlib, the source library, or Sheaf.
- Read `dag/lean_names_upstream.json` by matching dominant/highest declaration
  names: no matching existence declaration. The added dependency is an existing
  landed node, not a new notion or private duplicate.

The returned head had the H3 interface fault detailed below. It is repaired
without changing either mathematical node statement. There is no outstanding
STATEMENT-DISPUTED flag and no statement_change is needed for a lean-only repair.
The example CompactObject module is withdrawn in the current read clone; its
node record was read, and the delivered module follows the live module header,
public statement imports, source docstrings, and exposed-public-section convention.

Validation: the repaired dependency and item were each compiled by scompile.py
against the live server sources and published build, in dependency order, with
no errors or warnings (6.4 seconds for the dependency and 9.6 for the item).
All variables and universes are explicit; all delivered Lean lines are at most
100 characters. The repaired packet passed deliver2.py --no-push preflight
and compilation (`OK (dry run)`, commit 80b2102e7d2). The normal delivery
repeats those checks before pushing.

## Second reading by NS

This is the dispatcher's single-worker self-audit, not an independent agent review;
the brief prohibits starting another agent and assigns the independent review to
the maintainer. I reopened the node and the complete Lean signature after the
successful compile of the repair. The table above checks every hypothesis and conclusion.
In particular I checked the actual, rather than arbitrary, pairing/root data;
the direction of the Borel character (no inverse); the whole-radical invariant
condition; and the absence of an irreducibility or one-dimensional-full-invariants
conclusion. The first delivery incorrectly treated roots and their pairing as
sufficient to pin coroots. The return's central-torus counterexample disproves
that claim. This reading checked hact and hs against BottSamelsonGalleryGeometry
and the canonical dependency output; their binder types agree exactly. The
counterexample is now excluded by its action on the central character.


## Return repaired: H3 at immutable head 96406c7b0b1c

The retained sandbox was the returned version. The live read repository has no
Lean record for the item, and the server source fetched with
`scompile.py --source Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`
agrees with the read clone's Borel-pair module. Node copies in this packet have
been refreshed from current main; all fields except the authorized lean records
and the item's added stmt_deps are preserved. This is a substantive interface
repair, not a rebase-only or unchanged re-push.

The return is correct: in SL2 times G_m, roots ±(2,0) and fake coroots ±(1,k)
can satisfy the root-pairing rules without being the group's coroots. At k=1,
lambda=(-1,1) has fake pairing zero and would incorrectly be declared dominant.
The repaired item adds the exact `act`, `hact`, `s`, `hs` binders of
`BottSamelsonGalleryGeometry`, with P and b in place of D and base. For the
central character chi=(0,1), actual normalizer conjugation fixes chi. The fake
reflection sends it to (-2,1), so it cannot satisfy hs with hact. More generally,
root nonzeroness and character-lattice torsion freeness make the functional
chi ↦ <chi,alpha∨> recoverable from the reflection on all characters. The
perfect character/cocharacter pairing then fixes the coroot. Thus hdominant
now measures genuine group dominance.

Read source: Milne Theorem 21.11(d)--(e), printed pp.428--429, expressly gives
the normalizer representative and the unique coroot from its action on every
character; §§21.29--21.35 supply the Borel's positive system. This is precisely
the canonical coroot notion already named in the node, not a new mathematical
hypothesis. The item now cites the existing definition node
`def-sfb-rank-one-root-interfaces` and publicly imports its module. Its full
statement and recorded declarations were read: Character, Cocharacter,
normalizer, torusInNormalizer, Weyl and the actual test-scheme point-image
conditions. Search of the live Sheaf modules found this exact interface in
BottSamelsonGalleryGeometry; no duplicate definition or new node was introduced.

## Dependency modules

`lem-sfb-reductive-borel-pair-structure`: the previous recorded declaration
exhibited an abstract root datum whose roots and pairing were pinned, but did
not retain its rank-one Weyl reflections. This was insufficient for consumers
requiring canonical coroots in the presence of a central torus. The new module
`Sheaf.AlgebraicGeometry.GroupScheme.CanonicalReductiveBorelPairStructure`
states `AlgebraicGeometry.canonical_reductive_borel_pair_structure`. Its full
conclusion is the previous Borel-pair theorem's conclusion, followed within the
root-datum existential by `act`, `s`, `hact`, and `hs`. Its inputs are unchanged:
an algebraically closed field, reductive G, and every specified split Borel pair.
The original Borel existence, flag quotient and right-torsor properties, maximal
smooth connected normal unipotent radical, splitting projection, character and
cocharacter lattices, finite reduced root datum, actual pairing, conjugation
weights and Borel-positive base are all retained clause for clause.
Semisimple-implies-reductive and both old declarations remain publicly accessible
from the old module imported by the new module; no old signature is changed.
Only this dependency node's `lean` record changes, with the required explanatory
note. The item's public import is switched to this repaired interface.

The new declaration has its own source/blueprint docstring and the complete
proof plan of the owning node, including the additional retention of the
rank-one Weyl action and reflections rather than an unsupported claim that an
arbitrary abstract root datum supplies them. Its sole proof is sorry. It
imports the already stated reductive_rankOne_reflections as a proof dependency.
The node's original proof already cites that rank-one theorem, so no new
proof-dependency edge is needed. No data is selected from a mere existence
proof and no new definition is introduced.

## Citer validation

Filtering every DAG node's stmt_deps and proof_deps for this item gives exactly
three genuine citers. Other grep hits are provenance or via fields rather than
uses of this theorem. Each genuine citer still holds:

- `lem-sfb-rho-section-modules`: its input IsRhoBorelPair is exactly maximal split
  torus plus Borel inclusion. First apply semisimpleGroupScheme_isReductive;
  then canonical_reductive_borel_pair_structure supplies the radical, p, actual
  datum and the four new Weyl/reflection arguments for that same pair. The
  usual half-sum calculation is then in this canonical datum, so m rho is
  dominant and the repaired theorem applies. The already landed signature has
  no externally supplied arbitrary root datum, so no new user hypothesis is
  needed. Its proof is still sorry and needs no signature edit.
- `lem-sfb-induced-composition-linkage`: its semisimple simply connected S and
  specified pair meet the same canonical dependency inputs. The theorem's Weyl
  group is explicitly N_S(T)(F)/T(F) acting by inverse conjugation, so the
  canonical act/hact and the simple reflections are precisely the ones its
  proof uses to show -w0 eta dominant. No Lean record yet exists for this citer;
  the repaired dependency now supplies the required interface for its statement.
- `lem-sfb-top-bottom-cohomology-simple-image`: likewise its root datum and Weyl
  group are the group's canonical datum and normalizer action. Choose them
  together using canonical_reductive_borel_pair_structure. The dominant x and
  its highest-line invocation then use those same coroots; no extra condition
  is required and its asserted representation-theoretic conclusions are unchanged.
  This citer also has no Lean record yet.

Consumer interface validation: both repaired modules compiled together, with the
new dependency's existential `act`, `s`, conjugation clause and simple-reflection
clause having exactly the binder types consumed by the item. For an arbitrary
specified pair, the root-data existential of the canonical theorem returns
these simultaneously, rather than asserting they exist for the earlier arbitrary
coroot choice. Extract its quotient/radical/root tuples, install the returned
commutativity instances and the implied affine instances, and pass the returned
haG/haB/hroot/hpair/hweights/hpositive/act/hact/s/hs directly to the item. This
is the construction available to all three citers above. The original Borel-pair
interface alone cannot supply that construction, which is why this delivery
includes its §1(B) repair.

The empty-root and torus cases still have empty s and no hs obligations; the
normalizer action is the actual action, and arbitrary torus characters remain
allowed. The trivial group, lambda zero, every characteristic and the full
scheme-theoretic coaction conditions remain as in the first delivery. No
caller node is edited and no mathematical statement is weakened.
