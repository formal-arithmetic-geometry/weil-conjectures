## Worker report

Delivered module: `Sheaf.CategoryTheory.CondensedCentralActionDerivedVanishing`.
Main declaration:
`CategoryTheory.CondensedDerivedRestriction.centralAction_derived_vanishing`.
All three theorem proofs are `sorry`; the central operator has real data selected from
an existence-and-uniqueness specification. No node statement or dependency list changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative condensed ring R on the coherent profinite site is
  `A : CategoryTheory.CondensedBar.Ring.{u}`. This existing abbreviation is
  `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})`.
  Its `A.toMon` with the existing `ringComm` instance is precisely a general
  `Profinite.CondensedRing` with commutative multiplication. It does not require a
  presentation by continuous functions into a topological ring.
- The size convention is explicit `universe u`, test objects `Profinite.{u}`, section
  groups in `AddCommGrpCat.{u+1}` and the dependency's ordinary small-Hom derived
  categories `DerivedCategory.{u+1}`. Every variable and universe is bound; the file
  sets `autoImplicit false`. The same size convention as the dependency is retained.
- A topological group J is `{J : Type u} [Group J] [TopologicalSpace J]
  [IsTopologicalGroup J]`. There are no compactness, separation or discreteness instances.
- The internal action module N is `N : Equivariant A J`, the existing abbreviation
  for `Profinite.CondensedAction.ActionModule A.toMon J`. Its section actions are the
  monoid homomorphisms `N.act S : C(S,J) →* Module.End ...`, natural in all test objects.
- The central group element is `(z : J) (hz : ∀ g : J, z * g = g * z)`.
  The equation is exactly membership in the centre, expressed without a subgroup cast.
- The endomorphism z_N is `centralAction N z hz`. The helper
  `existsUnique_centralAction` specifies its value on EVERY profinite section as
  `N.act S (ContinuousMap.const S z) m`; `centralAction_apply` exposes this formula.
  The constant operator is uniquely determined as an actual equivariant internal map,
  and the definition is `Classical.choose` of that unique specification. This does
  not choose an arbitrary endomorphism or replace the operator by a hypothesis.
- Γ_J is the dependency's normalized fully fixed-submodule functor
  `invariants A J`. It uses `FixedAll`, quantifying over all profinite base changes,
  and has the injective invariant inclusion and normalized adjunction.
- RΓ_J is exactly `derived A J`, defined as the ordinary total
  `(invariants A J).functor.rightDerivedFunctor`; no bar/cochain computation is assumed.
- N[0] is `(DerivedCategory.singleFunctor (Equivariant A J) 0).obj N`.
  The map z_N[0] is the `.map (centralAction N z hz)` of that same functor.
- The first conjunct asserts the equality of `(derived A J).map` of this actual map
  with the identity endomorphism of RΓ_J(N[0]), in the derived category itself.
- The second conjunct is the implication
  `IsIso (centralAction N z hz - 𝟙 N) → IsZero (...)`. Its hypothesis is isomorphism
  in the action-module category, not just a sectionwise linear inverse. `IsZero`
  asserts the entire derived object is both initial and terminal, rather than only
  vanishing in an asserted range of cohomological degrees.
- There is no trivial-action, finite-dimensionality, compactness, discreteness or
  nonzero-coefficient hypothesis. The invertibility premise scopes only over the
  vanishing clause, so the identity conclusion holds unconditionally for central z.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`;
  the generic internal module and equivariant-map underlying structures.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, `sectionModule`, `Equivariant`,
  `Invariants`, `FixedAll`, `actionCategory`, `actionPreadditive`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `DerivedCategory.singleFunctor` through the public dependency.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: the recorded public
  derived-restriction interface, including `boundedBelowComputation`; its public
  dependencies provide `CategoryTheory.CondensedBar.Ring`, `Equivariant`, and
  `CategoryTheory.CondensedDerivedRestriction.invariants`, `derived`, `actionAbelian`,
  `actionGrothendieck` and ordinary derived-functor structure. I read the full signatures
  and documentation of the recorded `coefficientSquare` and these relevant declarations.
- Proof-only import `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its universal
  unit and computation-isomorphism interface (the node def-sfb-right-derived-functor).
- The proof dependency `lem-sfb-condensed-action-injective-infrastructure` has no Lean
  record or Mathlib match at delivery time. No import can be added for it. It is a
  proof prerequisite only, and the current public restriction-calculus interface already
  supplies the structures needed for this statement. Its future proof-module import is
  for the maintainer to add when that proof dependency is stated.
- `def-weil-size-convention` is explicitly a metatheoretic convention, with no module
  or declaration, and is rendered by the explicit universes above.

Source: I read the complete main-20261015 direct-images proof paragraph (3), and the
item's agent-extracted statement and five-step proof. The blueprint paragraph is an
ancestor source, not a claim that it literally states this auxiliary theorem. The
module docstrings preserve that provenance and all five proof steps: central
naturality, equivariant injective resolution, identity on invariant complexes,
computation-unit cancellation, and the invertible-zero argument. The construction
helper is step 1 of the SAME node, so it needs no independent notion or new DAG node.

Edge cases checked mathematically before writing:

- z = 1, including the trivial group: z_N is identity, so the first clause holds.
  The difference is zero, and being invertible then forces N itself to be zero.
- Zero N or the zero condensed ring: the identity of a zero object is zero and is
  invertible; both conclusions remain meaningful and true.
- Empty test set S: its unique continuous map to J is the required constant map;
  section identities and uniqueness still apply. No nonempty-test-set hypothesis occurs.
- Noncentral z is excluded exactly by hz: otherwise constant action need not be an
  equivariant endomorphism. No commutativity of the entire group is imposed.
- Arbitrary non-Hausdorff, noncompact topological groups are admitted; a constant
  map is always continuous. Arbitrary internal modules are admitted, not just
  finite-dimensional realizations, and no scalar-extension or flatness input is used.
- The identity conclusion is an equality of derived morphisms; hence additivity
  and preservation of inverses really do imply the second clause for the whole object.

Searches for an existing statement (all run using the prescribed msearch.py wrapper):

- LeanFinder: “A central group element acts as the identity on derived invariants of
  internal condensed modules, and invertible difference from identity implies vanishing”.
  Eight hits: low-degree group-cohomology formulas, continuous invariants on topological
  modules, finite cyclic group cohomology, and the ordinary representation intertwining
  statement. None is the internal condensed-module derived identity and vanishing.
- Loogle: `Representation.IntertwiningMap.centralMul`. One hit, the ordinary
  representation central-action map. Read its source and full signature at
  Mathlib/RepresentationTheory/Intertwining.lean:583-594: fixed ordinary coefficient
  semiring/module, not internal condensed coefficients or their derived invariants.
- Mathlib grep:
  `(central|center).*(cohomolog|invariant)|(cohomolog|invariant).*(central|center)`.
  Six irrelevant hits in Gaussian probability, Lie loops and Brauer group documentation.
- LeanSearch: “A central element acts trivially on derived invariants of a group action
  on sheaves of modules”. Eight hits: centre action, ordinary representation invariant
  adjunctions, ordinary invariant submodules; no matching derived internal statement.
- Project rg in the prescribed `lean/WeilConjectures` and `lean/Sheaf` trees for
  central/centre with derived/invariants, and exact blueprint ID: no existing statement.
  The dense-lattice comparison proof docstring at DenseLatticeDerivedInvariants.lean:856
  mentions the argument but does not declare it. The recorded upstream-name index
  and both source trees contain none of the four proposed declaration names.

Validation: scompile.py compiled this file in sandbox and library module modes, cleanly
(3.9 s and 2.8 s); the explicit direct statement-dependency imports were then added for
DAG correspondence and the complete final file is rechecked by deliver2.py below.
No STATEMENT-DISPUTED issue, new node, dependency repair, or statement correction.

## Second reading by O2

The dispatcher brief forbids spawning other agents and assigns the maintainer's
independent delivery review. This section records the worker's additional self-audit,
not an independent second agent's approval. With the node and final module open, I
checked the ring bundling, every topological-group binder, the absence of compactness
and discreteness, every-section constant-action specification and uniqueness, the
actual derived functor and degree-zero single functor, both conjuncts, and the scope
of the isomorphism premise. No statement mismatch was found. The only adjustment
was adding explicit public imports of recorded statement dependencies; it changes
no declaration or conclusion. Independent mathematical review remains the maintainer's.
