## Worker report

Item: `lem-sfb-lattice-sectionwise-action-bridge`, group Q156, stage 2.

The module `Sheaf.CategoryTheory.LatticeSectionwiseActionBridge` states
`Profinite.DiscreteLattice.RestrictionCup.lattice_sectionwise_action_bridge`.
Its sole theorem has proof `sorry`; there are no new definitions, instances, or
other postponed facts. Only the item's `lean` field changes. No statement correction,
new node, or dependency repair is needed.

I read the full item, its eight proof steps, all ten statement-dependency nodes and
their recorded declarations, and the current blueprint in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). As the node itself records, the blueprint provides the open-direct-image
route and this auxiliary bridge is the agent expansion. The proof docstring follows
all eight steps, identifying the clopen action construction, exactness, invariants,
ordinary tensors, localization, derived normalization, coefficient tensor, and assembly.
The old CompactObject example is now a withdrawn module, so the module header follows
the current dependency modules and the explicit module-mode rules instead.

Hypothesis and conclusion correspondence:

* The arbitrary condensed coefficient is `(R : Profinite.CondensedRing.{u})` with
  `[IsCommMonObj R.X]`. This is the ring-object encoding on
  `Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}`. There is no
  topological-ring presentation, flatness, characteristic, or nonzero assumption.
* Rank is `(r : ℕ)`, including zero. `DiscreteLattice.Group r` is the recorded
  `Multiplicative (Fin r → ℤ)`; `ULift.{u} (Group r)` is the same discrete group
  in the sectionwise action category's required universe. No group or site universe
  is identified with an unrelated level.
* The conclusion `∃ E : Bridge R r` uses precisely the dependency's two action
  categories. `E.equivalence` is their equivalence; `E.additive`, `E.limits`, and
  `E.colimits` provide additivity and preservation of kernels/cokernels. The inverse
  of an equivalence between these abelian categories is exact as well.
* The first conjunct supplies an equality of the functor followed by ordinary
  forgetting and the sectionwise forgetful functor, and requires
  `E.underlying = eqToIso h`. This fixes objects AND maps over the actual identity
  internal-module functor. Together with `Bridge.constants`, it says that the
  ordinary action of every `v` is exactly the action of its constant section,
  not a conjugated presentation under an arbitrary underlying isomorphism.
* For each ordinary action `N`, the `∃! act` conjunct quantifies precisely the
  homomorphisms `C(S, ULift (Group r)) →* Module.End (R(S)) (N(S))`.
  Its three clauses are (i) restriction naturality, (ii) the prescribed constant
  actions `N.ρ v`, and (iii) the fibre formula. The last formula is written for
  every `f : T ⟶ S` on which `g` is constant with value `v`; it says that the
  restriction of `act S g x` is `T^v` of the restriction of `x`. Taking `f` to be
  each clopen fibre inclusion gives the node's displayed componentwise action.
  Conversely naturality and the constant equation force exactly this formula.
* The following finite-partition conjunct states the product identification itself.
  For each `g` it gives finitely many nonempty profinite pieces `P : Fin n → Profinite`,
  inclusions `ι`, distinct values `v`, and `Nonempty (IsColimit (Cofan.mk S ι))`.
  Thus these pieces are a finite disjoint clopen partition of `S`; constancy and
  injectivity of `v` identify each piece with its value fibre. The displayed
  `Function.Bijective` is exactly the restriction map `N(S) → ∏ i, N(P i)`.
  Combined with the preceding fibre equation it renders the asserted action
  on the product. Using a finite enumeration rather than the image subtype
  does not change the pieces or the canonical restriction map.
* The fixed-section conjunct is
  `Profinite.CondensedAction.FixedAll N S x ↔ ∀ i : Fin r, ... = x`.
  The left side retains ALL profinite base changes and continuous group sections;
  the right side uses exactly the positive basis constants `generator i`.
* `E.invariants` and `E.inclusion` give `Γ_o Φ ≅ Γ_s` and the specified inclusion
  equation. The explicit universal clause says any natural isomorphism `α` with
  that equation equals `E.invariants`; this retains the node's uniqueness clause.
* The natural isomorphism `t` compares sectionwise trivial action followed by
  `Φ` with `DerivedCup.trivial R r`. Its displayed equation says its underlying
  map is the identity already fixed by `E.underlying`, on every module. Requiring
  `E.regular.hom = t.hom.app (𝟙_ (Modules R))` uses this very identification on
  the regular trivial module; `Bridge.regularUnderlying` fixes its underlying
  regular-algebra identity. The regular multiplication and unit are the usual
  internal regular multiplication and unit, so these identity maps preserve them.
* `∃ c : E.equivalence.functor.CoreMonoidal` gives the ordinary strong tensor
  comparison and its coherence. The binary equation, after the actual
  `actionTensor.forgetCore.μIso`, is exactly the tensor of the two fixed underlying
  identity maps. The unit equation, after `forgetCore.εIso`, is the regular-module
  identity. This uses the dependency's diagonal sectionwise tensor and Mathlib's
  diagonal ordinary action tensor, not another tensor structure.
* `E.derived` is precisely `D(Φ) ⋙ RΓ_o ≅ RΓ_s ⋙ raise R`. The `raise` functor
  is induced by the identical exact internal-module functor. `Bridge.normalization`
  quantifies over EVERY cochain complex and uses `derivedUnit`, `sectionUnit`, the
  localized invariant isomorphism, `mapDerivedCategoryFactors`, and `raiseFactors`.
  In particular the localization universes remain `u+1` and `u+2`.
* `E.baseTensor` and `E.baseTensorNormalization` retain the strong tensor structure
  on `raise`, its flat-term K-flat binary representative equation and its localized
  ordinary unit. These are conclusions in the supplied datum, not extra hypotheses.
* No `Compatible` predicate or cup-product compatibility equation occurs in the
  theorem's type. This is exactly the bridge-datum assertion preceding that task.

Dependency interfaces used (read in the corresponding Lean sources):

* `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`, the arbitrary ring object abbreviation.
* `def-weil-size-convention`: its recorded convention has no declaration; explicit
  `universe u`, `ULift.{u}` and the `Bridge` localization sizes implement it.
* `def-sfb-condensed-action-module`: `Sheaf.CategoryTheory.CondensedActionModule`,
  `Profinite.CondensedAction.ActionModule`, `sectionModule`, `forgetAction`,
  `trivial`, `FixedAll`, and the normalized `Invariants` inclusion.
* `lem-sfb-condensed-derived-restriction-calculus`:
  `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`, with its public
  `CategoryTheory.CondensedDerivedRestriction.invariants`, `derived` and computation
  interfaces from `CondensedDerivedInvariants`; the recorded calculus theorems
  supply the named context, not an alternative action or cohomology definition.
* `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod` and `ModObj`; the existing module abbreviations specialize it.
* `lem-sfb-discrete-lattice-koszul-resolution`:
  `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`,
  `Profinite.DiscreteLattice.Modules`, `Group`, `Equivariant`, `generator`,
  `invariants`, `derivedInvariants`, and `derivedUnit`.
* `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and the actual cochain localization `DerivedCategory.Q`.
* `def-sfb-condensed-action-tensor`: `Sheaf.CategoryTheory.CondensedActionTensor`,
  `CategoryTheory.CondensedDerivedRestriction.actionTensor`, `actionMonoidal`,
  and `ActionTensorData.forgetCore`. The core retains the sheaf tensor comparisons.
* `def-sfb-lattice-derived-invariants-tensor`:
  `Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor`,
  `Profinite.DiscreteLattice.DerivedCup.trivial`, its ordinary Mathlib action tensor,
  and the fixed derived tensor normalization used by the bridge definition.
* `def-sfb-lattice-restriction-cup-comparison`:
  `Sheaf.CategoryTheory.LatticeRestrictionCupComparison`,
  `Profinite.DiscreteLattice.RestrictionCup.Bridge`, `ring`, `regularAlgebra`,
  `smallModulesDerived`, `SmallDerived`, `raise`, `raiseFactors`, `sectionUnit`,
  `BaseTensorNormalized`, and `smallQLax`. In particular I read all fields of
  `Bridge`, not just its name, before stating existence.

All stated proof-dependency modules are imported without `public` unless they are
also statement dependencies. The two proof nodes
`lem-sfb-discrete-condensed-action-equivalence` and
`lem-sfb-condensed-action-injective-infrastructure` currently have neither Lean
records nor a closed upstream audit, so there is no module to import for them.
Their mathematical statements remain the named proof inputs in the docstring;
the statement itself does not need their unstated interfaces. The coherent-sheaf
criterion and exact-derived-factorization Mathlib matches are imported by their
recorded modules. No proof import is omitted to avoid a cycle.

Edge checks before/after writing:

* `r = 0`: the basis-fixed condition is vacuous and the group is trivial, so every
  section is fully fixed; the statement retains the trivial equivalence and units.
* Empty profinite `S`: its value partition is empty (`n = 0`); the displayed product
  has its unique empty tuple and the sheaf value on the empty object is the zero module.
  Nonempty pieces do not exclude this case because there are no pieces.
* A constant section on nonempty `S` has one piece; the fibre formula reduces to the
  prescribed constant action. A two-value locally constant section gives the two
  respective ordinary actions after the two restrictions.
* The zero ring and zero module cause no excluded case: no nonzero or faithfulness
  hypothesis occurs. The action and identity equations specialize to the unique maps.
* Negative lattice exponents are retained through `Group r` and the monoid homomorphism;
  invariance under a generator implies invariance under its inverse.
* Cochain complexes are unbounded, not merely bounded below or concentrated in zero.
  The `Bridge` equation keeps the whole all-complex normalization.

Searches actually run:

* `msearch.py ... leanfinder` query: "The sectionwise action of a discrete lattice on
  condensed modules is equivalent to an ordinary action, compatible with invariants
  and derived functors". Eight results, including
  `CondensedMod.LocallyConstant.functorIsoDiscreteAux₂`,
  `CondensedMod.LocallyConstant.functor`, the locally constant/discrete module isomorphisms,
  and the LightCondMod versions. None states the action or normalized derived bridge.
* `msearch.py ... loogle` query `Action, Functor.CoreMonoidal`: service reported zero
  hits and unknown identifier `Functor.CoreMonoidal`. This is an unavailable query,
  not evidence of mathematical absence.
* `msearch.py ... grep 'Action|LocallyConstant' Condensed`: 21 lines from the condensed
  discrete-module, locally constant and related files; no exact bridge statement.
* `rg -n 'lattice.*[Bb]ridge|sectionwise.*[Aa]ction|discrete.*[Ee]quivalence|constantAction'`
  on the two project roots found action infrastructure and `RelativeLatticeBridge`,
  whose rank-one comparison has different data and is not this statement.
* `grep -rn 'lem-sfb-lattice-sectionwise-action-bridge' lean/WeilConjectures` returned
  no hits, as did the equivalent `rg` identifier search in that root.
* `rg -n 'lattice_sectionwise_action_bridge|LatticeSectionwiseActionBridge'` on Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` returned no declaration collision.
  The existing `LatticeRestrictionCupComparison.Bridge` is a specification, not an
  existence theorem, and is reused directly.

Validation: the prescribed `scompile.py Q156 lem-sfb-lattice-sectionwise-action-bridge`
compiled the module on the live server. The final compile and required delivery dry run
are recorded below after completion. No global build or direct source-clone mutation.

## Second reading by Q156

Second pass over the node and the finished statement by the assigned worker; no claim
of a separate agent's review is made (the dispatcher explicitly forbids starting agents).
The maintainer's independent review follows delivery.

The first draft stated the fibre action formula and uniqueness but left the finite
product identification implicit in the sheaf condition. On this second pass I added
an explicit finite value-partition and the bijectivity of the canonical restriction
map. Distinct values and nonempty pieces identify precisely the nonempty value fibres;
the `Fin 0` case preserves the empty profinite object. I rechecked the arrow directions
in the tensor equations against `ActionTensorData.forgetCore`: the ordinary binary
map goes from the tensor of images to the image of the sectionwise tensor, and the
inverse forgetful comparison then lands in the tensor of the original modules.
The unit equation has the corresponding direction. I also checked that `E.regular`
is the same trivial-action identification used by `t` on the regular unit, that
`E.underlying` is the identity comparison from a functor equality, and that
`Bridge.normalization` retains both computation units on every complex. No node
statement or dependency record was changed.

Final validation: `scompile.py` compiled both sandbox and actual module names cleanly
(4.2 s / 4.1 s). `deliver2.py Q156 lem-sfb-lattice-sectionwise-action-bridge --no-push`
printed `OK (dry run): commit ec19a457d09 passes the preflight and compiles; nothing pushed`.
