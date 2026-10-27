## Worker report

Existing statement binding, with no new Lean module:
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_poincareMap` in
`WeilConjectures.PoincareDuality.Poincare`, lines 141–151 of the current source.
The exact source signature is
`theorem isIso_poincareMap : IsIso (poincareMap ℓ p d)`.
I read the live source using `scompile.py --source
WeilConjectures.PoincareDuality.Poincare`; it agrees with the read clone.
The prescribed existing-declaration path avoids restating the theorem.
Only the item's `lean` field changes. Its accepted stage-1 split and proof are preserved.
The repair note is resolved stage 1, not a released stage-2 interface repair.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Prime coefficient: `(ℓ : ℕ) [Fact ℓ.Prime]`. Positive characteristic and its distinction
  from ℓ are `{k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]`. A field's positive characteristic is prime, so this is the
  stated characteristic setting, not a finite-field restriction.
- Schemes over the same field: `{X S : Over (Spec (.of k))}` and `(p : X ⟶ S)`.
  The six section instances are `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated`
  on each structure map `X.hom`, `S.hom`. The first two together express finite type.
  `p.left` is the underlying scheme morphism, and its compatibility with k is part of
  the Over morphism.
- Dimension: `(d : ℕ)`. The surrounding geometric setting includes
  `[SmoothOfRelativeDimension d p.left]`. The source deliberately writes
  `omit [SmoothOfRelativeDimension d p.left] in` before `isIso_poincareMap`.
  This is precisely the omission explicitly described in the item's final sentence.
  Its meaning is that the categorical invertibility argument uses the already chosen
  purity isomorphism, not a fresh geometric construction. We do not claim that the
  elaborated theorem has a smoothness binder or add a second theorem with one.
- Coefficient ring: every functor and object in `poincareMap` uses
  `Profinite.padicAlgClRingObj ℓ`. `EllAdic.lean` defines it from
  `padicAlgClCondensedRing`: continuous sections with values in one finite intermediate
  extension, with pointwise operations. It is not the entire continuous-function ring
  of the valuation-topological algebraic closure.
- Category and constructibility: `Dᵇc(T.left)⟦Profinite.padicAlgClRingObj ℓ⟧` expands to
  `ProEtale.BoundedConstructible (condensedRingObj ... T.left)`, the full subcategory
  defined by `boundedConstructible`. The predicate is canonical t-structure
  boundedness intersected with `∀ n : ℤ, IsConstructibleModuleObject ... (Hⁿ K)`.
  `IsConstructibleModuleObject` uses a finite `Scheme.Stratification` and
  `IsLocallyFinitelyPresented` on each pulled-back module. The latter is a pro-etale
  cover with finite presentations. No derived completeness is inserted. There are
  finitely many possibly nonzero cohomology degrees; their finite stratifications can
  be commonly refined, giving the node's simultaneous-stratification description.
- Tensor, unit and Hom: `isMonoidal_boundedConstructible` and
  `isMonoidalClosed_boundedConstructible` give the full-subcategory monoidal closed
  structure. `𝟙_` is its unit and `(ihom K).obj L` its internal Hom. The actual
  restricted tensor–Hom adjunction is `boundedConstructibleTensorHomAdjunction`.
- Pullback and pushforward: `boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p`
  is the restriction of the ambient derived adjunction along the fully faithful
  inclusions. The module pullback it derives is the recorded `upperStar`, transport
  of module objects followed by scalar extension along `condensedPullbackHom`.
- Exceptional operations: `boundedConstructibleLowerShriek _ ℓ p` is open extension
  followed by proper derived pushforward at `compactificationOverField p`.
  `boundedConstructibleUpperShriek _ ℓ p` is the composite proper right adjoint and
  open pullback, with composite adjunction `boundedConstructibleUpperShriekAdjunction`.
- Tate object: `boundedConstructibleTateTwist ℓ X d (2 * d)` has ambient object
  `(shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)`.
  The latter is the recorded integral roots-of-unity inverse-limit/scalar-extension
  construction in degree zero, with nonnegative tensor powers. It is exactly the
  node's twist, not an arbitrarily selected object of the right isomorphism class.
- Chosen purity: `boundedConstructibleSmoothPurityIso ℓ p d` is
  `(asIso (smoothPurityMap ℓ p d)).symm`. `smoothPurityIso` is its image under the full
  inclusion; hence it is exactly the preimage of the chosen ambient purity isomorphism.
  The recorded `nonempty_smoothPurityIso` supplies the geometric existence statement,
  not an alternative normalization or an arbitrary replacement choice in this target.
- Exceptional projection: `boundedConstructibleExceptionalProjection _ ℓ p` is the
  curried natural transformation with the actual compactification projection
  morphisms as components. These are inherited from `ProjectionFormula.lean`.
- Verdier exchange: `Verdier.exchange adj adj' pf K L` is `curry` of
  `exchangePairing`. Its pairing applies PF, then the image of the pullback/pushforward
  counit tensored with K, evaluation, and the exceptional counit. The specialized
  `verdierExchange` in `Verdier.lean` uses exactly these adjunctions and PF.
- Poincare map: the specialized `poincareMap ℓ p d` calls
  `Verdier.poincareMap` on these exact adjunctions, PF and purity. The abstract definition
  is `G.map (pur.inv ≫ toIhomUnit _) ≫ exchange ... (𝟙_ C) (𝟙_ D)`;
  `toIhomUnit A = curry (λ_ A).hom`. Functoriality splits its first mapped composite
  into precisely the first two factors described by the node. Its source is
  `Rp_* Qlb_X(d)[2d]` and its target `RHom(Rp_! Qlb_X, Qlb_S)`.
- Trace: specialized `trace ℓ p d` calls `Verdier.trace`, whose definition is
  `P.map pur.inv ≫ adj'.counit.app (𝟙_ D)`.
- Compact-support cup product: specialized `cupProduct ℓ p d` calls
  `Verdier.cupProduct`, namely the PF component, then the image of the unit tensored
  with the pullback/pushforward counit, then the image of the left unitor.
- Conclusion: `IsIso (poincareMap ℓ p d)` asserts invertibility of this specified arrow
  in the full bounded-constructible category on S, not merely existence of some
  isomorphism between its endpoints. Trace and cup product are the definitions named
  in the statement; no extra trace–cup identity is added to its conclusion.

Dependency declarations read (all names below have their recorded namespaces):

- `nt-target-smooth-purity-qbar`: `Sheaf.Targets.SmoothPurityQbar`,
  `AlgebraicGeometry.ProEtale.CondensedRing.nonempty_smoothPurityIso`.
- `def-pur-condensed-tate-twists`: `WeilConjectures.TateTwist.ProEtale`,
  `AlgebraicGeometry.ProEtale.tateModuleLevel`, `tateModuleTransition`, `tateModuleSystem`,
  `tateModule`, `tateTwistOne`, `tateTwistNat`, `tateTwist`, `tateTwistDerived`.
- `sk-def-sfb-dc-setting` and `sk-def-sfb-dc-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`,
  `boundedConstructibleLowerShriekOfCompactification`, `boundedConstructibleLowerShriek`,
  and their recorded inclusion comparisons.
- `sk-def-sfb-qlbar-condensed`:
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, and ring-presheaf construction.
- `sk-def-sfb-bounded-constructible`:
  `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale` publicly exposes the
  general ring-object definition as well as the discrete-coefficient presentation;
  the actual target uses the general `AlgebraicGeometry.ProEtale.boundedConstructible`,
  not the discrete constant-ring specialization.
- `sk-def-sfb-dc-upper-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactification`,
  `boundedConstructibleUpperShriek`, and both exceptional adjunctions.
- `def-sfb-module-upper-star`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar`.
- `nt-target-poincare-tate-bc`: current `WeilConjectures.SmoothPurity.Defs` provides
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived` and
  `boundedConstructibleTateTwist` for this field setting, publicly exposed by the target
  module. The node's record points to the target module and an earlier more general
  signature; this consumer only needs its separated finite-type field specialization,
  which the current source supplies. No dependency edit is needed to bind an existing
  theorem whose map already uses that exact wrapper.
- `sk-def-sfb-dc-restricted-functors`:
  `Sheaf.Paper.BoundedConstructiblePushforwardRestriction` publicly imports the preceding
  upstream restricted operations, including `boundedConstructibleUpperStar`,
  `boundedConstructibleLowerStar`, their adjunction and monoidal closed structures.
  Its additional `boundedConstructibleLowerStarOfPreserves` handles general coefficients;
  the specified Qlb target uses the existing ell-adic specialization.
- `def-sfb-dc-hom`: `Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves`,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleHomOfPreserves` and its
  inclusion comparison. This is the general conditional interface; its module exposes
  the existing ell-adic `boundedConstructibleHom` used here.
- `def-sfb-dc-tensor-hom-adjunction`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves`,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleTensorHomAdjunctionOfPreserves`.
  This restricts the ambient adjunction under explicit preservation; the module publicly
  exposes the existing chosen ell-adic tensor–Hom adjunction used by the target.
- `def-sfb-bounded-constructible-complexes`:
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`,
  `AlgebraicGeometry.ProEtale.boundedConstructible`, `BoundedConstructible`.
- `def-sfb-constructible-module`: `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`,
  `AlgebraicGeometry.ProEtale.IsConstructibleModuleObject`, with the finite-stratum
  locally-finitely-presented condition just described.

The existing upstream proof applies its categorical `poincareMap_isIso_aux`, using
`Verdier.isIso_exchange_of_isIso` and the PF isomorphism instance. The accepted DAG proof
spells out that same argument in four assembly steps: (1) the compactification PF inverse
and naturality from `lem-pd-compactification-projection-inverse`; (2) the Hom-chain
realization from `lem-pd-condensed-hom-chain-realization` and its explicit Yoneda inverse;
(3) the exact Tate object and chosen purity; (4) the unit–Hom isomorphism and composition
of the three invertible factors. Existing binding introduces no new theorem proof or
imports. In particular it does not replace the specified map by a common-stage
coefficient-category comparison.

Edge cases checked by reading the signatures and definitions: `d = 0` is admitted, with
zero twist and shift and the unit–Hom identification; empty schemes and zero objects
are not excluded by a nonemptiness, irreducibility or dimension assumption; ℓ equal to
characteristic and characteristic zero are excluded exactly by the node's field setting;
nonproper smooth morphisms are admitted because exceptional functors use compactifications;
k need not be finite or algebraically closed. The single universe `u` is the existing
scheme/coefficient convention, with abelian sheaves in `u+1`; no universe equality is added.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `Poincare duality morphism is an isomorphism from smooth purity and Verdier exchange`:
   8 generic derived-category/complex hits; no target-specific Mathlib match.
2. `msearch.py ... loogle` with query
   `CategoryTheory.IsIso, AlgebraicGeometry.ProEtale.CondensedRing.poincareMap`:
   0 hits; Loogle reports the project-specific name unknown. This is not evidence of
   absence from the project.
3. `msearch.py ... grep 'poincareMap|isIso_verdierExchange'`: 0 Mathlib hits.
4. `rg` for `poincareMap|isIso_poincareMap|nt-target-poincare-isiso` in both project Lean
   roots finds the exact theorem in `WeilConjectures/PoincareDuality/Poincare.lean` and
   its abstract map in `Abstract.lean`; no alternative Sheaf declaration is needed.
   The source's module, definition and theorem docstrings and full signatures were read.
5. `grep -rn 'nt-target-poincare-isiso' lean/WeilConjectures`: no blueprint-tag hit.
   The upstream names index did not supply this target, so the actual source is decisive.
6. `scompile.py --source WeilConjectures.PoincareDuality.Poincare`: live server confirms
   the exact theorem and all three specialized map definitions. The current blueprint's
   Verdier-exchange unit and tensor–Hom proof were also read under `literature/blueprint/latest`.

No statement correction or new nodes. Existing-source caveat: `SmoothPurity.Defs` documents
its postponed trace construction and purity inputs. This binding records the requested
statement, not completion of its transitive proof dependencies or a new construction of
that trace. The omission of smoothness is disclosed above and already disclosed by the node.

Validation: `deliver2.py NB nt-target-poincare-isiso --no-push` returned OK: the
existing declaration passed a real server `#check`, the check module compiled within the
normal 60-second limit, and server preflight accepted the node and report. No new Lean
module requires compilation.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
