## Worker report

The module `Sheaf.Paper.RationalLocalizingProjectionFormula` states the two cases of
`det-thm-sf-pf-field-localizing` and five helpers for its canonical projection map,
with `sorry` proofs for the three named theorems, in
`AlgebraicGeometry.ProEtale.CondensedRing`. No mathematical statement is corrected.
The node's source and ten-step proof were read against the current main-20261015
blueprint statement and both proof paragraphs. The resolved stage-1 repair note
asks that this statement remain unchanged; this delivery leaves it unchanged.

Hypothesis and clause correspondence:

- The standing prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The field of characteristic p > 0, p different from ell, is
  `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
  Prime ring characteristic states exactly positive characteristic here.
- X and Y are `Scheme.{u}`, with `Over (Spec (.of k))`, and each structure morphism
  has `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated`. These are precisely
  separated finite-type schemes over k, as required by sk-def-sfb-dc-setting.
- The displayed map p is `(p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]`.
  The k-morphism condition comes from the standing setting, not a new restriction.
- Lambda = E is the finite-extension theorem with
  `(E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]`. Its coefficient is the recorded
  `Profinite.continuousCoefficientRingObj E`, whose sections are continuous
  functions, with pointwise operations. Any finite normed extension embeds in the
  chosen algebraic closure; the statement and map are independent of this embedding.
- Lambda = Qlbar is the separate `isIso_projectionMate_localizing_padicAlgCl`
  theorem, using `Profinite.padicAlgClRingObj ℓ`. This is the existing sheaf of
  finite-subextension-valued continuous functions, not all continuous functions
  into the topological algebraic closure. Its upstream closed audit is the binding
  of sk-def-sfb-qlbar-condensed; no replacement coefficient definition is made.
- A and B are objects of the ordinary unbounded derived category of the internal
  module-object category `Mod (Sheaf ... Ab.{u + 1}) (condensedRingObj Λ _)`.
- Membership A in Loc(Dbc(X,Lambda)) is hA:
  `CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X) A`;
  membership B is hB, with Y. This deliberately uses the recorded generic closure
  with the recorded Dbc generators. `localizingClosureProEtale` has Dctf generators,
  so using that specialization here would hide the equality that is a proof step.
- Rp*A is `(lowerStar Λ p).rightDerivedFunctor.obj A`. The first endpoint is
  this object tensor B, using the existing derived relative monoidal structure.
- p*B is represented by `(upperStar Λ p).leftDerivedFunctor.obj B`.
  The existing `leftDerivedUpperStarIsoMapDerivedCategory` identifies this canonically
  with the levelwise exact module pullback, so it is precisely the source's p*B.
- The second endpoint is `(lowerStar Λ p).rightDerivedFunctor.obj
  (A ⊗ (upperStar Λ p).leftDerivedFunctor.obj B)`.
- The canonical arrow is `moduleObjectProjectionMate Λ p A B`. It applies the
  existing `Adjunction.rightAdjointProjectionMap` to the existing derived adjunction
  and the uniquely representative-normalized derived pullback tensor comparison.
  Its transpose is comparison followed by counit tensor identity, in that order.
- The first and second conjuncts of each conclusion assert membership of both
  endpoints in `CategoryTheory.localizingClosure ... Y`. The final `IsIso` asserts
  invertibility of this actual canonical map. Together these are equivalent to
  being an isomorphism in the full target localizing category: the inclusion is
  fully faithful and reflects isomorphisms. Thus no closure clause is omitted.

Dependency declarations read and used:

- sk-def-sfb-dc-setting:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField` and its standing scheme binders. The setting is given
  by explicit binders; compactification is not an extra hypothesis of this theorem.
- sk-def-sfb-condensed-ring:
  `Sheaf.Topology.ProfiniteCondensedRing` (its current recorded module), exporting
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`,
  `Profinite.isCommMonObj_continuousCoefficientRingObj`, together with its public
  `ContinuousCoefficientUniverse` constructors. The generalized Type u interface
  avoids the old Type 0 restriction on E.
- sk-def-sfb-qlbar-condensed: published
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj` and its
  commutative-ring-object instance. Read with `scompile.py --source`.
- sk-def-localizing-closure: `Sheaf.Paper.LocalizingAdmissibleCoefficients`
  (its current recorded module), exporting `Sheaf.Paper.LocalizingClosure`,
  `CategoryTheory.localizingClosure`, `IsLocalizingSubcategory`, and the specialized
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale`, whose different generator
  predicate was checked before selecting the generic declaration.
- sk-def-sfb-constructible: `Sheaf.Paper.CondensedConstantConstructibility`,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`.
- sk-def-sfb-derived-tensor-hom: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and `.Tensor`,
  `derivedTensor`, `derivedHom`, `derivedTensorHomAdjunction`, and the existing
  `Mod.derivedMonoidalCategory`. The tensors are relative module tensors throughout.
- def-sfb-module-upper-star: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `upperStar`, `upperStar_obj`, `upperStarLowerStarAdjunction`;
  `.Derived.UpperLowerStar` gives the exact derived functors, comparison with
  levelwise pullback and `derivedUpperStarLowerStarAdjunction`.
- lem-weil-pbc-ringed-projection-mate-exact: original
  `Sheaf.Paper.ProjectionMateExact`, `SheafOfModules.ringedProjectionMateExact`,
  retained unchanged by public import. The internal-module projection-map helpers
  belong to this item, as described below.
- def-weil-proper-morphism: Mathlib
  `AlgebraicGeometry.IsProper`, in `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
  universally closed implies quasi-compact, so this is the usual properness.

The already-stated Mathlib proof dependencies are imported privately:
`Mathlib.CategoryTheory.Triangulated.Adjunction`, `.Shift.Adjunction` and
`.Triangulated.Pretriangulated`. Cartesian coefficient compatibility is exported
by the already imported upstream `ModuleObject.Basic`. The five proof-only nodes
`det-def-localizing-closure-ctf-equals-bc`,
`det-proper-base-change-unbounded-pullback`, `det-proper-image-localizing-proper`,
`det-thm-sf-pf-field-tensor`, and `det-thm-sfb-proper-base-change-rational` have
neither recorded modules nor upstream closed declarations in the inspected DAG,
so there are no modules to import for them. Their ten-step route is retained
verbatim in substance in each theorem's proof docstring.

Edge cases checked before writing: zero A or B; empty X or Y; p an identity;
unbounded A and B; shifts in arbitrary integer degrees; the finite extension
E = Q_ell; ell = 2; and Qlbar sections needing several finite subextensions.
No nonempty, positive-degree, boundedness, finite-Tor, smoothness, discrete-coefficient,
or derived-completeness assumption is introduced. The total comparison uses every
integer pair i,j; no boundedness shortcut enters the map. Universes of schemes,
coefficients and the existing sheaf/derived categories are the recorded ones.
All variables and universe parameters are explicit (`autoImplicit false`).

Searches for reuse, 2026-10-18:

- `msearch.py ... leanfinder "proper projection formula on localizing closure of
  bounded constructible condensed rational module sheaves"`: 8 hits, including
  LightCondMod.LocallyConstant.functor and Condensed.profiniteSolid; no match for
  this projection formula or the internal-module canonical comparison.
- `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointProjectionMap,
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor"`: 0 hits; the service did
  not know the project identifier. The actual upstream declaration was read in
  `WeilConjectures/CategoryTheory/Adjunction/ProjectionMap.lean` and reused.
- `msearch.py ... grep "projectionFormula|rightAdjointProjectionMap|localizingClosure"`:
  0 Mathlib hits. Generic project projection maps do exist, and are reused.
- `msearch.py ... leansearch "proper projection formula for localizing closure of
  bounded constructible condensed module objects"`: 8 hits about discrete condensed
  modules and localized modules; no exact match.
- `rg` in the allowed upstream WeilConjectures tree, side `lean/Sheaf`, and the
  upstream-name index for `moduleObjectProjectionMate`,
  `ModuleObjectDerivedTensorFormula`, `isIso_projectionMate_localizing`, and the
  item id: no exact declarations found before writing.
- Targeted source searches for monoidal mapMod/extendScalars and derived tensor
  comparison found the generic `Functor.leftDerivedTensorComparison` and its
  counit interfaces. The former requires an already specified strong monoidal
  structure on the internal-module pullback, which this coefficient API does not
  supply. The new interface uses its existing counits and specifies the ordinary
  generator and total-map normalization explicitly, rather than choosing a
  strong-monoidal structure without normalization.

No STATEMENT-DISPUTED flag and no source statement fault were found.

## Dependency modules

None. Repair of L's independent review of immutable head `07be0b725760`, H13/H2:
the rejected edit to `lem-weil-pbc-ringed-projection-mate-exact.json` is omitted
entirely from this delivery. Its current base record is unchanged:
`Sheaf.Paper.ProjectionMateExact`, `SheafOfModules.ringedProjectionMateExact`, and
all eight companion declarations. Its general exactness, shift, triangle,
naturality and unit assertions therefore retain their existing DAG record and
all landed citers retain the same binding. Merely publicly importing that theorem
did not justify replacing its record by a special-case tensor comparison.

All five internal-module declarations are now helpers in the owning item module
`Sheaf.Paper.RationalLocalizingProjectionFormula`, listed in this item's
`lean.declarations`, with source and this item's blueprint tag on each docstring:

- `ModuleObjectTensorGeneratorFormula`: the ordinary balanced-coequalizer formula,
  using `Mod.tensorObjπ`, the inverse-image oplax comparison and the actual scalar
  extension units `Mod.extendUnitHom` along `condensedPullbackHom`.
- `ModuleObjectDerivedTensorFormula`: the signed total-complex comparison on every
  integer summand, normalized through the two derived-functor counits.
- `existsUnique_moduleObjectDerivedTensorComparison`: the named uniquely
  characterizing theorem, including invertibility; its proof remains `sorry`,
  with its full representative-construction proof plan in the docstring.
- `moduleObjectDerivedTensorComparison`: choice from that named unique-existence
  theorem; the chosen object is determined uniquely.
- `moduleObjectProjectionMate`: the actual counit mate via the existing derived
  adjunction and `Adjunction.rightAdjointProjectionMap`.

The separate `ModuleObjectProjectionMate.lean` module is no longer delivered.
No new node or statement correction is needed: these helpers define the canonical
map already present in the item's own statement. All data definitions remain real
constructions, and no theorem has acquired a proof other than `sorry`.

## Second reading by Q99

Author self-check for direct dispatcher delivery; the maintainer supplies the
independent review. I reopened the node and the combined item module and checked every
hypothesis and clause against the correspondence above. In particular, the
closure is generated by `constantModelBoundedConstructible`, not upstream
constructibility with arbitrary local matrices and not Dctf as an unproved
replacement. Both endpoint-membership clauses are present. E and Qlbar are
separate theorems so the Qlbar case does not acquire a spurious finite-field
parameter. The source and target of the mate have the required tensor order,
and the coefficient comparison uses actual units, counits and coequalizer
projections. The unique-existence normalization prevents the comparison from
being an arbitrary isomorphism. No node statement or proof-plan fields changed. The item node differs from the
current shared base only in `lean`; the dependency node is not in the packet.
The two projection-formula signatures and all five helper signatures and bodies
are retained from the reviewed head; only ownership, imports, and blueprint tags
change. The helper section closes before the item theorems, so its section
variables add no hypotheses to either projection-formula theorem.

Final signature self-check: all standing geometric and characteristic assumptions are
written directly in both theorem signatures, including properness, so their inclusion
does not depend on section-variable inference for a postponed proof. The six implicit-use
lambda names in the total-colimit instances were prefixed with underscores after the
first compiler run; no linter is disabled.

The blueprint unit's older Lean pointer was also checked in full:
`AlgebraicGeometry.Etale.hasProjectionFormula_field`,
`WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/Rational.lean:139`.
Its signature concerns rationalizations of bounded constructible derived-complete
integral étale complexes with finite Tor amplitude, and their reductions. It does
not state the unbounded internal-condensed-module localizing projection formula
or construct its Qlbar localizing case, so it is not an existing match for this item.
