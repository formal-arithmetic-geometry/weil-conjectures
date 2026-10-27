## Worker report

This is an existing-declaration attachment. No Lean module is added. The primary
statement is `AlgebraicGeometry.ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`
in `WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate`, lines 261–266.
The public imported definitions and instances listed in `lean.declarations` supply
the other clauses. The node is unchanged outside `lean`.

The earlier retry described N8 as an already completed stage-2 delivery. Reading
`coord/reports/N8/lem-sf-native-adic-pullback-frobenius-mates.md` shows that it is a
stage-1 split report. The current node has no `lean` or `reviewed_lean` record.
The source theorem exists independently upstream. No returned branch is reused.

Hypothesis and clause correspondence:

- A finite field `k₀` is the source theorem's `{k : Type u} [Field k] [Finite k]`.
  Its algebraic closure is the canonical closure used by
  `Scheme.Hom.geometricFiber` and `geometricGaloisFrobenius`; these are precisely
  the geometric fibers and geometric Galois Frobenii of the recorded framework.
  The prime is `(l : ℕ) [Fact l.Prime]`, and the coefficient field is
  `PadicAlgCl l`, with the framework's `WeilCoefficients` universe lift.
  The theorem holds for every prime, hence applies when `l ≠ ringChar k₀`.
- The two base schemes are `{X₀ Y₀ : Scheme.{u}}`, their structure maps are
  `{f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)}`, and the morphism over the
  base is `(φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)`. Applying this theorem to the separated
  finite-type schemes and morphism of the node requires no additional hypothesis.
  The upstream theorem is valid even without these restrictions; no case of the
  node is excluded and no natural-language statement is changed.
- `B_T` is `ProEtale.adicConstantSheaf l T`, the sheaf of locally finite
  continuous functions, and `𝒜_T` is `ProEtale.AdicSheaf l T`. The source's
  `Module.lean` lines 54–57 define exactly the internal module category over this
  coefficient object, rather than modules over the discrete constant field.
- `L` is `adicUpperStar l (Scheme.Hom.geometricFiberMap φ h)`; `R` is
  `adicLowerStar l (Scheme.Hom.geometricFiberMap φ h)`. `Module.lean` defines them
  by `.modLeft` and `.modRight` of the ordinary inverse-image/direct-image
  adjunction and the actual `adicConstantSheafToLowerStar` coefficient map.
  `UpperStar.lean` defines that map by precomposition of locally finite functions
  with the pullback projection, and `upperStarAdicConstantSheafIso` identifies
  its adjoint with an isomorphism. Consequently scalar extension along this
  adjoint is the transported inverse-image module functor, the actual tensor
  pullback of the node. This is not a freely chosen functor or module action.
- The specified `L ⊣ R` is `adicUpperStarLowerStarAdjunction`, defined by
  `.modAdjunction` with this same coefficient map (`Module.lean`, lines 141–145).
  The units and counits used by the source mate theorem are those of this
  adjunction twice, not independent witnesses of a bare existence proposition.
- Additivity of `L` is `instAdditiveAdicSheafAdicUpperStar`. Its exactness is the
  pair `instPreservesFiniteLimitsAdicSheafAdicUpperStar` and
  `instPreservesFiniteColimitsAdicSheafAdicUpperStar`. Additivity of `R` is
  `instAdditiveAdicSheafAdicLowerStar`. All four are in `Module.lean`, lines
  163–182, and were synthesized in a module-mode server probe.
- `P_T` is `adicLowerStar l F_T.inv`, definitionally the framework's
  `WeilSheaf.frobeniusPullback`. It is additive by the same lower-star instance.
  The equivalence is `adicLowerStarEquivalence l F_T.symm` (or the inverse
  of `adicLowerStarEquivalence l F_T`), and `isEquivalence_adicLowerStar` gives
  the corresponding functor instance. `adicUpperStarIsoLowerStarInv l F_T`
  identifies `F_T^*` with `P_T`, with precisely the `leftAdjointUniq`
  normalization of `GeometricFrobenius.lean`, lines 47–76.
- The actual `e` is `adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h`.
  Its source is `L ⋙ P_X` and target `P_Y ⋙ L`: Lean writes functor application
  in the reverse order to the node's ordinary-composition notation. Its five
  factors are the specified upper-star/inverse-lower-star identifications,
  pullback compositors and equality transport, not an arbitrary isomorphism.
- The actual `b` is `adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h`.
  Its source is `R ⋙ P_Y` and target `P_X ⋙ R`, and its definition is the
  lower-star composition/congruence/inverse-composition word for the equality
  of the two scheme maps involving inverse Frobenius.
- The primary declaration says exactly that `mateEquiv adj adj` applied to
  `TwoSquare.mk _ _ _ _ e.inv` has natural transformation `b.hom`.
  Expanding Mathlib's recorded `CategoryTheory.mateEquiv` at `M` gives, in
  Lean's left-to-right morphism order,
  `adj.unit.app (P_Y.obj (R.obj M)) ≫ R.map (e.inv.app (R.obj M)) ≫
  R.map (P_X.map (adj.counit.app M)) = b.hom.app M`.
  Symmetry is exactly the displayed component equality in the node, for every
  `M`, with the same sources, targets, coefficient actions, unit and counit.

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework`: its recorded public entry module is
  `WeilConjectures.WeilSheaf.LowerShriek`. The relevant declarations are
  `AlgebraicGeometry.ProEtale.AdicSheaf`, `adicConstantSheaf`,
  `PadicAlgCl.locallyFiniteFunctions`, and
  `AlgebraicGeometry.WeilSheaf.frobeniusPullback`. `WeilSheaf.Category`
  lines 123–145 and 444–450 identify the same native Frobenius and pullback
  exchange used to lift to Weil sheaves. The derived compact-support operation
  is not needed for this underived statement.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: the recorded
  `SheafOfModules.module_pullback_pushforward_adjunction` in
  `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` was read with its
  complete ring/action and tensor/Hom normalization. For the native internal
  module encoding, `adicUpperStarLowerStarAdjunction` is the existing concrete
  ringed-topos adjunction for the same precomposition coefficient map. We
  attach that concrete theorem; we do not pick the generic existential
  witnesses as alternative functors or replace the dependency record.
- `def-weil-pbc-adjunction-mate`: the recorded Mathlib declaration is
  `CategoryTheory.mateEquiv` in `Mathlib.CategoryTheory.Adjunction.Mates`.
  Its definition and docstring specify the same unit/transformation/counit
  composite. The existing source theorem uses it directly.

Edge cases checked: the additive and finite-limit/finite-colimit instances
apply to arbitrary scheme morphisms, including the identity and empty schemes.
There is no nonemptiness assumption and the zero module is included. No smooth,
proper, surjective or lisse hypothesis occurs. The coefficient comparison is an
isomorphism for arbitrary scheme morphisms, not only weakly etale ones. Scheme
universes remain arbitrary `u`, and the native site/module universes are used
unchanged (`AdicSheaf` is in `Type (u + 2)`). Both Frobenius functors are handled
by the same equivalence for each geometric fiber. No statement dispute or
statement correction was needed.

Searches for an existing declaration:

- `msearch.py leanfinder`, query “Exact pullback of native adic module sheaves
  and its geometric Frobenius comparison are compatible as adjunction mates”:
  8 results, generic module adjunctions and pullback-composition comparisons;
  no native adic theorem in Mathlib.
- `msearch.py loogle`, query `"mateEquiv", "PreservesFiniteLimits"`: 0 results.
  Query `"mateEquiv"`: 12 results, including `CategoryTheory.mateEquiv`,
  `mateEquiv_apply`, and `iterated_mateEquiv_conjugateEquiv`.
- `msearch.py grep`, query
  `adicUpperStarGeometricFiberMapCompFrobeniusIso|adicUpperStarLowerStarAdjunction`:
  0 Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the named native
  comparisons and mate theorem found `Adic.ExchangeMate` and its use in
  `WeilSheaf.UpperStarLowerStarAdjunction`; no separate Sheaf copy is needed.
  Searching the item id in `lean/WeilConjectures` found no blueprint-tag match,
  but the declaration is an exact semantic match, not a name-only match.
- `scompile.py --source WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate`
  confirmed the current live source, including the full final mate signature.
  A speculative `Sheaf.SixFunctors.NativeAdicPullbackFrobeniusMates` source
  lookup had no module; no such module is assumed or imported.

Validation: the module-mode scratch probe importing only the public upstream
`Adic.ExchangeMate` compiled cleanly on the server (4.0 s sandbox / 6.7 s library).
It checked the mate theorem and canonical adjunction/equivalence signatures,
synthesized all four additive/exactness instances, and synthesized the additive
autoequivalence for pushforward along the inverse of an isomorphism. The delivery wrapper
also checks every name listed in the existing record. No new proof or `sorry`
is introduced. N8's stage-1 split is preserved verbatim.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
