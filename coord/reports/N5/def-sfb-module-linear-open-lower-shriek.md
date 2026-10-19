## Worker report

Recorded an existing declaration; no Lean module or definition is added. The published
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` defines
`AlgebraicGeometry.ProEtale.CondensedRing.linearOpenImmersionLowerShriek` and all the
companion declarations needed by the node. The module was read in full using
`scompile.py --source`, since it is missing in the older slopmaster2 checkout. The shared
`lean/WeilConjectures` copy was also inspected; the published source has newer proofs but
agrees on the construction and signatures. The existing source is used as published.

Source checked: current blueprint snapshot `main-20261015`,
`sec-six-functors-basics/sk-def-sfb-module-lower-shriek/def-sfb-module-linear-open-lower-shriek.md`.
The node has no `blueprint_update` or maintenance repair note. No statement correction,
new node, dependency repair, or disputed statement is required.

Hypothesis and clause correspondence:

- A commutative condensed ring is encoded by
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]` and
  `[IsCommMonObj Λ]`. This is a ring object in condensed abelian groups with the tensor
  product over the integers, not a constant ordinary ring.
- The schemes and open immersion are the section variables `{U X : Scheme.{u}}`,
  `(j : U ⟶ X)`, and `[IsOpenImmersion j]`. There is no quasi-compactness, properness,
  separation, nonemptiness, characteristic, or finiteness restriction.
- `Λ_X = p_X^* Λ` is the existing `AlgebraicGeometry.ProEtale.condensedRingObj Λ X`,
  definitionally `(upperStarFromPoint X).obj Λ`, with its transported `MonObj` instance.
  The bundled version is `coefficientRing X (Mon.mk Λ)`; it is not a new coefficient object.
- The displayed domain is literally
  `Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    ((j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))`.
  The codomain is
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
  Both are the dependency's actual module-object categories, with `ModObj` recording
  unitality and associativity and `Mod.Hom` recording linearity.
- The definition's body is
  `(ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft
    (condensedRingObj Λ X)`.
  Thus this is the linearization of abelian extension by zero along its actual adjunction.
- Unfolding `Adjunction.mapModLeft`, `Adjunction.projectionFormula`, and
  `Functor.ProjectionFormula.smul` gives exactly
  `(asIso (adj.projectionFormulaMap B M.X)).inv ≫ P.map γ[S.obj B,M.X]`,
  with `B = condensedRingObj Λ X`, `S = ProEtale.upperStar Ab j`, and
  `P = ProEtale.openImmersionLowerShriek Ab j`.
  The canonical map is defined as the inverse adjunction hom-equivalence applied to
  `S.obj B ◁ adj.unit.app M.X ≫ Functor.LaxMonoidal.μ S B (P.obj M.X)`.
  Its inverse followed by `P.map` of the action is exactly the displayed node formula,
  with the same direction and order of the tensor factors. This is not an arbitrary
  choice of an isomorphism. Its invertibility is supplied by the published
  `CondensedRing.hasProjectionFormula_openImmersion` instance, implementing the same
  canonical projection formula as the recorded dependency.
- `Functor.ProjectionFormula.mapModLeft` sends the underlying object to `P.obj M.X` and
  the underlying morphism to `P.map f.hom`. The companion
  `linearOpenImmersionLowerShriek_comp_forget` states the functor equality
  `linearOpenImmersionLowerShriek Λ j ⋙ Mod.forget (condensedRingObj Λ X) =
    Mod.forget _ ⋙ (j)_!open[Ab.{u + 1}]`.
  Consequently the underlying sheaf functor is extension by zero on objects and morphisms.
- Exactness is recorded by the existing instances
  `linearOpenImmersionLowerShriek_additive`,
  `preservesFiniteLimits_linearOpenImmersionLowerShriek`, and
  `preservesFiniteColimits_linearOpenImmersionLowerShriek`. These are the additive,
  left-exact and right-exact clauses for the module categories.
- `linearOpenImmersionLowerShriekAdjunction` has type
  `linearOpenImmersionLowerShriek Λ j ⊣
    (j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)`.
  This is precisely the stated transport right adjoint. In particular the definition
  neither changes scalars to `Λ_U` nor uses the distinct nonlinear
  `CondensedRing.openImmersionLowerShriek`.

All six companion declarations are listed in `lean.declarations` so the delivery tool's
existing-declaration compiler probe checks each of them, not only the functor name.
The `lean.statement` is the definition's literal signature, with its section hypotheses
explained above and in `lean.note`. No proof is written in this delivery. Binding an
existing construction does not assert closure of its entire upstream proof dependency graph.

Dependency declarations read and used:

- `sk-def-sfb-pulled-back-coefficients` records
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, `condensedRingObj`,
  and `isCommMonObj_condensedRingObj`. These implement the exact coefficient ring used here.
- `sk-def-sfb-module-objects` has no lean record, but its closed slopmaster2 audit names
  the Mathlib declarations `CategoryTheory.ModObj`, `Mod`, `Mod.forget`, and `Mod.regular`
  in `Mathlib.CategoryTheory.Monoidal.Mod`. Their signatures and docstrings were read;
  no dependency module or new node is necessary.
- `sk-def-sfb-transport` likewise has a closed slopmaster2 audit. Its declarations are
  `CategoryTheory.Functor.mapMod` in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Adjunction.mapModAdjunction` in
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`, and
  `Functor.ProjectionFormula`, `Functor.ProjectionFormula.mapModLeft`,
  `Functor.ProjectionFormula.mapModRight`, `Functor.ProjectionFormula.mapModAdjunction`,
  `Adjunction.HasProjectionFormula`, `Adjunction.projectionFormula`, and
  `Adjunction.mapModLeftAdjunction` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`.
  These supply exactly the generic transport and canonical linearization, with full
  coherence data and actual action formulas. Their definitions and docstrings were read.
- `lem-sfb-open-projection-formula` records
  `AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekProjectionMap_app_app` in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection`.
  Its general coefficient theorem applies to `Ab.{u+1}`. Its right-handed tensor order
  is carried to the left-handed canonical formula by the tensor symmetry, as already
  explained in the dependency's record. The chosen linearization uses the left-handed
  canonical `Adjunction.projectionFormulaMap` directly.
- `sk-def-sfb-finite-lower-shriek` records the public import closure of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper`.
  The relevant declarations `ProEtale.openImmersionLowerShriek`,
  `openImmersionLowerShriekUpperStarAdjunction`,
  `openImmersionLowerShriek_additive`, and `preservesFiniteLimits_openImmersionLowerShriek`
  were read from the current published `FiniteCoefficient.LowerShriek.Open.Defs` source.
  These give the actual sheafified localization Kan extension and its adjunction.
- `def-sfb-finite-upper-star` records `AlgebraicGeometry.ProEtale.upperStar` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`. The published old path is a
  compatibility re-export of `FiniteCoefficient.UpperLowerStar.Defs`; the latter was read
  with `scompile.py --source`. It defines pullback by sheafified left Kan extension.
- `sk-def-sfb-sheaf-tensor` records `CategoryTheory.sfbSheafTensor_properties` and companion
  declarations in `Sheaf.CategoryTheory.SheafTensor`. This and `SheafTensorStructure`
  were read: the tensor is `Sheaf.monoidalCategory J A`. The upstream instance in
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` uses precisely the
  same Mathlib localized tensor. `WeilConjectures.CategoryTheory.RingObjects.Ab` supplies
  its coefficient tensor via the abelian-group tensor product over the integers, with
  integer unit. Thus no alternative sheaf monoidal structure is substituted.

Edge cases checked before binding: the section allows the empty scheme and an empty
open immersion, the identity immersion, the zero coefficient ring, and zero modules.
The generic projection-formula lift and the sheafified Kan-extension construction impose
no exclusion in any of these cases. For the empty open the underlying extension is zero;
for the identity it is the canonical identity extension with the transported action.
All schemes range over an arbitrary universe `u`, the site retains its object and
morphism sizes, and the coefficients are `Ab.{u+1}` as in the existing framework; no
extra equality of site universes is introduced.

Searches made (2026-10-18):

- `msearch.py ... leanfinder "Extension by zero for module objects over a condensed ring
  along an open immersion using the projection formula"`: eight hits, including
  `Condensed.free`, `LightCondensed.free`, and locally constant condensed module functors;
  none defines this geometric extension by zero.
- `msearch.py ... leansearch "linear extension by zero functor module objects projection
  formula"`: eight hits, including `DFinsupp.lmk`, `Function.ExtendByZero.linearMap`, and
  square-zero extension maps; none is the node's construction.
- `msearch.py ... loogle '"mapModLeft"'`: zero Mathlib hits.
- `msearch.py ... grep 'linearOpenImmersionLowerShriek|mapModLeft|HasProjectionFormula'
  CategoryTheory`: zero Mathlib hits.
- `rg` in the older `WeilConjectures` source for
  `linearOpenImmersionLowerShriek|mapModLeft|hasProjectionFormula_openImmersion`, and the
  required item-id search: no hits in that older checkout.
- `rg` over the shared `lean/Sheaf` and published framework `lean/WeilConjectures` found
  the exact existing ModuleObject/LowerShriek/Defs declaration and the generic
  ModuleObjects/ProjectionFormula implementation, together with existing consumers.
  `ProEtaleOpenClosedSequenceRingSheaf` treats arbitrary ring-sheaf coefficients; it is
  not a competing definition of this specific condensed coefficient functor.
- The upstream declaration-name index was checked for the main name. The authoritative
  current source was then retrieved using `scompile.py --source` and read in full.

Validation: `deliver2.py --no-push` compiles existing-declaration probes through the
required `scompile.py` wrapper and runs the current server preflight. No new module is
needed or compiled as a delivery artifact.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
