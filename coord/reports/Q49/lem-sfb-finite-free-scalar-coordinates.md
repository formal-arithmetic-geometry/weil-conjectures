## Worker report

The module `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates` states
`CategoryTheory.Mod.sheaf_finiteFreeScalarCoordinates` with the whole proof `sorry`.
Its helper `CategoryTheory.Mod.FiniteFreeScalarCoordinates` is a fully written
Prop-valued packaging of this same assertion, not another tensor, module category,
or scalar-extension construction. Both declarations belong to the assigned node.
No new node, dependency repair, or statement correction is needed. The source is
the final sentence of blueprint main-20261015,
`sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`:
the finite-free coefficient tensor is naturally a finite power. I read the item's
six-step expansion and all three statement-dependency records and declarations.
There is no repair-note file for this item.

Hypothesis and clause correspondence:

- The essentially small site is `{C : Type uC} [Category.{vC} C]
  [EssentiallySmall.{w} C] (J : GrothendieckTopology C)`. The independent universes
  `uC`, `vC`, and `w` are not equated. Abelian coefficients are `Ab.{w}` with the
  tensor-over-integers structure of the upstream `RingObjects.Ab` module.
- The canonical sheaf tensor is explicitly
  `(sfbSheafTensorStructure (A := Ab.{w}) J).monoidal`, with its recorded symmetric
  structure's braiding. It is not a cartesian or arbitrarily chosen tensor.
  The explicit `sheafIsAbelian` argument uses the canonical small-model
  `hasSheafifyEssentiallySmallSite`; this works even at coefficient universe zero.
- The predicate asserts `Nonempty (MonoidalPreadditive H)`, `HasCoequalizers H`,
  and preservation of small colimits by left and right tensor. These are
  consequences of the closed symmetric sheaf tensor, not hypotheses on the site
  or the rings. It then universally quantifies over their proof instances to
  elaborate the scalar-extension expressions. Since the required instances are
  asserted to exist and are proof irrelevant, this does not omit any case.
- Commutative ring objects are `(R B : H) [MonObj R] [MonObj B]
  [IsCommMonObj R] [IsCommMonObj B]`; the ring morphism is
  `(φ : R ⟶ B) [IsMonHom φ]`. No nontriviality or field assumption occurs.
- Module objects use the recorded `CategoryTheory.Mod` throughout. The chosen
  finite-free identification is `(n : ℕ)
  (θ : finiteFree R n ≅ (comap φ).obj (regular B))`. The existing `finiteFree`
  is exactly the finite biproduct of `regular R`, so the statement uses the
  specified R-module isomorphism, not merely a rank or nonempty witness.
- The coordinates `q_i` are the underlying maps of
  `θ.inv ≫ biproduct.π (fun _ : Fin n ↦ regular R) i`.
  The basis maps `e_i` are
  `biproduct.ι (fun _ : Fin n ↦ regular R) i ≫ θ.hom`.
  Thus the unit-to-B map representing `b_i = e_i(1)` is exactly
  `η[R] ≫ (biproduct.ι ... i ≫ θ.hom).hom`.
- The conclusion `∃ Φ : extendScalars φ ⋙ comap φ ≅
  Functor.const (Discrete (Fin n)) ⋙ lim, ...` is an isomorphism of
  R-module-valued functors. The codomain is the categorical finite-power
  functor; its maps are induced componentwise and its projections are `Pi.π`.
  Limits of module objects are created on the underlying objects, so these are
  the componentwise module-sheaf finite powers in the node.
- The forward formula is the equality, for every `M` and `i`, of
  `extendπ φ M ≫ (Φ.hom.app M).hom ≫ (Pi.π ... i).hom` with
  `(θ.inv ≫ biproduct.π ... i).hom ▷ M.X ≫ γ[R,M.X]`.
  Its right side sends a local elementary tensor `(s,m)` to `q_i(s)m`.
  The left side is precomposed with the canonical relative-tensor quotient.
- The inverse formula identifies `(Φ.inv.app M).hom` with the sum over
  `i : Fin n` of `Pi.π_i`, the inverse left unitor, the right tensor of
  `η_R ≫ e_i`, and `extendπ φ M`. Applied to a tuple this is precisely
  `∑ b_i ⊗ m_i`. The finite sum is taken in the underlying preadditive sheaf
  category; the component of Φ is already an R-module morphism.
- The formulas are equalities of sheaf morphisms involving the coequalizer
  projection and the actual tensor. They specify the formulas on elementary
  local tensors via the tensor and coequalizer universal properties. They do
  not assert any equality between tensor-sheaf sections and sectionwise tensors.
  Naturality and both inverse identities are part of the `≅` of functors.

Dependency declarations used:

- `sk-def-sfb-sheaf-tensor`: `Sheaf.CategoryTheory.SheafTensor`,
  `CategoryTheory.sfbSheafTensor_properties`, its canonical structure
  `CategoryTheory.sfbSheafTensorStructure`, and the public
  `sfbSheafTensor_hasWeakSheafify` instance. I read the structure construction,
  comparison, full theorem signature and docstrings. The theorem supplies
  closedness and left/right colimit preservation; the monoidal tensor is the
  sheafified objectwise tensor over the integers.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `Mod.Hom`, `Mod.regular`, `Mod.comap`; I read their
  signatures and module/action definitions. These are reexported through the
  upstream scalar-extension module.
- `sk-def-sfb-change-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.extendScalars`, `Mod.comap`, `Mod.extendπ` and the
  coequalizer description `extendScalarsObj_X`. I read their definitions and
  the full module documentation: the quotient map used in the formulas is the
  actual coequalizer of the two balancing actions.
- The already existing `Mod.finiteFree` from
  `WeilConjectures.CategoryTheory.ModuleObjects.Free` supplies the chosen
  finite direct sum. `Mod` limits are created by the forgetful functor as in
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`. Mathlib supplies
  `Functor.const`, `lim`, `Pi.π`, `biproduct.ι`, `biproduct.π`, and the
  abelian sheaf instance and small-model sheafification transport.

Edge cases checked mathematically before writing:

- Rank zero: `finiteFree R 0` is zero, so θ forces the underlying B-module
  sheaf to be zero. The power is the terminal/zero module, the forward
  coordinate condition is empty, and the inverse is the empty sum, zero.
- Zero coefficient rings and zero modules are permitted, without a positive
  rank or nonzero hypothesis. If R is zero, its unital modules and B are zero.
- Rank one with basis element different from 1: the forward map uses θ's
  coordinate functional and the inverse uses `η_R ≫ e_0`, not B's unit. Thus
  it has the required dependence on the chosen basis.
- An empty site is allowed. All conditions concern the actual sheaf and
  module categories, and do not demand a test object or a nonempty site.
- No claim that every tensor-sheaf section is an elementary tensor, or a sum
  of elementary tensors on the same test object, is used.

Searches for an existing declaration:

- `msearch.py ... leanfinder`: “Finite free internal ring sheaf scalar extension
  is naturally a finite power of a module, with basis coordinate formulas”.
  Eight hits, including `SheafOfModules.freeFunctor_obj`, local finite-type
  generators and `ModuleCat.tilde`; none states the internal-ring-sheaf
  natural coordinate isomorphism.
- `msearch.py ... loogle`: `Mod.extendScalars, biproduct`. No hits; the search
  service does not index that project identifier.
- `msearch.py ... grep`: `finiteFree|finite_free|powerFunctor` in
  `CategoryTheory`. Two hits, both the power functor on formal coproducts in
  `Mathlib/CategoryTheory/Limits/FormalCoproducts/Cech.lean`. I read its
  declaration; it is a different category and no scalar-extension assertion.
- `msearch.py ... leansearch`: “For a finite free internal algebra B over R,
  restriction of B tensor_R M is naturally the finite power M^n, with
  coordinates from a chosen basis”. Eight hits: ordinary algebra tensor basis,
  `TensorPower`, tensor algebra bases, and `Module.Finite.base_change`.
  None concerns internal modules on an arbitrary site.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, and the upstream name
  index for the declaration names found no collision. A direct search for
  the item id in `lean/WeilConjectures` found no existing declaration.
- Concept searches for finite coordinates, powers, and tensor/finite-free
  scalar extension in both project roots found
  module `Sheaf.CategoryTheory.ConstantFiniteFreePowerIso`, declaration
  `CategoryTheory.constantFiniteFree_underlyingPowerIso`.
  I read its full signature and proof docstring: it assumes ordinary constant
  coefficient rings and only concludes an underlying abelian-presheaf
  natural isomorphism, so it does not state this arbitrary internal-ring
  R-module-valued coordinate assertion. The related
  `ConstantFiniteFreeProducts` asserts countable-product preservation.

No STATEMENT-DISPUTED issue was found. The theorem docstring gives each of
this node's six proof steps. Only the named theorem is postponed; the helper
predicate contains no sorry and defines no mathematical data by choice.

Validation: every compile uses the prescribed `scompile.py` wrapper, for this
single module only. The final file compiled cleanly both as a sandbox module (5.9 s) and under its
actual library module name (4.7 s), with no errors or warnings.
The only repository write is performed later by the authorized delivery tool;
all authored files are in the assigned sandbox.

## Second reading by Q49

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
