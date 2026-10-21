## Worker report

Delivered module: `Sheaf.Paper.PbcPairFunctorShiftCoherence`. Its one postponed theorem is
`AlgebraicGeometry.Scheme.pbcPairFunctorShiftCoherence`. The fully written helper predicate
`CategoryTheory.StageSystem.Morphism.PairFunctorShiftCoherenceSpec` packages the statement;
it introduces no category, shift, functor or comparison data. This helper belongs to the
same node and is listed in `lean.declarations`. No dependency node or statement is changed.

Hypothesis and clause matching:

- The prime is `(l : ℕ) [Fact l.Prime]`; the chosen algebraic closure is
  `(Ω : Type c) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`.
- The schemes are independent `Scheme.{u}` and `Scheme.{v}`. `[IsNoetherian T]` and
  `[IsNoetherian S]`, `hTdim`, `hSdim`, `hTl`, `hSl` give exactly the noetherian,
  finite-dimensional and invertibility hypotheses, separately for both schemes.
- The systems in the theorem are the actual `pbcScalarSystem l Ω T hTdim hTl` and
  `pbcScalarSystem l Ω S hSdim hSl`. Their stages are `pbcStageCategory`, their pair
  categories are the recorded `PbcFiniteStagePairCategory`, and `U.ι`/`V.ι` are the
  recorded inclusions. The generic predicate is applied to these concrete systems;
  it is not a theorem asserting the node for arbitrary unrelated systems.
- `A : StageSystem.Morphism U V` bundles exactly `Φ_E`, the natural isomorphisms
  `β_{F/E} : Φ_E ⋙ V.T h ≅ U.T h ⋙ Φ_F`, and the associator equation `A.coh`.
  Read in ordinary composition order, its equation is precisely the displayed
  `β_{G/E} a^S = Φ_G(a^T) β_{G/F} T^S(β_{F/E})`.
- `[∀ E, (A.Φ E).Additive]` is the assumed stage additivity. The stage instances
  `[∀ E, (A.Φ E).CommShift ℤ]` are the prescribed natural isomorphisms `s_{E,n}`
  with their zero and addition equations, using Mathlib's existing class.
- The first premise of the predicate is `∀ i K, HEq ((A.β (le_refl i)).hom.app K)
  (𝟙 ((A.Φ i).obj K))`. At the concrete systems the identity transitions are
  literally identity, so this is exactly `β_{E/E} = 1`, componentwise. Equality
  of the hom components determines equality of natural isomorphisms.
- The second premise, `∀ {i j} h, NatTrans.CommShift (A.β h).hom ℤ`, is exactly
  the displayed compatibility equation for every integer and stage object.
  Expanding `NatTrans.shift_app_comm` and
  `Functor.commShiftIso_comp_hom_app` gives, in Lean composition order,
  `V.T h.map s_E ≫ σ^S ≫ β[n] = β_(K[n]) ≫ Φ_F.map σ^T ≫ s_F`.
  This is the node's equation with its two sides reversed.
- `∀ (G : U.PairCategory ⥤ V.PairCategory) [G.Additive]` quantifies over the
  prescribed additive pair functor, without replacing it by `A.functor`.
- Its next premise is exactly `G.obj X = ⟨X.stage, (A.Φ X.stage).obj X.obj⟩`.
  The next premise quantifies over every representative `M,hX,hY,f` and identifies
  `G.map (mkHom M hX hY f)` with `mkHom M hX hY
  (β_source.hom ≫ Φ_M.map f ≫ β_target.inv)` between the explicitly given image
  pairs. This is the node's representative formula. `HEq` handles the endpoint
  equalities supplied by the object formula; it imposes no definitional-equality
  restriction and is ordinary arrow equality after that transport.
- The conclusion `∃ q : G.CommShift ℤ, ...` supplies natural isomorphisms `s_n`
  and their zero and addition coherence equations. Mathlib `Functor.CommShift`
  has exactly the three fields `commShiftIso`, `commShiftIso_zero`,
  `commShiftIso_add`. Its `isoZero_hom_app` is `G(z^A) ≫ (z^B)⁻¹`;
  its `isoAdd_hom_app` is `G(c^A) ≫ s_m ≫ s_n[m] ≫ (c^B)⁻¹`,
  exactly the two displayed equations in Lean's composition convention.
- The first conjunct fixes every component to
  `(V.ι X.stage).map (((A.Φ X.stage).commShiftIso n).hom.app X.obj)`.
  This is `[E,s_{E,n,K}]`. Since they are natural isomorphisms, specifying their
  hom components also fixes their inverse components.
- The second conjunct supplies, for each `i`, a natural isomorphism
  `κ : U.ι i ⋙ G ≅ A.Φ i ⋙ V.ι i`. Its hom components are heterogeneous-equal
  to the identity of `(i,Φ_i K)`, hence are the identity components claimed.
  `NatTrans.CommShift κ.hom ℤ` is precisely the last displayed equation for
  the composite shift comparisons, using the supplied `q`. The instance-lambda
  installs that same existential witness, not an unrelated comparison.
- Neither `Functor.IsTriangulated` nor any preservation-of-triangles hypothesis
  appears in the predicate or theorem. The generic structural instances in the
  predicate (stage and transition additivity, stage shifts, scalar `CommShift`,
  associator `CommShift`) are supplied by the recorded canonical PBC modules at
  specialization, not assumptions added to the concrete theorem.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteStagePairCategory`: `pbcStageCategory`, `pbcScalarExtension`,
  `pbcScalarAssociator`, `pbcScalarSystem`, `PbcFiniteStagePairCategory`,
  `StageSystem.pairPreadditive`.
- `Sheaf.Paper.CommonStageCalculus`: `commonStageCalculus`, `pbcRationalHasShift`,
  `pbcScalarCommShift`, `pbcScalarAssociatorCommShift`, `StageSystem.pbcPairHasShift`,
  `StageSystem.pbcStageInclusionCommShift`. These provide the actual shifts on the
  pair-category stages and inclusions (not an independently chosen triangulation).
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and its recorded
  scalar-exactness and coherence companions; imported as the proof dependency.
  The formula uses the normalized scalar system of the pair-category dependency,
  as the item requests, rather than substituting a second coefficient-stage model.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: `StageSystem.Morphism`,
  its fields `Φ`, `β`, `coh`, and the map-at-stage formula `Morphism.mapAt`.
- `WeilConjectures.CategoryTheory.StageSystem.Basic`: `PairCategory.mkHom`,
  `PairCategory.toStage`, `StageSystem.ι` (through the dependency public imports).
- Mathlib `CategoryTheory.Functor.Additive`, `Functor.CommShift`,
  `NatTrans.CommShift`. Read `Pretriangulated`, `IsTriangulated` and
  `Functor.IsTriangulated` from the triangulated dependency's Mathlib matches;
  the node explicitly does not require the latter predicate on `G`.

Source read: the complete current blueprint descent-functors proof named by the node;
compared `PbcDescentFunctors.lean`'s `shiftHom`, `shiftIso`, `descendedCommShift`, and
`inclusionComp_commShift`. Those private declarations concern the constructed functor
and cannot be used as the public statement about an arbitrary prescribed `G`.

Edge cases checked: `n=0` is the `CommShift` zero equation; all negative integers and
`m=-n` are covered without any positivity assumptions by `CommShift` addition.
Repeated fields are included in the unit and associator hypotheses. Zero morphisms,
zero objects, and empty schemes are not excluded. The field-indexing poset is nonempty
and directed by the recorded finite-field construction. Independent coefficient,
source-scheme and target-scheme universes remain independent. No nonempty geometric
scheme, nonzero object, or triangle-preservation assumption has been added.

Searches performed (actual results are also in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder "A prescribed functor between finite coefficient pair
  categories inherits coherent integer shift comparisons and inclusion compatibility
  from shift compatible stage functors"`: 8 hits, including `HasShift.induced`,
  `CommShift.ofInduced`, induced shift-sequence constructions, fully faithful shift
  transfer and `Quotient.liftCommShift`; none is the prescribed pair-category theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.CommShift,
  CategoryTheory.NatTrans.CommShift"`: 12 hits for the existing classes, identities,
  composition, unitor and iso transfer compatibility; no pair-category descent theorem.
- `msearch.py ... grep "descendedCommShift|inclusionComp_commShift|StageSystem|PairCategory"
  CategoryTheory`: 0 Mathlib hits.
- `msearch.py ... leansearch "A functor on a filtered pair category inherits integer shift
  isomorphisms with zero addition coherence and identity inclusion comparisons from
  scalar compatible stage functors"`: 8 hits for `ShiftMkCore.mk`, induced shifts,
  `SingleFunctors`, and shift sequences; no exact match.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `pbcPairFunctorShiftCoherence|pairFunctorShiftCoherence|descendedCommShift|
  inclusionComp_commShift`: only the cited private implementation and its private
  uses in `PbcDescentFunctors.lean`. `grep -rn` for the item id in
  `lean/WeilConjectures` found no existing declaration.

Compilation: the direct concrete signature timed out while elaborating representative
endpoint types. A scratch-prefix diagnosis isolated that occurrence. Packaging the same
formulas as the fully written generic predicate avoids repeatedly unfolding the raw
rational Hom and quotient-functor construction. `scompile.py` then compiled the delivered
module cleanly as sandbox (9.2 seconds) and library module (7.0 seconds). Every theorem
proof in the delivery is `sorry`; the helper definition has its full actual Prop body.
No statement dispute or source correction was needed.

## Second reading by N8

Performed a separate in-thread second pass with the node, final predicate and theorem
open. No separate worker was launched, following the dispatcher's explicit prohibition;
the maintainer's independent review remains the independent reading.

Checked every quantifier and arrow direction against the node: stage `CommShift` gives
natural isomorphisms for all integers with both coherence equations; `A.coh` has the
specified associator orientation; the β-shift premise uses the same scalar comparisons;
`G` is arbitrary and has both object and representative formulas. The component clause
uses the target inclusion applied to exactly the stage `s`, and the inclusion isomorphism
has identity components and the shift equation for the very same existential `q`.
The `HEq` clauses only account for the explicitly supplied object equalities; they do not
replace the specified map by an arbitrary one. The concrete theorem has no additional
structural hypotheses and preserves the independent universes. No mismatch was found.
The only implementation revision was to package the unchanged formulas in a predicate
to make the original statement elaborate within the mandatory compile limit.
