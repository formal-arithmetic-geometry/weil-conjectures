# Weil SHEAF, stage 3: the four remaining gaps

State of the live repository (`weil-conjectures-sheaf`, branch `sheaf-dag`), 2026-10-15 14:00 JST. The targets' import closure contains exactly four modules with `sorry`, one `sorry` each. Everything else the six targets of `lean/Challenge.lean` need is proved.

All four gaps serve a single target, `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` (and its separably closed variant) in `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`: invariance of the étale cohomology of a curve under an extension of algebraically closed fields. They reach it along two routes:

- Gaps 1 and 2 through the limit / continuity argument (`LimitHigherDirectImageExchange` → `SmoothLimitDerivedDirectImageExchange` → `FieldExtensionHigherDirectImageExchange` → `AlgClosedExtensionInjectiveAcyclic` → `SmoothCalculations`).
- Gaps 3 and 4 through Serre duality for smooth proper curves (`SerreDuality` → `SmoothCalculations`), 37 and 51 import steps from the target.

**Question for the experts.** Gaps 3 and 4 are needed only because our proof of `SmoothCalculations` goes through Serre duality and the relative dualizing complex. Is there a route to the field-extension invariance for curves that avoids it? If so, both gaps leave the closure.

---

## Gap 1. Naturality of the cartesian chart identification with the derived exchange map

Module `Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality`, theorem `cartesianChartCohomologyLift_exchange`. Blueprint `lem-sc-cartesian-chart-exchange-naturality`.

**Mathematics.**
- Setting:
  - `f : X → S` is a morphism of schemes and `F` an abelian étale sheaf on `X`.
  - `D` is an inverse system of `S`-schemes with a limit cone `c`.
  - `V` is étale over a stage `D_i`, and `U = V ×_{D_i} lim D` is its pullback to the limit.
- Statement: for every stage `j → i` and every class `x` in `H^q` of the cartesian chart `(X ×_S D_i)|_V` at `j`, the following two maps agree:
  - the lift of `x` to the limit chart, followed by the derived base-change (exchange) map `Lπ_j^* R(f_j)_* F → R(f_∞)_* π^* F`;
  - the image of `x` under the identification of the chart cohomology on `U`, after restricting along the chart cone.
- So this is an identity between constructed maps; no choice is involved.
- Sources: Stacks 0EYM, 03Q8, 03CB, 09YQ.

**Status.** The mathematics is clear: the proof is a diagram chase with mates and the adjunction triangle identities, as in the docstring below. The remaining difficulty is Lean engineering: elaborating the final rewrite times out because of a hidden parenthesization in the composite. A strong prover session is working on it, and the helper lemmas (chart leg, transport, evaluation, comparison) are proved.

```lean
/-- The explicit chart lift and apex isomorphism commute with the specified
cartesian derived exchange. This asserts an identity between constructed maps;
it does not choose an isomorphism, lift, coefficient object, or representative.
Source: Stacks Project, Tags 0EYM, 03Q8, 03CB and 09YQ.
(blueprint: lem-sc-cartesian-chart-exchange-naturality).

Proof: Apply rawRestrictedCohomologyComparison_naturality to the chart cone leg
with its upperStarComp coefficient map. It identifies the inverse evaluation of
the restricted cohomology map with abelianHigherDirectImageRawPullback of the
stage class. Expand cartesianChartRawAdjunctionIso on both sides. Pullback
uniqueness identifies the two arrows from the actual apex source to the chart
stage: the inverse chart identification followed by the chart leg equals the
cartesian projection followed by the inverse stage identification. Each equality
is checked after the two pullback projections. Inverse-image composition then
identifies the coefficient maps and the free-sheaf source maps; its associativity
and naturality cancel the chart identifications. Take derived adjoints under the
apex projection. Replace derivedBaseChangeMapPlus by its mate using
baseChange_eq_derivedBaseChangeMapPlus. The adjunction triangle identity cancels
the stage counit with its unit, leaving exactly the pullback of the raw stage
class followed by the coefficient comparison. Naturality of the single-functor
and shift comparisons identifies these factors with the definition of
abelianHigherDirectImageRawPullback. Undoing the raw evaluation comparison proves
the equation. The free-sheaf source is transported by the specified pullback
square hr throughout; no invertibility of exchange is used. Empty test objects
and q=0 require no separate argument. -/
theorem cartesianChartCohomologyLift_exchange
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    cartesianChartCohomologyLift f D c F q i V U r hr j x ≫
      (shiftFunctor _ (q : ℤ)).map
        (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
          (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
    (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V U r hr).hom
      (restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x) := by
  sorry
```

---

## Gap 2. A class on the limit has a chart representative at a finite stage (continuity)

Module `Sheaf.AlgebraicGeometry.CartesianRawClassChartRepresentative`, theorem `exists_cartesianRawClass_chart_representative`. Blueprint `lem-sc-cartesian-raw-class-chart-representative`.

**Mathematics.**
- Setting:
  - `k` is a field and `(D_i)` a cofiltered system of quasi-compact, quasi-separated `k`-schemes with affine transitions; `X_∞ = lim D_i` is quasi-compact and quasi-separated.
  - `f : X → Spec k` is quasi-compact and quasi-separated, and `F` an abelian étale sheaf on `X`.
  - `V` is an affine étale `X_∞`-scheme, and `z ∈ Hom_{D^+}(ℤ[V], π_i^* R(f_i)_* F [q])`, i.e. a class in `H^q(V, π_i^* R(f_i)_* F)`.
- Statement:
  - There exist a stage `j`, an affine étale `W → D_j` with `V = W ×_{D_j} X_∞`, a further stage `l → j` and a class `x` in `H^q` of the cartesian chart `(X ×_k D_j)|_W` at `l`.
  - These satisfy: (a) `z` followed by the exchange map equals the image of `x` on the limit chart; (b) the same holds compatibly after every further transition `m → l`.
- This is the existence half of continuity of étale cohomology along limits (Stacks 09YQ, 0EYL, 0GIT), in the raw derived-Hom form, together with its compatibility with the exchange square (Stacks 0EYM). No vanishing is asserted.

**Status.**
- This gap was split off when a group proved the vanishing statement `CartesianHigherImageSingleRawClassVanishing` from it.
- The prover session reported as missing an identification `Hom_{D^+}(ℤ[V], K[q]) ≅ H^q(V, K)` for bounded-below `K`, natural in `V` and compatible with pullback along the cartesian transitions.
- The route we gave it: the free–forget adjunction, with `Hom(ℤ[V], −) = Γ(V, −)` and `ℤ[V]` needing no resolution, so computing with an injective resolution of `K` gives `RHom(ℤ[V], K) = RΓ(V, K)`. The compatibility with pullback comes from the mates under inverse image.
- The derived continuity theorem itself is already in the library. An expert check of that route, or a pointer to a cleaner one, would help.

```lean
/-- A raw stage class admits a chart representative after one further base change.

Source: Stacks Project, Tags 0EYL and 0GIT for descent with the original stage
coefficient complex fixed; Tag 0EYM for the exchange comparison square.
(blueprint: lem-sc-cartesian-raw-class-chart-representative).

Proof: Restrict the inverse system to arrows into i and descend the affine test
object to an affine etale model. The resulting models form a limiting qcqs system
with affine transitions. Apply derived cohomology continuity with the fixed
bounded-below complex cartesianDerivedImage f (D.obj i).hom F[0]. The free
representable sections adjunction identifies the given raw class with the
hypercohomology of its pullback to V, so surjectivity gives a representative at
one model. For this identification with arbitrary bounded-below coefficients,
take a bounded-below injective representative: evaluation at the free
representable generator computes its restricted derived sections. Replace the
descended affine model by its base change to the representative's stage and
rename that stage j; it is still affine because the transition is affine.
Apply the stage exchange to that representative. Derived adjunction
and the raw restricted cohomology comparison identify it with x on the
cartesian chart. Let l be the identity object at this new stage, and let b be
its arrow to i. Pasting of exchange maps identifies the limit image of x with
the limit image of z. For any arrow a to l, naturality of restricted cohomology,
derived adjunction, the exact inverse-image single and shift comparisons, and
exchange pasting identify the pullback of x with z followed by the displayed
transition along a.left followed by b. These are equalities of specified maps,
before invoking continuity on the chart system. No zero hypothesis or eventual
vanishing is asserted. The argument also includes empty affine V and q=0.
-/
theorem exists_cartesianRawClass_chart_representative
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
 :
    ∃ (j : I) (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
      (r : V.left ⟶ W.left)
      (hr : IsPullback r V.hom W.hom (c.π.app j).left)
      (l : Over j) (b : l.left ⟶ i)
      (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        (q : ℤ) ((cartesianChartDiagram f D j).obj l) W),
      z ≫ (shiftFunctor _ (q : ℤ)).map
          (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
            (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
        (cartesianChartCohomologyIso f (D.obj j).hom (c.π.app j).left c.pt.hom
          (Over.w (c.π.app j)).symm F q W V r hr).hom
          (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
            (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
            (q : ℤ) ((cartesianChartCone f D c j).π.app l) W x) ∧
      ∀ (m : Over j) (a : m ⟶ l),
        z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app m.left).left (D.map (a.left ≫ b)).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w (a.left ≫ b))).symm).hom.app _ ≫
            (D+(((c.π.app m.left).left)^*[AddCommGrpCat.{u + 1}])).map
              (cartesianDerivedImageMap f (D.obj i).hom (D.obj m.left).hom
                (D.map (a.left ≫ b)).left (Over.w (D.map (a.left ≫ b))).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
          cartesianChartCohomologyLift f D c F q j W V r hr m
            (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
              (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
              (q : ℤ) ((cartesianChartDiagram f D j).map a) W x) := by
  sorry
```

---

## Gap 3. Core of the object realization on an overlap, in the limit of derived categories of perfect complexes

Module `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData`, theorem `perfect_overlap_object_realization_core_of_data`. Blueprint `lem-pc-perfect-overlap-object-realization-core-of-data`.

**Mathematics.**
- Setting:
  - `(R_i)` is a directed system of rings with colimit `R`, and `Z → Spec R_i` is of finite presentation, quasi-compact and quasi-separated.
  - `Y_j = Z ×_{R_i} R_j` and `X = Z ×_{R_i} R`.
  - `Y_j = U ∪ V` with `U`, `V` quasi-compact opens; `A`, `B` are perfect complexes on `U`, `V`; `E ∈ D(X)`.
  - `φ_U : g^*A ≅ E|_{g^{-1}U}` and `φ_V : g^*B ≅ E|_{g^{-1}V}`.
- Statement:
  - Over the overlap `U ∩ V`, the restrictions of `A` and `B` pulled back to every stage `k ≥ j`, together with the comparisons `ψ_k` to `E|_{U ∩ V}` built from `φ_U` and `φ_V`, form a coherent system.
  - Concretely: the transition functors between stages, the base comparisons and the "pins", i.e. the equations fixing the transitions and the objects.
  - This system realizes `E|_{U ∩ V}` in the colimit of the derived categories of the stages.
- This is the overlap step in gluing perfect complexes along a limit of schemes: `D_perf(X) = colim_k D_perf(Y_k)` (Stacks 08DW, 0D5S).

**Status.**
- The unrestricted statement (for arbitrary stagewise data) was false. Counterexample: the transports at different stages can be twisted independently.
- It was corrected on 2026-10-15 (commit e2928e181f) to require the canonical comparison family.
- What remains is a coherence statement: the canonical `schemeComparisonFromRestrictions` and the open-site equivalence comparisons agree with the fixed `perfectHomComparison` after `perfectOverlapStageEquivalence`. That gives the natural isomorphism `G_k ⋙ apex ≅ stage_k ⋙ transition_k` and its component equation for `ψ_k`.
- Lean side: the dependent record caused kernel timeouts. The session has made the transitions opaque (the file now compiles in 21 s) and is proving the two coherence lemmas.
- A mathematically simpler formulation of the overlap step, for example avoiding the explicit 2-colimit data, would be welcome.

```lean
/-- Given the canonical stagewise comparison data, the transition and object pins
are assembled into the core realization structure.  The transition is obtained by
conjugating the overlap pullback functor by the fixed stage and apex equivalences.
The counit-pinned derived-pullback composition comparison gives `baseComparison`
and `transition_pin`; its naturality gives `comparison`.  Expanding the prescribed
`ψ` and the theta equations cancels the site unit and counit and proves `object_pin`.
This is the cartesian composition calculation from Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-of-data).
-/
-- The canonicality hypothesis rules out independently twisted transports, which
-- make the unrestricted statement false (K1 delivery report).
theorem perfect_overlap_object_realization_core_of_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k) :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X),
    let instP : Category (schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme) := inferInstance
    let instQ : Category (schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme) := inferInstance
    let instX : Category (schemeDerivedCategory X) := inferInstance
    let PU : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ U).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory
    let PV : schemeDerivedCategory X ⥤ schemeDerivedCategory (gj ⁻¹ᵁ V).toScheme :=
      (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory
    ∀ (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        PU.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        PV.obj E),
      let P := gj ⁻¹ᵁ U
      let Q := gj ⁻¹ᵁ V
      let RU := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) P).mapDerivedCategory
      let RV := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) Q).mapDerivedCategory
      let RW := (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
      let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
      let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
      let τU : RU ⋙ SP ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
      let τV : RV ⋙ SQ ≅ RW := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
          (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    ∀ (data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij hstage
        U V hcover hU hV A B hA hB E φU φV k hjk),
    data = perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
      U V hcover hU hV A B hA hB E φU φV →
    Nonempty (
      let K := {k : I // j ≤ k}
      let C : K → Type (u + 1) := fun k ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        schemeDerivedCategory (U' ⊓ V').toScheme
      let F : (k : K) → Bool → C k := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let SU : schemeDerivedCategory U'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ U' from inf_le_left))).mapDerivedCategory
        let SV : schemeDerivedCategory V'.toScheme ⥤
            schemeDerivedCategory (U' ⊓ V').toScheme := (schemeOpenOverlapRestriction Yk
          (homOfLE (show U' ⊓ V' ≤ V' from inf_le_right))).mapDerivedCategory
        if b then SV.obj B' else SU.obj A'
      let G : (k : K) → C k ⥤
          DerivedCategory (SheafOfModules.{u}
            ((moduleRings X.toRingedSpace).over (P ⊓ Q))) := fun k ↦
        (data k.val k.property).d.toDiagram.HW
      let ψ : ∀ k b, (G k).obj (F k b) ≅ RW.obj E := fun k b ↦
        let Yk := pullback t (Spec.map (R.map (homOfLE (hij.trans k.property))))
        let f := baseChangeMap t
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let U' := f ⁻¹ᵁ U
        let V' := f ⁻¹ᵁ V
        let A' : schemeDerivedCategory U'.toScheme := (derivedPullback (f ∣_ U)).obj A
        let B' : schemeDerivedCategory V'.toScheme := (derivedPullback (f ∣_ V)).obj B
        let d := (data k.val k.property).d
        let θU := (data k.val k.property).θU
        let θV := (data k.val k.property).θV
        match b with
        | true => d.toDiagram.γV.symm.app B' ≪≫ SQ.mapIso θV ≪≫ τV.app E
        | false => d.toDiagram.γU.symm.app A' ≪≫ SP.mapIso θU ≪≫ τU.app E
      let stageEquiv : ∀ k : K, C k ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (R.map (homOfLE k.property)))) := fun k ↦
        let arrow : Over.mk (Spec.map (R.map (homOfLE (hij.trans k.property)))) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (R.map (homOfLE k.property)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
        perfectOverlapStageEquivalence (baseChangeMap t arrow)
          (pullback.snd t (Spec.map (R.map (homOfLE (hij.trans k.property)))))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (R.map (homOfLE k.property))) (isPullback_baseChangeMap t arrow) U V
      let apexEquiv : DerivedCategory (SheafOfModules.{u}
          ((moduleRings X.toRingedSpace).over (P ⊓ Q))) ≌
          schemeDerivedCategory (pullback
            ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
            (Spec.map (c.ι.app j))) :=
        let arrow : Over.mk (Spec.map (c.ι.app i)) ⟶
            Over.mk (Spec.map (R.map (homOfLE hij))) :=
          Over.homMk (Spec.map (c.ι.app j))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
        perfectOverlapApexEquivalence gj
          (pullback.snd t (Spec.map (c.ι.app i)))
          (pullback.snd t (Spec.map (R.map (homOfLE hij))))
          (Spec.map (c.ι.app j)) (isPullback_baseChangeMap t arrow) U V
      PerfectHomObjectRealizationCore R c j C F _ (fun _ ↦ RW.obj E) G ψ
        (U ⊓ V).toScheme
        ((U ⊓ V).ι ≫ pullback.snd t (Spec.map (R.map (homOfLE hij))))
        (fun b ↦ if b then
          (derivedPullback (Yj.homOfLE (inf_le_right : U ⊓ V ≤ V))).obj B
          else (derivedPullback (Yj.homOfLE (inf_le_left : U ⊓ V ≤ U))).obj A)
        stageEquiv apexEquiv) := by
  classical
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV data hdata
  sorry
```

---

## Gap 4. Naturality of the Tor coordinates of a quasi-coherent tensor resolution under restriction

Module `Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality`, theorem `tensorResolutionCoordinateSections_naturality`. On the route to the Koszul / self-Ext computation for regular immersions used by the relative dualizing complex of a smooth morphism.

**Mathematics.**
- Setting:
  - `Y` is a scheme and `M`, `N` are quasi-coherent; `K → M` and `F → N` are K-flat resolutions.
  - For every affine open `U` there are module models `M(U) ≅ MA(U)`, `N(U) ≅ NA(U)` and a projective resolution `P(U) → MA(U)`.
  - The coordinates identify `H^{-n}(K ⊗ N)(U)` with `H_n(P(U) ⊗ NA(U)) = Tor_n^{Γ(U)}(MA(U), NA(U))`.
- Statement:
  - Take affine opens `V ⊆ U` and semilinear comparisons `a : P(U) → P(V)`, `b : NA(U) → NA(V)` and `k = a ⊗ b`, compatible with the augmentations and the module models.
  - Then restricting from `U` to `V` on the homology sheaf corresponds, in these coordinates, to the map on `Tor` induced by `k`.
- This is naturality of the computation of local `Tor` by projective resolutions.

**Status.** No mathematical content is in doubt. The proof in the docstring is a chain of naturality squares. Most helper lemmas are already proved and committed (chart augmentation, chart tensor isomorphism, coordinate isomorphism, section coordinates, restriction naturality on tensor summands). The prover session is closing the last assembly.

```lean
/-- The canonical chart coordinates commute with any augmented semilinear tensor comparison.

Proof in words: the augmentation formula for `a` gives the first chain square by
`tensorResolutionChartAugmentation_naturality`. The coefficient formula for `b`
and the pure-tensor formula for `k` give the second chain square by
`tensorResolutionChartTensorIso_naturality`: check each nonpositive degree on
pure tensors, then use the tensor-product universal property, and use the zero
object in the remaining degrees. The common K-flat zigzag is natural for those
two squares, so `tensorResolutionCoordinateSheafIso_naturality_of_squares`
gives equality of the sheaf comparison maps. Apply global sections on the two
affine spectra and the units of the affine restriction adjunction.
`tensorResolutionSection_naturality` identifies the resulting right-hand map
with restriction of the global homology sheaf. Finally,
`tensorResolutionSemilinearMap_homology` identifies the left-hand map with
`HomologicalComplex.homologyMap k` followed by `mapHomologyIso`. This is the
displayed equation after applying the two section equivalences. -/
theorem tensorResolutionCoordinateSections_naturality
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (b : NA U →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] NA V)
    (a : (P U).complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj
        (P V).complex)
    (k : ((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj (P U).complex ⟶
      ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (.down ℕ)).obj
        (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj (P V).complex))
    (ha : ∀ x : (P U).complex.X 0,
      sM V ((P V).π.f 0 (a.f 0 x)) =
        M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x)))
    (hb : ∀ y : NA U,
      sN V (b y) = N.val.map (homOfLE h).op (sN U y))
    (hk : ∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
      k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
        (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let Q := (CochainComplex.mapBifunctor K
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)
      (curriedTensor Y.Modules)).homology (-(n : ℤ))
    let e := (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj
      (P V).complex).sc n |>.mapHomologyIso
        (ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom)
    ∀ x, Q.val.map (homOfLE h).op
        (tensorResolutionCoordinateSections Y M N U (MA U) (NA U)
          (sM U) (sN U) (P U) K F q s hK hF hq hs n x) =
      tensorResolutionCoordinateSections Y M N V (MA V) (NA V)
        (sM V) (sN V) (P V) K F q s hK hF hq hs n
        (e.hom (HomologicalComplex.homologyMap k n x)) := by
  sorry
```
