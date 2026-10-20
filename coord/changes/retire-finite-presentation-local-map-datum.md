# AlgebraicGeometry.exists_finitePresentation_local_map_datum

## Reason

The current retirement queue lists `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum`
as a duplicate of the proved upstream module.  The upstream theorem has the same
conclusion with the unnecessary Noetherian instance hypothesis omitted, so it proves
the node statement by specialization.  The two current source consumers already
import the upstream module; no consumer adaptation is required.

## Old

The withdrawn Sheaf declaration was:

```lean
theorem exists_finitePresentation_local_map_datum {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)] (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt] (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] : (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules), Fj.IsFinitePresentation → Fj.IsQuasicoherent → Gj.IsFinitePresentation → Gj.IsQuasicoherent → ∀ φ : (Scheme.Modules.moduleBaseChange f (T := Over.mk (Spec.map (R.map (homOfLE hij)))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶ (Scheme.Modules.moduleBaseChange f (T := Over.mk (Spec.map (R.map (homOfLE hij)))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj, ∃ (j' : I) (hjj' : j ≤ j'), let A := Scheme.Modules.moduleBaseChange f (T := Over.mk (Spec.map (R.map (homOfLE hij)))) (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj'))))) (Over.homMk (Spec.map (R.map (homOfLE hjj'))) (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) let B := Scheme.Modules.moduleBaseChange f (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj'))))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)) ∃ e : Scheme.Modules.moduleBaseChange f (T := Over.mk (Spec.map (R.map (homOfLE hij)))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A ⋙ B, e = Scheme.Modules.tensorPullbackCompositionIso (baseChangeMap f (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj'))))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))) (baseChangeMap f (T := Over.mk (Spec.map (R.map (homOfLE hij)))) (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj'))))) (Over.homMk (Spec.map (R.map (homOfLE hjj'))) (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))) (baseChangeMap f (T := Over.mk (Spec.map (R.map (homOfLE hij)))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) (by rw [← baseChangeMap_comp] congr 1 ext simpa using c.w (homOfLE hjj').op) ∧ ∃ U : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u}, Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧ let Q := modulesPseudofunctor.toDescentData U.f let V := U.pullback₁ (baseChangeMap f (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj'))))) (T' := Over.mk (c.π.app (op i))) (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))) ∃ ψ : Q.obj (A.obj Fj) ⟶ Q.obj (A.obj Gj), ∀ α : A.obj Fj ⟶ A.obj Gj, Q.map α = ψ → ∀ a, (Scheme.Modules.pullback (V.f a)).map (e.hom.app Fj ≫ B.map α) = (Scheme.Modules.pullback (V.f a)).map (φ ≫ e.hom.app Gj))
```


## New

Withdraw `lean/Sheaf/AlgebraicGeometry/FinitePresentationLocalMapDatum.lean` using
`deleted.txt`.  The node now records the existing declaration
`AlgebraicGeometry.exists_finitePresentation_local_map_datum`, whose
signature is the same conclusion without the unused Noetherian instance.  Its theorem
specializes to every old use.  The upstream source module is preserved verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| `WeilConjectures.AlgebraicGeometry.FinitePresentationModuleMapDescent` | unclaimed source | Already imports the upstream twin; no edit. |
| `WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage` | unclaimed source | Already imports the upstream twin; no edit. |

## Status

landed 20261020T233204-L-903947 2026-10-20 (merge of deliver/N1/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum)
