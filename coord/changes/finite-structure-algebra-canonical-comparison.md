# AlgebraicGeometry.finite_structure_algebra_operations_lift

## Reason

The old hc names Classical.choice of a bare Nonempty natural-isomorphism type. It
cannot specify a canonical comparison: proof irrelevance erases the constructed
witness, and natural module automorphisms need not preserve units. The conclusion
uses the adjunction pinned by exists_tensorPullbackAdjunction. Replace hc with the
inverse of tensorPullbackCompositionIso, the explicit mate built from these same
pinned adjunctions. The corrected normalization argument is moved to the end of the
argument list, so the obsolete call fails at a simple argument boundary rather than
spending the counterfactual compile limit comparing expanded adjunction formulas.
This repairs the recorded statement dispute without changing
any target or conclusion. The new transition lemma proves its required unit equation.

## Old

```lean
theorem finite_structure_algebra_operations_lift (A : Type u) [CommRing A] (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))))) (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))) (hc : ∀ n : ℕ, c n = (Classical.choice (Scheme.Modules.nonempty_tensorPullbackComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))))).symm ≪≫ eqToIso (congrArg Scheme.Modules.tensorPullback (hi n))) (Yn : ℕ → Scheme.{u}) (fnY : ∀ n, Yn n ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) [∀ n, IsFinite (fnY n)] (gn : ∀ n, Yn n ⟶ Yn (n + 1)) (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1))) (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) = fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G) (hproper : Scheme.Modules.HasSupportProperOver f G) (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅ (Scheme.Modules.pushforward (fnY n)).obj (SheafOfModules.unit (Yn n).ringCatSheaf)) (hψ : ∀ n, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫ (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n) (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫ (Scheme.Modules.pushforward (fnY n)).map (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) = (c n).hom.app G ≫ (ψ n).hom) : ∃ B : X.CommAlgebraSheaf, ∃ e : B.toModule ≅ G, ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))), (∀ (n : ℕ) (U : X.Opens) (x : B.right.obj.obj (op U)), ((b n).right.hom.app (op U)).hom x = ((Scheme.Modules.pushforwardComp (fnY n) (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).hom.app (SheafOfModules.unit (Yn n).ringCatSheaf)).app U (((Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map e.hom ≫ (ψ n).hom)).app U (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))).unit.app B.toModule).app U x))) ∧ (∀ (n : ℕ) (U : X.Opens), (b (n + 1)).right.hom.app (op U) ≫ (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U) ((fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) (by rw [← Scheme.Hom.comp_preimage, hw n]) = (b n).right.hom.app (op U))
```

## New

```lean
theorem finite_structure_algebra_operations_lift (A : Type u) [CommRing A] (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))))) (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))) (Yn : ℕ → Scheme.{u}) (fnY : ∀ n, Yn n ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) [∀ n, IsFinite (fnY n)] (gn : ∀ n, Yn n ⟶ Yn (n + 1)) (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1))) (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) = fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G) (hproper : Scheme.Modules.HasSupportProperOver f G) (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅ (Scheme.Modules.pushforward (fnY n)).obj (SheafOfModules.unit (Yn n).ringCatSheaf)) (hψ : ∀ n, (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫ (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n) (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫ (Scheme.Modules.pushforward (fnY n)).map (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) = (c n).hom.app G ≫ (ψ n).hom) (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm) : ∃ B : X.CommAlgebraSheaf, ∃ e : B.toModule ≅ G, ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))), (∀ (n : ℕ) (U : X.Opens) (x : B.right.obj.obj (op U)), ((b n).right.hom.app (op U)).hom x = ((Scheme.Modules.pushforwardComp (fnY n) (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).hom.app (SheafOfModules.unit (Yn n).ringCatSheaf)).app U (((Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map ((Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map e.hom ≫ (ψ n).hom)).app U (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))).unit.app B.toModule).app U x))) ∧ (∀ (n : ℕ) (U : X.Opens), (b (n + 1)).right.hom.app (op U) ≫ (gn n).appLE ((fnY (n + 1) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⁻¹ᵁ U) ((fnY n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⁻¹ᵁ U) (by rw [← Scheme.Hom.comp_preimage, hw n]) = (b n).right.hom.app (op U))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | C4 | Assigned corrected statement, proved from algebra construction and the proved transition lemma. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | Sole direct declaration user. Its unchanged signature still assumes the old bare comparison; the application no longer typechecks. Replace only its proof by the named existing hole and flag the unresolved normalization. |

The 194 transitive import users reported by downstream.py do not mention the changed
declaration. FiniteStructureAlgebraLift keeps its complete elaborated type and public
imports, so these transitive users are unaffected. No target statement or definition
changes. The caller's hole is deliberately reopened rather than asserting equality
between an arbitrary choice and the explicit mate. The canonical comparison repair
must subsequently propagate through the caller's own interface and system dictionary.

The forced adaptation changes the body beginning with the old `obtain` application
through the end of its proof to `:= by sorry`; no existing signature or visibility
changes. Retaining the remainder of the original proof would require a local hole at
the broken application, which the stage-3 contract forbids: every remaining hole must
be a named public theorem with body exactly `:= by sorry`. Its complete original proof remains in the repository and in the compiler
counterfactual. The preflight compiles the original against the delivered dependencies
and confirms the failure, and compiles the adapted version. This is a statement repair
and decomposition, with one additional pre-existing theorem hole reopened, not net proof
progress.

## Status

landed 20261013T130749-L-3985816 2026-10-13 (merge of deliver/C4/Sheaf.Paper.FiniteStructureAlgebraOperationsLift)
