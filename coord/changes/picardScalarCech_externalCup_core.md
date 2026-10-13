# picardScalarCech_externalCup_core

## Reason

Repair of reviewer X-2527f (head 2527f78d2), E1/E2 point 4. The uncovered core
is false: take R = Q[t], A = R[t^-1], X = Spec R, F associated to
A direct-sum (A/R), U = {D(t)}, Y = Spec Q and G = O_Y with its full cover.
Restriction of F to D(t) is the projection to A. The R-linear sections
s0(x) = (x,0) and s1(x) = (x,[x]) both satisfy the resolution comparison
equations for every resolution. Choose eX from s0 and eP from s1. At degree
zero and x = t^-1, the claimed equality compares (x,[x]) with (x,0), and fails.
The nonzero quotient class disappears on restriction, so quantifying over
resolutions does not remove the ambiguity. The family U does not cover X.

Remove the false core rather than retain an inconsistent unresolved dependency.
Restore the covered theorem's whole proof to `sorry`, retaining its signature
and complete proof docstring. Its proof must use the cover hypotheses.

## Old

```lean
theorem picardScalarCech_externalCup_core
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) [F.IsQuasicoherent] (G : Y.Modules) [G.IsQuasicoherent]
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCechCupComponent f g U V F G c)
    (eX : ∀ p : ℕ, ((picardCechFunctor f U).obj F).homology p →ₗ[k]
      scalarCohomology f F p)
    (heX : ∀ p, IsPicardScalarCechComparison f U F p (eX p))
    (eY : ∀ q : ℕ, ((picardCechFunctor g V).obj G).homology q →ₗ[k]
      scalarCohomology g G q)
    (heY : ∀ q, IsPicardScalarCechComparison g V G q (eY q))
    (eP : ∀ n : ℕ,
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj
            (externalCupCoefficients f g F G)).homology n →ₗ[k]
        scalarCohomology (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n)
    (heP : ∀ n, IsPicardScalarCechComparison (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) n (eP n)) :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
    T.iCycles n z = HomologicalComplex.ιMapBifunctor A B
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ) i.val.1 i.val.2 n
        i.property ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
      eP n (HomologicalComplex.homologyMap c n (T.homologyπ n z)) =
        cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G) d)) i.property)
          (externalCup f g F G i.val.1 i.val.2
            (eX i.val.1 (A.homologyπ _ a)) (eY i.val.2 (B.homologyπ _ v))) := by
  sorry
```

The covered theorem previously applied this core after introducing its cycles;
its cover hypotheses hUc and hVc were unused.

## New

The entire core declaration and its docstring are removed. There is no
replacement core declaration. The covered declaration
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup` keeps its exact
signature and docstring, with proof `:= by sorry`.

For `lem-sc-picard-scalar-cech-external-cup-core`, clear the `lean` record,
proof and proof dependencies and record this retirement in `proof_origin`.
The historical mathematical statement is preserved, not weakened. For
`lem-sc-picard-scalar-cech-external-cup`, retain the source-based covered proof
plan and explicitly require the cover equalities in its comparison step;
record that this plan is unresolved, not proved through the removed core.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | C1 | Sole Lean user: picardScalarCech_externalCup; replace its application of the removed core with the explicit unresolved proof obligation. |

A search of all library Lean sources found no other use of the core.
All downstream statements, definitions, signatures, visibility and imports are
unchanged. No target statement changes, and no consumer module needs adaptation.
The covered theorem now depends directly on its own unresolved proof, rather
than on the false uncovered statement. The blueprint unit route is preserved.

## Status

landed 20261013T201738-L-3965489 2026-10-13 (merge of deliver/C1/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
