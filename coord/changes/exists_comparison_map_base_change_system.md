# RingHom.exists_comparison_map_base_change_system

## Reason

Repair reviewer X-aec48, head aec48f28c. The old intermediate statement is false:
the sequence-splitting equivalence for A = ℕ → ℤ satisfies hlim on initial-stage
constants while the terminal comparison is the nonsurjective diagonal A → A × A.
The missing hypothesis is compatibility of e with the full limit B inclusion.
The caller already has precisely this hypothesis as he. Stacks Tag 02JO (3)
uses the scalar-compatible comparison, not an arbitrary ring equivalence.

## Old

```lean
theorem exists_comparison_map_base_change_system
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (μB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      μB.toRingHom =
        (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (ψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀))
    (hψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom)
    (hlim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
        e.toRingHom.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom) :
      let J := {j : I // i ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x y}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∃ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
              ∃ (cD : Cocone D) (cE : Cocone E) (f : cD.pt ⟶ cE.pt),
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE),
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ f) ∧
                Function.Bijective f ∧
                (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                  (E.map r) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom)
```

## New

```lean
theorem exists_comparison_map_base_change_system
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      e.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom)
    (i : I) (hi : i₀ ≤ i)
    (aPi : letI := (F.map (homOfLE hi)).hom.toAlgebra
      Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀))
    (μB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P] (↥(colimit F) ⊗[F.obj i₀] B₀))
    (hμB : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      μB.toRingHom =
        (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom)
    (ψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+* (↥(F.obj i) ⊗[F.obj i₀] C₀))
    (hψ : letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom)
    (hlim : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      letI := aPi
      letI := aP
      let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
        e.toRingHom.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom) :
      let J := {j : I // i ≤ j}
      ∃ (aPs : ∀ j : J,
          letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
          Algebra P (↥(F.obj j.val) ⊗[F.obj i₀] B₀)),
        ∃ (D E : J ⥤ CommRingCat.{max v w x y}) (α : D ⟶ E),
          ∃ (d : ∀ j : J,
              letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
              letI := aPs j
              ↥(D.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] B₀) ⊗[P] Q),
            ∃ (c : ∀ j : J,
                letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                ↥(E.obj j) ≃+* (↥(F.obj j.val) ⊗[F.obj i₀] C₀)),
              ∃ (cD : Cocone D) (cE : Cocone E) (f : cD.pt ⟶ cE.pt),
                ∃ (_hD : IsColimit cD) (_hE : IsColimit cE),
                (∀ j, α.app j ≫ cE.ι.app j = cD.ι.app j ≫ f) ∧
                Function.Bijective f ∧
                (∀ {j k} (r : j ⟶ k), IsPushout (α.app j) (D.map r)
                  (E.map r) (α.app k)) ∧
                (∀ j : J,
                  letI := (F.map (homOfLE (hi.trans j.property))).hom.toAlgebra
                  letI := aPs j
                  ((c j).toRingHom.comp ((α.app j).hom.comp (d j).symm.toRingHom)).comp
                    (Algebra.TensorProduct.includeLeftRingHom (R := P)
                      (A := ↥(F.obj j.val) ⊗[F.obj i₀] B₀) (B := Q)) =
                    (Algebra.TensorProduct.map (Algebra.ofId (F.obj j.val) (F.obj j.val))
                      φ₀).toRingHom)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ComparisonMapBaseChangeSystem | E3 | Add he to the intermediate theorem; correct its proof docstring and node. |
| Sheaf.RingTheory.FinitePresentationComparisonSystem | unclaimed | Forced proof-only adaptation: pass the already assumed he after e at line 142. Every signature, visibility, import and other proof line is unchanged. |

The downstream declaration-use search lists exactly these two modules. The sole DAG
citer is lem-weil-pbc-finite-presentation-comparison-system; its statement remains
valid because it already assumes he. All further downstream interfaces, including
the five targets, remain identical. No definition is changed, so no target acquires
a different meaning through a definition change.

Forced-adaptation evidence: the original caller compiles against the shared baseline
(exit code 0, 4.8 s). Against the corrected sandbox dependency it fails at 143:6:

```text
error: Application type mismatch: The argument
  i
has type
  I
of sort `Type v` but is expected to have type
  e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
    (Algebra.TensorProduct.map (Algebra.ofId ↑(colimit F) ↑(colimit F)) φ₀).toRingHom
of sort `Prop` in the application
  exists_comparison_map_base_change_system F i₀ B₀ C₀ φ₀ P Q aP e i
```

The adapted caller compiles against that same corrected dependency (exit code 0,
4.9 s). The only caller edit inserts he after e. This set requires CODEX review.

## Status

landed 20261013T095944-L-2455725 2026-10-13 (merge of deliver/E3/Sheaf.RingTheory.ComparisonMapBaseChangeSystem)
