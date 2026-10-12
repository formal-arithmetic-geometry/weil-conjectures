# Algebra.popescu_char_p_preparation_quotient
## Reason
The old quotient theorem was false: k=F₅, m=0, A=C=k[ε]/(ε²), Λ=k[t],
γ=α evaluation ε↦0, β=id, q=(t), r=1 and π₀=0 satisfy its assumptions,
but J=0 and Λ_q has dimension one. The repaired boundary retains auxiliary
thickening factorization and power-containment witnesses from the actual construction.
The caller's signature stays unchanged.
## Old
```lean
theorem popescu_char_p_preparation_quotient
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (m : ℕ) [Algebra (MvPolynomial (Fin m) k) Λ]
      [IsScalarTower k (MvPolynomial (Fin m) k) Λ]
    (C : Type (max u v)) [CommRing C] [Algebra k C]
      [Algebra (MvPolynomial (Fin m) k) C]
      [IsScalarTower k (MvPolynomial (Fin m) k) C]
      [FinitePresentation (MvPolynomial (Fin m) k) C]
    (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ)
    (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k)
    (hbase : (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ)
    (hparam : 1 ≤ r ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin r)
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin r)
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ i, IsStrictlyStandardElement
        (R := MvPolynomial (Fin m) k)
        (algebraMap (MvPolynomial (Fin m) k) C (π i)))) :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let J_C := J.map (algebraMap R C)
    let J_Λ := J.map (algebraMap R Λ)
    let R₀ := R ⧸ J
    let C₀ := C ⧸ J_C
    let Λ₀ := Λ ⧸ J_Λ
    ∃ (_ : FinitePresentation R₀ C₀) (γ₀ : C₀ →ₐ[R₀] Λ₀)
      (q₀ : PrimeSpectrum Λ₀),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      (¬ popescuIdeal γ₀ ≤ q₀.asIdeal ∨
        q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes ∧
        ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
        let P := Localization.AtPrime (q₀.asIdeal.under R₀)
        let L := Localization.AtPrime q₀.asIdeal
        letI := Localization.AtPrime.algebraOfLiesOver
          (q₀.asIdeal.under R₀) q₀.asIdeal
        ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
          EssentiallySmooth P E ∧
          ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L)
              ((IsScalarTower.toAlgHom R₀ Λ₀ L).comp γ₀)
              (fun _ _ ↦ Commute.all _ _))
```
## New
```lean
theorem popescu_char_p_preparation_quotient
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (m : ℕ) [Algebra (MvPolynomial (Fin m) k) Λ]
      [IsScalarTower k (MvPolynomial (Fin m) k) Λ]
    (C : Type (max u v)) [CommRing C] [Algebra k C]
      [Algebra (MvPolynomial (Fin m) k) C]
      [IsScalarTower k (MvPolynomial (Fin m) k) C]
      [FinitePresentation (MvPolynomial (Fin m) k) C]
    (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ)
    (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k)
    (hbase : (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ)
    (hparam : 1 ≤ r ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin r)
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin r)
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin r, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ i, IsStrictlyStandardElement
        (R := MvPolynomial (Fin m) k)
        (algebraMap (MvPolynomial (Fin m) k) C (π i))))
    (hconstruction :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I : Ideal Q) (K : Ideal L),
        I ≤ JQ ∧ K ≤ JL ∧ I.map (algebraMap Q L) ≤ K ∧
        ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra Q D)
          (_ : Algebra (Q ⧸ I) D) (_ : IsScalarTower Q (Q ⧸ I) D),
          EssentiallySmooth (Q ⧸ I) D ∧
          ∃ (f : Q ⊗[R] C →ₐ[Q] D) (g : D →ₐ[Q] L ⧸ K),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId Q (L ⧸ K))
              ((Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ))
              (fun _ _ ↦ Commute.all _ _)) :
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
    let J_C := J.map (algebraMap R C)
    let J_Λ := J.map (algebraMap R Λ)
    let R₀ := R ⧸ J
    let C₀ := C ⧸ J_C
    let Λ₀ := Λ ⧸ J_Λ
    ∃ (_ : FinitePresentation R₀ C₀) (γ₀ : C₀ →ₐ[R₀] Λ₀)
      (q₀ : PrimeSpectrum Λ₀),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      (¬ popescuIdeal γ₀ ≤ q₀.asIdeal ∨
        q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes ∧
        ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
        let P := Localization.AtPrime (q₀.asIdeal.under R₀)
        let L := Localization.AtPrime q₀.asIdeal
        letI := Localization.AtPrime.algebraOfLiesOver
          (q₀.asIdeal.under R₀) q₀.asIdeal
        ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
          EssentiallySmooth P E ∧
          ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L)
              ((IsScalarTower.toAlgHom R₀ Λ₀ L).comp γ₀)
              (fun _ _ ↦ Commute.all _ _))
```
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.PopescuCharPPreparation | V3 | proof passes the strengthened construction witnesses |
## Status
landed 20261012T150958-L-2232705 2026-10-12 (merge of deliver/V3/Sheaf.RingTheory.PopescuCharPPreparation)
