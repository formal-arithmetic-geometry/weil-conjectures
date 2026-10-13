# AlgebraicGeometry.sections_over_quasiCompactOpen_of_affine

## Reason

Repair of reviewer X-c4c20, head c4c209b0b, E2/H3 review point 4.
The previous Sigma domains were disjoint unions, not the direct limits specified
by Stacks Properties Lemma 01PM and the node. For A = M = Z, I = 0, D empty,
N_0 = 0 and N_n = Z for n > 0, their zero maps at indices 0 and 1 are distinct
but have equal images. The old injectivity assertion was false.

The corrected statement presents both Hom systems by diagrams of additive groups,
with isomorphisms identifying each stage with its Hom group. Their maps are
specified at every n <= m: restriction along the literal ideal inclusion `r`,
and restriction followed by the literal quotient projection `q`. The equations
on underlying ideal elements and on all quotient classes uniquely determine
these maps. In particular the adjacent transition maps are precisely those of
the node. Taking additive-group colimits gives the underlying groups of the
module direct limits; the canonical comparisons have the stated fraction formulas.

The comparison maps are natural transformations into the constant section group,
so their naturality is transition compatibility (including every adjacent pair).
Their restrictions on every D(f), f in I, are specified using
`StructureSheaf.const`: the section with value numerator/denominator in every
prime localization. For the first comparison the numerator is phi(f^n) and the
denominator f^n. For the second it is any lift y of psi(f^n), with the same
denominator. Quantifying over all lifts records independence of the lift.
The basic opens cover D by hD, so these formulas uniquely determine the cocones
under the given stage identifications; they are not arbitrary existential maps.
The colimit desc maps have injectivity, bijectivity, and conditional bijectivity,
respectively, exactly as in the node. No data are chosen from an unproved theorem.

## Old

```lean
theorem sections_over_quasiCompactOpen_of_affine
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (I : Ideal A) (hIfg : I.FG)
    (D : (Spec (CommRingCat.of A)).Opens)
    (hD : ∀ (p : PrimeSpectrum A), p ∈ D ↔ ¬ ∀ a : A, a ∈ I → a ∈ p.asIdeal)
    (N : ℕ → Submodule A M)
    (hN : ∀ n x, x ∈ N n ↔ ∀ a : A, a ∈ I ^ n → a • x = 0) :
    ∃ c : (Σ n : ℕ,
      ((ModuleCat.of A (I ^ n : Ideal A)) ⟶ ModuleCat.of A M)) →
        Γ(tilde (ModuleCat.of A M), D),
      ∃ c' : (Σ n : ℕ,
        ((ModuleCat.of A (I ^ n : Ideal A)) ⟶ ModuleCat.of A (M ⧸ N n))) →
        Γ(tilde (ModuleCat.of A M), D),
      Function.Injective c ∧ Function.Bijective c' ∧
      ((∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) →
        Function.Bijective c)
```

## New

```lean
theorem sections_over_quasiCompactOpen_of_affine
    {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (I : Ideal A) (hIfg : I.FG)
    (D : (Spec (CommRingCat.of A)).Opens)
    (hD : ∀ (p : PrimeSpectrum A), p ∈ D ↔ ¬ ∀ a : A, a ∈ I → a ∈ p.asIdeal)
    (N : ℕ → Submodule A M)
    (hN : ∀ n x, x ∈ N n ↔ ∀ a : A, a ∈ I ^ n → a • x = 0) :
    ∃ (r : ∀ (n m : ℕ), n ≤ m →
        (ModuleCat.of A (I ^ m : Ideal A) ⟶ ModuleCat.of A (I ^ n : Ideal A)))
      (q : ∀ (n m : ℕ), n ≤ m →
        (ModuleCat.of A (M ⧸ N n) ⟶ ModuleCat.of A (M ⧸ N m)))
      (F G : ℕ ⥤ AddCommGrpCat.{u})
      (e : ∀ n, F.obj n ≅ AddCommGrpCat.of
        (ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A M))
      (e' : ∀ n, G.obj n ≅ AddCommGrpCat.of
        (ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A (M ⧸ N n)))
      (c : F ⟶ (Functor.const ℕ).obj
        (AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D)))
      (c' : G ⟶ (Functor.const ℕ).obj
        (AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D))),
      (∀ (n m : ℕ) (h : n ≤ m) (x : (I ^ m : Ideal A)),
        (r n m h x : A) = (x : A)) ∧
      (∀ (n m : ℕ) (h : n ≤ m) (x : M),
        q n m h ((N n).mkQ x) = (N m).mkQ x) ∧
      (∀ (n m : ℕ) (h : n ≤ m)
        (φ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A M),
        (e m).hom (F.map (homOfLE h) ((e n).inv φ)) = r n m h ≫ φ) ∧
      (∀ (n m : ℕ) (h : n ≤ m)
        (ψ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A (M ⧸ N n)),
        (e' m).hom (G.map (homOfLE h) ((e' n).inv ψ)) = r n m h ≫ ψ ≫ q n m h) ∧
      (∀ (f : A) (hf : f ∈ I), ∃ hle : PrimeSpectrum.basicOpen f ≤ D,
        (∀ (n : ℕ) (φ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A M),
          (tilde (R := CommRingCat.of A) (ModuleCat.of A M)).presheaf.map (homOfLE hle).op
              (c.app n ((e n).inv φ)) =
            StructureSheaf.const (R := A) (φ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩)
              (f ^ n) (PrimeSpectrum.basicOpen f)
              (fun p hp ↦ p.asIdeal.primeCompl.pow_mem hp n)) ∧
        (∀ (n : ℕ)
          (ψ : ModuleCat.of A (I ^ n : Ideal A) ⟶ ModuleCat.of A (M ⧸ N n))
          (y : M), (N n).mkQ y = ψ ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ →
          (tilde (R := CommRingCat.of A) (ModuleCat.of A M)).presheaf.map (homOfLE hle).op
              (c'.app n ((e' n).inv ψ)) =
            StructureSheaf.const (R := A) y (f ^ n) (PrimeSpectrum.basicOpen f)
              (fun p hp ↦ p.asIdeal.primeCompl.pow_mem hp n))) ∧
      Function.Injective (colimit.desc F
        ⟨AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D), c⟩) ∧
      Function.Bijective (colimit.desc G
        ⟨AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D), c'⟩) ∧
      ((∀ x : M, (∀ a : A, a ∈ I → a • x = 0) → x = 0) →
        Function.Bijective (colimit.desc F
          ⟨AddCommGrpCat.of Γ(tilde (R := CommRingCat.of A) (ModuleCat.of A M), D), c⟩))
```

Added public import: `Mathlib.Algebra.Category.Grp.Colimits`, needed for the
colimit objects in the corrected signature. Existing public imports retained.
The temporary private counterexample helpers from the returned sandbox were
removed; none existed in the repository's original module.

## Users

`tools/downstream.py Sheaf.Paper.SectionsOverQuasiCompactOpen --uses
AlgebraicGeometry.sections_over_quasiCompactOpen_of_affine` reports zero
downstream modules and only the defining module as a textual occurrence.
A repository-wide rg confirms that no other module applies the theorem.
There are no forced adaptations or changed target statements/definitions.
The global theorem `Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen`
describes this affine comparison in its docstring but does not import or apply
this declaration; its signature and proof are unaffected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionsOverQuasiCompactOpen | R3 | Corrected false comparison domains and specified canonical cocones; one theorem sorry remains. |

## Status

landed 20261013T060425-L-585165 2026-10-13 (merge of deliver/R3/Sheaf.Paper.SectionsOverQuasiCompactOpen)
