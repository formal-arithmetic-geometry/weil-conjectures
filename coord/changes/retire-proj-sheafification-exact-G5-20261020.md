# AlgebraicGeometry.Proj.proj_sheafification_shortExact

## Reason

Retire the unused Sheaf duplicate listed in `coord/retire-items.tsv`. The adopted
upstream module `WeilConjectures.AlgebraicGeometry.ProjSheafificationExact` already
contains a complete declaration with the same exactness conclusion and all data used
by the node. The upstream declaration omits only the old copy's unused hypotheses
`hscalar` and `hres`; a direct application to the old signature was compiled in the
attachment check. The shared source scan reports zero downstream importers and zero
textual users of the Sheaf declaration, so no consumer adaptation is needed.

## Old

The withdrawn `lean/Sheaf/AlgebraicGeometry/ProjSheafificationExact.lean` declared:

```lean
theorem proj_sheafification_shortExact
    (k : Type u) [Field k]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (MvPolynomial (Fin 2) k) (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (h𝓜 : ∀ i, DirectSum.IsInternal (𝓜 i))
    (hsmul : ∀ (i : Fin 3) (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M i),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 i z → a • y ∈ 𝓜 i (n + z))
    (F : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k), ∀ (d : ℕ), 0 < d →
      f ∈ homogeneousSubmodule (Fin 2) k d →
      (F i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 i n : Set (M i))) (Submonoid.powers f))
    (hscalar : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
      (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
      (s : (F i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha i f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
        algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
          (Localization.Away f) r • alpha i f d hd hf s)
    (hres : ∀ (i : Fin 3) (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
      (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
        basicOpen (homogeneousSubmodule (Fin 2) k) f)
      (e c : ℕ) (a : MvPolynomial (Fin 2) k),
      0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
      ∀ (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha i g b hb hg ((F i).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (phi : M 0 →ₗ[MvPolynomial (Fin 2) k] M 1)
    (psi : M 1 →ₗ[MvPolynomial (Fin 2) k] M 2)
    (hphi : ∀ (z : ℤ) (y : M 0), y ∈ 𝓜 0 z → phi y ∈ 𝓜 1 z)
    (hpsi : ∀ (z : ℤ) (y : M 1), y ∈ 𝓜 1 z → psi y ∈ 𝓜 2 z)
    (hinj : Function.Injective phi) (hexact : Function.Exact phi psi)
    (hsurj : Function.Surjective psi)
    (i : F 0 ⟶ F 1) (q : F 1 ⟶ F 2)
    (hi : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M 0)
      (s : (F 0).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha 0 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 1 f d hd hf (i.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))
    (hq : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M 1)
      (s : (F 1).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha 1 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 2 f d hd hf (q.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
        mk (psi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/ProjSheafificationExact.lean` using
`deleted.txt`. Attach node `lem-sc-p1-proj-sheafification-exact` to the existing
upstream declaration:

```lean
theorem proj_sheafification_shortExact
    (k : Type u) [Field k]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (MvPolynomial (Fin 2) k) (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (h𝓜 : ∀ i, DirectSum.IsInternal (𝓜 i))
    (hsmul : ∀ (i : Fin 3) (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M i),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 i z → a • y ∈ 𝓜 i (n + z))
    (F : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k), ∀ (d : ℕ), 0 < d →
      f ∈ homogeneousSubmodule (Fin 2) k d →
      (F i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 i n : Set (M i))) (Submonoid.powers f))
    (phi : M 0 →ₗ[MvPolynomial (Fin 2) k] M 1)
    (psi : M 1 →ₗ[MvPolynomial (Fin 2) k] M 2)
    (hphi : ∀ (z : ℤ) (y : M 0), y ∈ 𝓜 0 z → phi y ∈ 𝓜 1 z)
    (hpsi : ∀ (z : ℤ) (y : M 1), y ∈ 𝓜 1 z → psi y ∈ 𝓜 2 z)
    (hinj : Function.Injective phi) (hexact : Function.Exact phi psi)
    (hsurj : Function.Surjective psi)
    (i : F 0 ⟶ F 1) (q : F 1 ⟶ F 2)
    (hi : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M 0)
      (s : (F 0).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha 0 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 1 f d hd hf (i.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
        mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))
    (hq : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) (y : M 1)
      (s : (F 1).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha 1 f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 2 f d hd hf (q.val.app (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) =
        mk (psi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact
```

The old node statement is unchanged. Its additional `hscalar` and `hres` hypotheses
are simply ignored when applying the more general upstream theorem, preserving the
old existential zero-composite and `ShortExact` conclusion. No compatibility module is
needed because the copy has no importers.

## Users

`tools/downstream.py` and a repository-wide import scan find no downstream modules
using the Sheaf copy or its declaration. The retirement row's historical consumers have
already been retired or use the upstream module directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjSheafificationExact | G5 | Withdrawn unused duplicate. |
| WeilConjectures.AlgebraicGeometry.ProjSheafificationExact | unmodified | Existing adopted declaration retained. |

## Status

landed 20261020T155200-L-3205928 2026-10-20 (merge of deliver/G5/Sheaf.AlgebraicGeometry.ProjSheafificationExact)
