# AlgebraicGeometry.Proj.tilde_functorial

## Reason

The queue lists Sheaf.AlgebraicGeometry.ProjTildeFunctorial as a retirement item. Its proved theorem duplicates the existing source-library theorem, which has the same conclusion and drops three unused assumptions. Its only consumer imports it but never applies the declaration. Retire the Sheaf module and redirect the consumer and DAG attachment to the source. No source-library file changes.

## Old

The withdrawn Sheaf declaration:

```lean
theorem tilde_functorial
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (h𝓜 : ∀ i, DirectSum.IsInternal (𝓜 i))
    (hsmul : ∀ (i : Fin 3) (n : ℕ) (z : ℤ) (a : S) (y : M i),
      a ∈ 𝒜 n → y ∈ 𝓜 i z → a • y ∈ 𝓜 i (n + z))
    (F : Fin 3 → (Proj 𝒜).Modules)
    (alpha : ∀ (i : Fin 3) (f : S), ∀ (d : ℕ), 0 < d → f ∈ 𝒜 d →
      (F i).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        (Submonoid.powers f))
    (hscalar : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : HomogeneousLocalization.Away 𝒜 f) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf (awayToSection 𝒜 f r • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
          alpha i f d hd hf s)
    (hres : ∀ (i : Fin 3) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
      ∀ (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha i g b hb hg ((F i).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (mu : ∀ (i : Fin 3) (x : Proj 𝒜),
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i) →+
        LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl (M i))
    (hmu : ∀ (i : Fin 3) (x : Proj 𝒜), Function.Injective (mu i x) ∧
      Set.range (mu i x) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hgerm : ∀ (i : Fin 3) (x : Proj 𝒜) (f : S) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ 𝒜 d) (hx : x ∈ basicOpen 𝒜 f) (m : ℕ) (y : M i)
      (s : (F i).val.obj (op (basicOpen 𝒜 f)))
      (t : x.asHomogeneousIdeal.toIdeal.primeCompl),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      (t : S) = f ^ m →
      mu i x (TopCat.Presheaf.germ (F i).val.presheaf (basicOpen 𝒜 f) x hx s) = mk y t) :
    ∃ lift : ∀ (i j : Fin 3) (phi : M i →ₗ[S] M j),
      (∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z) → (F i ⟶ F j),
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (chi : F i ⟶ F j),
        (∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M i)
          (s : (F i).val.obj (op (basicOpen 𝒜 f))),
          alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha j f d hd hf (chi.val.app (op (basicOpen 𝒜 f)) s) =
            mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) ↔
          chi = lift i j phi hphi) ∧
      (∀ (i j k : Fin 3) (phi : M i →ₗ[S] M j) (psi : M j →ₗ[S] M k)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (hpsi : ∀ (z : ℤ) (y : M j), y ∈ 𝓜 j z → psi y ∈ 𝓜 k z),
        lift i k (psi.comp phi) (fun z y hy ↦ hpsi z (phi y) (hphi z y hy)) =
          lift i j phi hphi ≫ lift j k psi hpsi) ∧
      (∀ i : Fin 3, lift i i (LinearMap.id : M i →ₗ[S] M i) (fun _ _ hy ↦ hy) = 𝟙 (F i)) ∧
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (x : Proj 𝒜) (d : ℕ) (h : x.asHomogeneousIdeal.toIdeal.primeCompl)
        (y : M i), (h : S) ∈ 𝒜 d → y ∈ 𝓜 i d →
        ∀ s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i),
        mu i x s = mk y h →
        mu j x ((RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).map
          (lift i j phi hphi) s) = mk (phi y) h)
```

The consumer import was:

```lean
public import Sheaf.AlgebraicGeometry.ProjTildeFunctorial
```

## New

The existing, unchanged source-library declaration:

```lean
theorem tilde_functorial
    {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (M : Fin 3 → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]
    (𝓜 : ∀ i, ℤ → AddSubgroup (M i))
    (F : Fin 3 → (Proj 𝒜).Modules)
    (alpha : ∀ (i : Fin 3) (f : S), ∀ (d : ℕ), 0 < d → f ∈ 𝒜 d →
      (F i).val.obj (op (basicOpen 𝒜 f)) →+ LocalizedModule.Away f (M i))
    (halpha : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d),
      Function.Injective (alpha i f d hd hf) ∧
      Set.range (alpha i f d hd hf) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 i n : Set (M i)))
        (Submonoid.powers f))
    (hscalar : ∀ (i : Fin 3) (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d)
      (r : HomogeneousLocalization.Away 𝒜 f) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf (awayToSection 𝒜 f r • s) =
        algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) r •
          alpha i f d hd hf s)
    (hres : ∀ (i : Fin 3) (f g : S) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 b) (inc : basicOpen 𝒜 g ≤ basicOpen 𝒜 f)
      (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g ^ e = a * f →
      ∀ (m : ℕ) (y : M i) (s : (F i).val.obj (op (basicOpen 𝒜 f))),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha i g b hb hg ((F i).val.map (homOfLE inc).op s) =
        mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (mu : ∀ (i : Fin 3) (x : Proj 𝒜),
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i) →+
        LocalizedModule x.asHomogeneousIdeal.toIdeal.primeCompl (M i))
    (hgerm : ∀ (i : Fin 3) (x : Proj 𝒜) (f : S) (d : ℕ) (hd : 0 < d)
      (hf : f ∈ 𝒜 d) (hx : x ∈ basicOpen 𝒜 f) (m : ℕ) (y : M i)
      (s : (F i).val.obj (op (basicOpen 𝒜 f)))
      (t : x.asHomogeneousIdeal.toIdeal.primeCompl),
      alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      (t : S) = f ^ m →
      mu i x (TopCat.Presheaf.germ (F i).val.presheaf (basicOpen 𝒜 f) x hx s) = mk y t) :
    ∃ lift : ∀ (i j : Fin 3) (phi : M i →ₗ[S] M j),
      (∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z) → (F i ⟶ F j),
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (chi : F i ⟶ F j),
        (∀ (f : S) (d : ℕ) (hd : 0 < d) (hf : f ∈ 𝒜 d) (m : ℕ) (y : M i)
          (s : (F i).val.obj (op (basicOpen 𝒜 f))),
          alpha i f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha j f d hd hf (chi.val.app (op (basicOpen 𝒜 f)) s) =
            mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) ↔
          chi = lift i j phi hphi) ∧
      (∀ (i j k : Fin 3) (phi : M i →ₗ[S] M j) (psi : M j →ₗ[S] M k)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (hpsi : ∀ (z : ℤ) (y : M j), y ∈ 𝓜 j z → psi y ∈ 𝓜 k z),
        lift i k (psi.comp phi) (fun z y hy ↦ hpsi z (phi y) (hphi z y hy)) =
          lift i j phi hphi ≫ lift j k psi hpsi) ∧
      (∀ i : Fin 3, lift i i (LinearMap.id : M i →ₗ[S] M i) (fun _ _ hy ↦ hy) = 𝟙 (F i)) ∧
      (∀ (i j : Fin 3) (phi : M i →ₗ[S] M j)
        (hphi : ∀ (z : ℤ) (y : M i), y ∈ 𝓜 i z → phi y ∈ 𝓜 j z)
        (x : Proj 𝒜) (d : ℕ) (h : x.asHomogeneousIdeal.toIdeal.primeCompl)
        (y : M i), (h : S) ∈ 𝒜 d → y ∈ 𝓜 i d →
        ∀ s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj (F i),
        mu i x s = mk y h →
        mu j x ((RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).map
          (lift i j phi hphi) s) = mk (phi y) h)
```

Withdraw the Sheaf module using deleted.txt. The consumer now imports:

```lean
public import WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial
```

The original statement follows by `exact tilde_functorial 𝒜 M 𝓜 F alpha halpha hscalar hres mu hgerm` after importing the source module. The associated sheaves, localization constructions, chart formulas, uniqueness, composition, identity, and stalk formulas are unchanged. The source theorem is stronger only in that h𝓜, hsmul, and hmu are unnecessary. No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjTildeFunctorial | B5 | Retired duplicate; zero original holes. |
| Sheaf.AlgebraicGeometry.ProjSheafificationExact | unclaimed | Its sole public import is redirected; all declaration signatures and proofs remain verbatim. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProjTildeFunctorial --uses AlgebraicGeometry.Proj.tilde_functorial` listed this one downstream consumer and no application outside the withdrawn module. A full-library import search likewise found just this consumer. The source-library twin remains untouched. The unit realization record is unchanged.

## Status

landed 20261020T135350-L-1814193 2026-10-20 (merge of deliver/B5/Sheaf.AlgebraicGeometry.ProjTildeFunctorial)
