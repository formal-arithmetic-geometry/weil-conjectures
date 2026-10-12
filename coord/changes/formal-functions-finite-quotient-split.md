# formalFunctions_finite_quotient_comparison

## Reason

Decompose the finite-level comparison into its canonical quotient/pullback factorization
and its germ-compatibility argument. The first worker's universal assertion for arbitrary
isomorphisms was false: for f=id on Spec Q, F=O and p=0, negation is a system
isomorphism, but it sends the germ of 1 to -1 rather than its pullback 1. The repaired
isomorphism lemma specifies the canonical pullback, and the maps lemma uses this formula.

## Old

The existing theorem's signature is preserved verbatim:

```lean
theorem formalFunctions_finite_quotient_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) : let X' := pullback (Y.fromSpecStalk y) f let f' := pullback.fst (Y.fromSpecStalk y) f let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F let J := (Scheme.IdealSheafData.ofIdealTop ((maximalIdeal (Y.presheaf.stalk y)).map (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f' let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙ ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom ∃ b : formalCompletionSystem J F' ⋙ C ≅ formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars (algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))), ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y] formalFibreCohomologyLocal f y F p n, (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p), r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧ ∀ a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y] formalFunctionsLocalCohomology f y F p, IsFormalFunctionsLocalComparison f y F p a → ∀ n : ℕ, IsFormalFunctionsTheta f y F p n ((r n).comp a)
```

The new declarations below did not exist in the repository.

## New

The existing theorem has exactly the signature above. Its proof obtains the canonical
isomorphism and maps, and applies germ compatibility at each level. New declarations:

```lean
def formalFunctionsFiniteι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) : formalFibre f y n ⟶ pullback (Y.fromSpecStalk y) f

theorem formalFunctionsFiniteι_snd {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) : formalFunctionsFiniteι f y n ≫ pullback.snd (Y.fromSpecStalk y) f = formalFibreι f y n

def formalFunctionsFiniteFMap {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (n : ℕ) : (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F ⟶ (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)

def formalFunctionsFinitePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p n : ℕ) : formalFunctionsLocalCohomology f y F p →+ formalFibreCohomologyLocal f y F p n

theorem formalFunctions_finite_quotient_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p : ℕ) : let X' := pullback (Y.fromSpecStalk y) f let f' := pullback.fst (Y.fromSpecStalk y) f let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F let J := (Scheme.IdealSheafData.ofIdealTop ((maximalIdeal (Y.presheaf.stalk y)).map (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap f' let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙ ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫ f'.appTop).hom ∃ b : formalCompletionSystem J F' ⋙ C ≅ formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars (algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))), ∃ r : ∀ n : ℕ, formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y] formalFibreCohomologyLocal f y F p n, (∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p), r n z = (b.hom.app (op n)) ((C.map (formalModuleQuotientπ J (n + 1) F')) z)) ∧ ∀ (n : ℕ) (z : formalFunctionsLocalCohomology f y F p), r n z = formalFunctionsFinitePullback f y F p n z

theorem formalFunctions_finite_quotient_maps {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p n : ℕ) (r : formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y] formalFibreCohomologyLocal f y F p n) (hr : ∀ z, r z = formalFunctionsFinitePullback f y F p n z) (a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y] formalFunctionsLocalCohomology f y F p) (ha : IsFormalFunctionsLocalComparison f y F p a) : IsFormalFunctionsTheta f y F p n (r.comp a)
```

The construction uses explicit pullback.lift and the canonical tensor adjunction pinned
by the unit formula of exists_tensorPullbackAdjunction. Its chosen adjunction has a fixed
unit, hence a fixed Hom equivalence. No arbitrary witness of mere existence is selected.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback | P3 (new) | real construction; no holes |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso | P3 (new) | canonical pullback in its conclusion |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps | P3 (new) | assumes the canonical pullback formula |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientComparison | P3 | proof-only imports and composition; existing signature unchanged |
| Sheaf.AlgebraicGeometry.FormalFunctionsLocalDictionary | unclaimed/not adapted | existing consumer retains the identical theorem statement |

No existing definition or target meaning changes. No adaptations are delivered.

## Status

landed 20261012T184330-L-4014502 2026-10-12 (merge of deliver/P3/Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientComparison)
