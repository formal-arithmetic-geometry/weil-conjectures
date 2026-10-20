## What changed

The queue marks `Sheaf.AlgebraicGeometry.ProjSheafificationExact` as a retirement
item, and its theorem already has zero `sorry`s. I withdrew the unused Sheaf module
with `deleted.txt` and updated node `lem-sc-p1-proj-sheafification-exact` to attach its
statement to the complete adopted upstream declaration
`WeilConjectures.AlgebraicGeometry.ProjSheafificationExact`.

The old node statement is unchanged. The upstream theorem has the same conclusion and
all required data, while omitting only the old copy's unused `hscalar` and `hres`
hypotheses.

Change record: `coord/changes/retire-proj-sheafification-exact-G5-20261020.md`.

A scratch attachment theorem applying the upstream result to the old full
signature compiles cleanly; its axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. No consumer needs adaptation.

The complete attachment verification below was compiled through `lcompile.py` in
2.2 seconds without warnings. Both axiom probes report exactly
`[propext, Classical.choice, Quot.sound]`. This code is a scratch verification recorded
for review, and is not a new library module or declaration.

```lean
module

public import WeilConjectures.AlgebraicGeometry.ProjSheafificationExact

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem old_check
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
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  have _ := hscalar
  have _ := hres
  exact AlgebraicGeometry.Proj.proj_sheafification_shortExact k M 𝓜 h𝓜 hsmul F alpha halpha
    phi psi hphi hpsi hinj hexact hsurj i q hi hq

end AlgebraicGeometry.Proj

#print axioms AlgebraicGeometry.Proj.old_check
#print axioms AlgebraicGeometry.Proj.proj_sheafification_shortExact
```

## Proved and sorry left

The retirement item started with zero `sorry`s, so holes closed: 0; holes added: 0;
split off: 0. The withdrawn module contains no declarations. The upstream declaration
is already complete and remains unchanged. The attachment check proves the old
statement from it without adding a theorem or an assumption.

## No longer needed

Withdrawn module: `lean/Sheaf/AlgebraicGeometry/ProjSheafificationExact.lean`.

The retired copy's six imports disappear with it:

- `WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial`
- `Mathlib.RingTheory.MvPolynomial.Homogeneous`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.Algebra.Module.ProjAwayDegreeZeroExact`
- `WeilConjectures.AlgebraicGeometry.Modules.BasisExactness`
- `WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`

The adopted upstream theorem retains the same chart-exactness and basis argument.
Its imports, declarations and proof are unchanged; all node proof dependencies,
statement dependencies and tool approvals are retained. No dependency module is
claimed globally unnecessary. The unit `sk-thm-picard-duality` and every parent node
continue to use the same mathematical statement through its upstream attachment.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an item containing a `sorry`, but the current queue entry is
explicitly `retire` and the module was already proved in the earlier W2 landing. The
retirement metadata records the upstream twin as a duplicate with zero consumers. The
upstream signature is slightly more general because it omits two unused compatibility
hypotheses, so applying it discharges the old statement exactly; no weaker statement is
introduced and no target statement changes.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
