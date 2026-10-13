/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.CategoryTheory.Limits.Final
import Sheaf.RingTheory.LimitModuleEssentiallyFinitePresentationOverSystem

/-! # Tower descent over a prescribed local-ring system
Source: Stacks Project, Algebra, proof of Tag 00R7, using Tags 00QV and 00QX.
(blueprint: lem-weil-pbc-limit-tower-over-local-system)
-/

@[expose] public section

universe u v p q

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace WeilConjectures

/-- Descend the two upper rings and a module over a supplied base-ring system and a supplied
presentation of the top ring over the middle ring. The base diagram and its cocone are
restricted along a final functor, rather than constructed afresh. Finite generation is
omitted because it follows from the displayed cokernel presentation.

Source: Stacks Project, Algebra, proof of Tag 00R7, first paragraph, using the constructions
of Tags 00QV and 00QX (blueprint: lem-weil-pbc-limit-tower-over-local-system).

Proof: Apply `RingHom.exists_limit_module_essentially_finite_presentation_over_system` to
`F`, its supplied colimit cocone, the presentation of `S` over `R`, and the zero module
(with the empty matrix). This yields a tail of `I`, a local middle-ring diagram, its
colimit cocone to `S`, and compatible local structure maps. Make the latter into a natural
transformation using their transition compatibility. Apply the same theorem to this
middle-ring diagram, the supplied presentation of `S'` over `S`, and the given matrix
presentation of `M`. It yields a further tail with the top-ring and module diagrams,
their colimit cocones, compatible local structure maps, semilinearity, the descended
matrix presentations, and the transition and limit tensor comparison maps. Restrict the
base and middle diagrams to this final tail. The composite of the two tail inclusions is
final: directedness gives a common upper bound above any index and either cutoff, and
above any two such bounds. Finality preserves the base and middle colimit cocones. The
remaining ring and module assertions are exactly the clauses of the two applications,
restricted to the final tail; the formula for the restricted base cocone is explicit below.

For the independent module universe `v`, first apply the module descent theorem to
`ULift M` in universe `max u v`, transporting its module structure and matrix presentation.
Every stage ring is essentially of finite type over the integers, by composition of the
three essential finite type structure maps. Such a ring is countable: a finite polynomial
algebra over the integers is countable, and quotients and localizations of countable rings
are countable. Each descended module is a quotient of a finite power of a countable stage
ring, hence countable. Replace it by its `Shrink` in universe `v` and transport its group
and module structures and all maps along the resulting equivalences. Compose the maps at
the limit with `ULift.down`. Objectwise equivalences preserve the colimit universal
property, semilinearity, cokernel equivalences and tensor comparison equivalences. This
produces the asserted module diagram in universe `v`, including when `s` or `t` is zero.
-/
theorem limit_tower_over_local_system
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u})
    (π₀ : F ⟶ (Functor.const I).obj (CommRingCat.of R))
    (hFlocal : ∀ i, IsLocalRing (F.obj i))
    (hFmap : ∀ (i j : I) (h : i ≤ j), IsLocalHom (F.map (homOfLE h)).hom)
    (hπlocal : ∀ i, IsLocalHom (π₀.app i).hom)
    (hcolim : Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π₀)))
    (hFfinite : ∀ i, Algebra.EssFiniteType ℤ (F.obj i))
    (α : R →+* S) (β : S →+* S') [IsLocalHom α] [IsLocalHom β]
    (B : Type p) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (W : Submonoid B) (f : B →+* S) (hf : f.comp (algebraMap R B) = α)
    (hS : letI := f.toAlgebra; IsLocalization W S)
    (Q : Type q) [CommRing Q] [Algebra S Q] [Algebra.FinitePresentation S Q]
    (V : Submonoid Q) (g : Q →+* S') (hg : g.comp (algebraMap S Q) = β)
    (hS' : letI := g.toAlgebra; IsLocalization V S')
    (M : Type v) [AddCommGroup M] [Module S' M]
    (s t : ℕ) (H : (Fin s → S') →ₗ[S'] (Fin t → S'))
    (hM : Nonempty (((Fin t → S') ⧸ LinearMap.range H) ≃ₗ[S'] M)) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : Nonempty Λ) (_ : IsDirected Λ (· ≤ ·))
      (J : Λ ⥤ I), J.Final ∧
      let A := J ⋙ F
      let π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R) :=
        { app := fun i ↦ π₀.app (J.obj i)
          naturality := fun _ _ h ↦ π₀.naturality (J.map h) }
      ∃ (Bs C : Λ ⥤ CommRingCat.{u}) (ρ : A ⟶ Bs) (σ : Bs ⟶ C)
      (κ : Bs ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (κ' : C ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
      (_ : ∀ i : Λ, Module (C.obj i) (D.obj i)),
      -- local rings and local homomorphisms
      (∀ i, IsLocalRing (A.obj i)) ∧ (∀ i, IsLocalRing (Bs.obj i)) ∧
      (∀ i, IsLocalRing (C.obj i)) ∧
      (∀ i, IsLocalHom (ρ.app i).hom) ∧ (∀ i, IsLocalHom (σ.app i).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (A.map (homOfLE h)).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (Bs.map (homOfLE h)).hom) ∧
      (∀ (i j : Λ) (h : i ≤ j), IsLocalHom (C.map (homOfLE h)).hom) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i))) ∧
      (∀ i, IsLocalHom (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i))) ∧
      -- the maps to `R, S, S'` commute with `α, β`
      (∀ i, ρ.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom α) ∧
      (∀ i, σ.app i ≫ κ'.app i = κ.app i ≫ CommRingCat.ofHom β) ∧
      -- semilinearity of the module maps
      (∀ (i j : Λ) (h : i ≤ j) (y : C.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (C.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : C.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      -- (1) the colimits
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ')) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      -- (2) essential finite type
      (∀ i, (algebraMap ℤ (A.obj i)).EssFiniteType) ∧
      (∀ i, (ρ.app i).hom.EssFiniteType) ∧
      (∀ i, (σ.app i).hom.EssFiniteType) ∧
      -- (3) finite generation, indeed cokernels of `t × s` matrices
      (∀ i, ∃ H₀ : (Fin s → C.obj i) →ₗ[C.obj i] (Fin t → C.obj i),
        Nonempty (((Fin t → C.obj i) ⧸ LinearMap.range H₀) ≃ₗ[C.obj i] D.obj i)) ∧
      -- (4) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (ρ.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ φ : Bs.obj i ⊗[A.obj i] A.obj j →+* Bs.obj j,
          (∀ (x : Bs.obj i) (y : A.obj j),
            φ (x ⊗ₜ[A.obj i] y) = (Bs.map (homOfLE h)).hom x * (ρ.app j).hom y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] A.obj j), IsLocalization U (Bs.obj j))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (σ.app i).hom.toAlgebra
        letI := (Bs.map (homOfLE h)).hom.toAlgebra
        ∃ φ : C.obj i ⊗[Bs.obj i] Bs.obj j →+* C.obj j,
          (∀ (x : C.obj i) (y : Bs.obj j),
            φ (x ⊗ₜ[Bs.obj i] y) = (C.map (homOfLE h)).hom x * (σ.app j).hom y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] Bs.obj j), IsLocalization U (C.obj j))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (C.map (homOfLE h)).hom.toAlgebra
        ∃ e : C.obj j ⊗[C.obj i] D.obj i ≃ₗ[C.obj j] D.obj j,
          ∀ (y : C.obj j) (x : D.obj i),
            e (y ⊗ₜ[C.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (5) base changes to the limit
      (∀ i,
        letI := (ρ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ φ : Bs.obj i ⊗[A.obj i] R →+* S,
          (∀ (x : Bs.obj i) (y : R),
            φ (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * α y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (Bs.obj i ⊗[A.obj i] R), IsLocalization U S)) ∧
      (∀ i,
        letI := (σ.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ φ : C.obj i ⊗[Bs.obj i] S →+* S',
          (∀ (x : C.obj i) (y : S),
            φ (x ⊗ₜ[Bs.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)) x * β y) ∧
          (letI := φ.toAlgebra
           ∃ U : Submonoid (C.obj i ⊗[Bs.obj i] S), IsLocalization U S')) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ'.app i)).toAlgebra
        ∃ e : S' ⊗[C.obj i] D.obj i ≃ₗ[S'] M,
          ∀ (y : S') (x : D.obj i),
            e (y ⊗ₜ[C.obj i] x) =
              y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) := by
  sorry

end WeilConjectures
