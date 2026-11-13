/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisGlobalExtComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtTransport
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
/-! # Free abelian sheaves for a two-open cover

Source: Stacks Project, Tag 01EB.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
/-- Compatible Ext presentations for a single cohomology term.
Source: Stacks Project, Tag 01EB and Section 01F7. -/
theorem H.openFreeExtComparison (f : X ⟶ Spec (.of R)) (M : X.Modules) (W : X.Opens) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
    let G := invImage (baseChangeFst (S := S) f)
    let N := (SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
      (baseChangedModule (S := S) f M)
    let φ := coeff (baseChangeFst (S := S) f) (baseChangeUnit (S := S) f M)
    let ρ := (scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let τ := (scalarRep (baseChangedModule (S := S) f M)).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    ∃ (e : ∀ n, HOver (W.ι ≫ f) ((pullback W.ι).obj M) n ≃+ Ext (H.openFreeSheaf W) F n)
      (e' : ∀ n, HOver (baseChangeSnd (S := S) (W.ι ≫ f))
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M)) n ≃+
        Ext (G.obj (H.openFreeSheaf W)) N n),
      (∀ n a x, e n (a • x) = (e n x).comp (Ext.mk₀ (ρ a).asHom) (add_zero n)) ∧
      (∀ n a x, e' n (a • x) = (e' n x).comp (Ext.mk₀ (τ a).asHom) (add_zero n)) ∧
      (∀ n x, e' n (H.baseChangeLinear (S := S) (W.ι ≫ f) ((pullback W.ι).obj M) n x) =
        ((e n x).mapExactFunctor G).comp (Ext.mk₀ φ) (add_zero n)) := by
  obtain ⟨e, e', he, he', hb⟩ :=
    H.globalFreeExtComparison (S := S) (W.ι ≫ f) ((pullback W.ι).obj M)
  obtain ⟨t, t', ht, ht', htb⟩ := H.openFreeExtTransport (S := S) f M W
  refine ⟨fun n ↦ (e n).trans (t n), fun n ↦ (e' n).trans (t' n), ?_, ?_, ?_⟩
  · intro n a x
    change t n (e n (a • x)) = _
    rw [he, ht]
    rfl
  · intro n a x
    change t' n (e' n (a • x)) = _
    rw [he', ht']
    rfl
  · intro n x
    change t' n (e' n (H.baseChangeLinear (S := S) (W.ι ≫ f)
      ((pullback W.ι).obj M) n x)) = _
    rw [hb, htb]
    rfl

end AlgebraicGeometry.Scheme.Modules
