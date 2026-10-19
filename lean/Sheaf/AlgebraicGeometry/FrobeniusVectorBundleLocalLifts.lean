/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalCoordinates
import Sheaf.AlgebraicGeometry.FrobeniusPolynomialSolutions

/-! # Local Frobenius equations on finite locally free modules -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

/-- Sections of F - 1 admit lifts on an étale covering.

Source: Stacks Project, More on Étale Cohomology, Tag 0GKU,
label lemma-frobenius-linear-on-vb, surjectivity paragraph; Tag 0A3L.
(blueprint: lem-weil-pbc-frobenius-vector-bundle-local-lifts)

Proof: Refine the source of a section by affine open subsets on which the pulled-back
finite locally free module is free, of a finite rank which may depend on the subset.
Using the pulled-back basis, write F(x)_i = sum_j c_ij x_j^p; naturality identifies
these coefficients on every further étale restriction. For target coordinates b_i,
adjoin x_i with equations b_i + x_i - sum_j c_ij x_j^p = 0. The Jacobian matrix is
the identity in characteristic p, hence this square presentation is étale. At any
geometric point, Lang's theorem for the resulting semilinear map on the finite
coordinate vector space over the algebraically closed residue field supplies a
solution. Thus the solution scheme surjects onto the affine source and is an étale
cover. Its universal coordinates give the requested lift. Compose these covers with
the affine trivializing cover of the original source. Their image sieve is covering,
which is precisely local surjectivity. All calculations pass through the sectionwise
ULift bijection. Rank zero uses the identity cover; empty objects use the empty cover. -/
theorem frobenius_vectorBundle_local_lifts
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    Sheaf.IsLocallySurjective (F - 𝟙 _) := by
  classical
  have hcoords := frobenius_vectorBundle_local_coordinates p S E F hF
  clear hF
  generalize (sheafCompose S.smallEtaleTopology
    AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (Modules.etaleTensorSectionsSheaf E) = G at F hcoords ⊢
  refine ⟨fun {U} s ↦ (Scheme.mem_smallEtaleTopology_iff _).2 fun x ↦ ?_⟩
  obtain ⟨A, hA, hxA, n, c, e, hp, hnat, heq⟩ :=
    hcoords U x
  have : IsAffine A.toScheme := hA
  let L := Etale.localizationRestriction AddCommGrpCat.{u + 1}
    (A.ι ≫ U.hom) inferInstance
  let VA' : A.toScheme.Etale := Etale.mk (𝟙 A.toScheme)
  let sA : (L.obj G).obj.obj (op VA') :=
    G.obj.map (MorphismProperty.Over.homMk A.ι (by
      change A.ι ≫ U.hom = (𝟙 A.toScheme) ≫ A.ι ≫ U.hom
      simp) trivial :
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale (A.ι ≫ U.hom))).obj VA' ⟶ U).op s
  let b := e VA' sA
  obtain ⟨P, π, y, hP, hπ, hsπ, hy, -⟩ :=
    frobenius_polynomial_solution_cover A.toScheme p hp n c b
  have : Etale π := hπ
  have : Surjective π := hsπ
  let VP' : A.toScheme.Etale := Etale.mk π
  let k' : VP' ⟶ VA' := MorphismProperty.Over.homMk π (by
    change π ≫ 𝟙 A.toScheme = π
    simp) trivial
  let VP : S.Etale :=
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale (A.ι ≫ U.hom))).obj VP'
  let k : VP ⟶ U := MorphismProperty.Over.homMk (π ≫ A.ι) (by simp [VP, VP', Etale.mk]) trivial
  let t := (e VP').symm y
  obtain ⟨z, hz⟩ := hsπ.1 (⟨x, hxA⟩ : A.toScheme)
  refine ⟨VP, k, ⟨t, ?_⟩, z, ?_⟩
  · apply (e VP').injective
    change e VP' ((L.map F).hom.app (op VP') t - t) = _
    ext i
    rw [map_sub, Pi.sub_apply, heq, AddEquiv.apply_symm_apply]
    calc
      _ = π.appTop (b i) := by convert hy i using 1; rfl
      _ = e VP' (G.obj.map k.op s) i := by
        have hres : G.obj.map k.op s = (L.obj G).obj.map k'.op sA := by
          change _ = G.obj.map _ (G.obj.map _ s)
          rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
          rfl
        rw [hres, hnat]
        rfl
  · change A.ι (π z) = x
    rw [hz]
    rfl

end AlgebraicGeometry.Scheme
