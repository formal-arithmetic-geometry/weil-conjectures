/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact

/-!
# Exact products for pro-etale module objects

Source: blueprint `det-sf-open-closed-extension-zero-limits`, proof (2), and
`det-pe-products-derived`; Bhatt--Scholze, Proposition 3.1.10
(blueprint: lem-sf-proetale-module-object-products-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Exact small products for modules over an arbitrary monoid in abelian pro-etale sheaves.
Source: blueprint proof (2) of `det-sf-open-closed-extension-zero-limits`, applying
`det-pe-products-derived` to the module-object presentation of coefficients
(blueprint: lem-sf-proetale-module-object-products-exact).

Proof: Modules over the tensor unit in abelian sheaves are equivalent to abelian
sheaves: the unit axiom forces every action to be the left unitor, so every underlying
map is linear, and a free module over the unit realizes every sheaf. Use the existing
section-module equivalence for this commutative unit to identify these modules with
sectionwise modules over its reconstructed ring sheaf. The existing exact-products
theorem applies to that ring. Transport exactness through the composite equivalence
to abelian sheaves. Finally the exact conservative module-object forgetful functor
preserves products and reflects finite colimits, so exactness pulls back to modules
over arbitrary B. This includes the empty index set and zero ring; no commutativity
of B is used. -/
theorem proEtale_moduleObject_products_exact (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (I : Type (u + 1)) :
    HasExactLimitsOfShape (Discrete I)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B) := by
  classical
  let A := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let T := (𝟙_ A)
  have ha (M : Mod A T) : @Mod.act A _ _ T _ M.X M.mod = (λ_ M.X).hom := by
    have h := @Mod.one_act A _ _ T _ M.X M.mod
    change (𝟙 T) ▷ M.X ≫ @Mod.act A _ _ T _ M.X M.mod = (λ_ M.X).hom at h
    simpa only [id_whiskerRight, Category.id_comp] using h
  let Q : Mod A T ⥤ A := Mod.forget T
  let ff : Q.FullyFaithful :=
    { preimage := fun {M N} f ↦ by
        change M.X ⟶ N.X at f
        exact Mod.homMk (M := M) (N := N) f (by
          exact (congrArg (fun k ↦ k ≫ f) (ha M)).trans
            ((leftUnitor_naturality f).symm.trans
              (congrArg (fun k ↦ T ◁ f ≫ k) (ha N).symm)))
      map_preimage := fun _ ↦ rfl
      preimage_map := fun _ ↦ rfl }
  let : Q.Full := ff.full
  let : Q.Faithful := ff.faithful
  let : Q.EssSurj := ⟨fun M ↦ ⟨(Mod.free T).obj M, ⟨λ_ M⟩⟩⟩
  let : Q.IsEquivalence := {}
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) T
  let R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) T)
  let := Scheme.ProEt.products_exact.{u, 0, u + 1} X R I
  let := HasExactLimitsOfShape.of_codomain_equivalence (Discrete I)
    (E.symm.trans Q.asEquivalence)
  exact HasExactLimitsOfShape.domain_of_functor (Discrete I) (Mod.forget B)

end AlgebraicGeometry.ProEtale
