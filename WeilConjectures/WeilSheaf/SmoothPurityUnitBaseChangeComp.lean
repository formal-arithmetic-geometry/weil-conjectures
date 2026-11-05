/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The exceptional base change map at the unit and composition (A1', step 3)

For stacked squares `f : X ⟶ Y`, `g : Y ⟶ Z` over `k₁` with base changes `f'`, `g'` over `k₂`
and compact-support base change isomorphisms `bcf`, `bcg`, `bcfg` compatible with the composition
isomorphisms `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, the exceptional base change map at the unit of the
composite (`ProEtale.CondensedRing.smoothUnitBaseChange`) is the pasting of the mate of `bcf` at
`Rg^! ℚ̄_ℓ` and of `Rf'^!` applied to the exceptional base change map of `g`, through the
composition isomorphisms `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` (`smoothUnitBaseChange_comp`). Hence
invertibility passes from the factors to the composite (`isIso_smoothUnitBaseChange_comp`):
this is the pasting step of the local proof of `IsIso smoothUnitBaseChange` for a smooth
non-proper `f` (Zariski-locally `f = g ∘ j ∘ p` with `g` étale, `j` an open immersion and `p`
the projection of a projective space).

The generic statement is `CategoryTheory.Adjunction.unitBaseChange_comp`, a reformulation of
`CategoryTheory.Adjunction.mateEquiv_inv_comp` in terms of `unitBaseChange`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

section Generic

variable {Cx Cy Cz Cx' Cy' Cz' : Type*} [Category* Cx] [Category* Cy] [Category* Cz]
  [Category* Cx'] [Category* Cy'] [Category* Cz']
  {Lf : Cx ⥤ Cy} {Rf : Cy ⥤ Cx} (adjf : Lf ⊣ Rf) {Lg : Cy ⥤ Cz} {Rg : Cz ⥤ Cy} (adjg : Lg ⊣ Rg)
  {Lh : Cx ⥤ Cz} {Rh : Cz ⥤ Cx} (adjh : Lh ⊣ Rh)
  {Lf' : Cx' ⥤ Cy'} {Rf' : Cy' ⥤ Cx'} (adjf' : Lf' ⊣ Rf')
  {Lg' : Cy' ⥤ Cz'} {Rg' : Cz' ⥤ Cy'} (adjg' : Lg' ⊣ Rg')
  {Lh' : Cx' ⥤ Cz'} {Rh' : Cz' ⥤ Cx'} (adjh' : Lh' ⊣ Rh')
  {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'} {Gc : Cz ⥤ Cz'}
  (Exf : Lf ⋙ Gb ⟶ Ga ⋙ Lf') [IsIso Exf] (Exg : Lg ⋙ Gc ⟶ Gb ⋙ Lg') [IsIso Exg]
  (Exh : Lh ⋙ Gc ⟶ Ga ⋙ Lh') [IsIso Exh] (e : Lh ≅ Lf ⋙ Lg) (e' : Lh' ≅ Lf' ⋙ Lg')
  (hEx : ExchangeCompCompatible Exf Exg Exh e e')
  (ρ : Rh ≅ Rg ⋙ Rf)
  (hρ : ∀ K : Cz, Lg.map (Lf.map (ρ.hom.app K)) ≫ Lg.map (adjf.counit.app _) ≫
    adjg.counit.app K = e.inv.app _ ≫ adjh.counit.app K)
  (ρ' : Rh' ≅ Rg' ⋙ Rf')
  (hρ' : ∀ K : Cz', Lg'.map (Lf'.map (ρ'.hom.app K)) ≫ Lg'.map (adjf'.counit.app _) ≫
    adjg'.counit.app K = e'.inv.app _ ≫ adjh'.counit.app K)
  {U : Cz} {U' : Cz'} (ε : Gc.obj U ⟶ U')

end Generic

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The counit compatibility of the composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` -/

section CompCounit

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (f : X ⟶ Y) (g : Y ⟶ Z)

end CompCounit

/-! ### Pasting of exceptional base change maps at the unit -/

section Paste

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y Z : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {X' Y' Z' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left} {πZ : Z'.left ⟶ Z.left}
  (bcf : boundedConstructibleLowerShriek l f ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f')
  (bcg : boundedConstructibleLowerShriek l g ⋙ boundedConstructibleUpperStarOfMap l πZ ≅
    boundedConstructibleUpperStarOfMap l πY ⋙ boundedConstructibleLowerShriek l g')
  (bcfg : boundedConstructibleLowerShriek l (f ≫ g) ⋙ boundedConstructibleUpperStarOfMap l πZ ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l (f' ≫ g'))
  (hbc : Adjunction.ExchangeCompCompatible bcf.hom bcg.hom bcfg.hom
    (boundedConstructibleLowerShriekComp_padicAlgCl l f g)
    (boundedConstructibleLowerShriekComp_padicAlgCl l f' g'))
  (e : (boundedConstructibleUpperStarOfMap l πZ).obj (𝟙_ _) ⟶ 𝟙_ _)

end Paste

end AlgebraicGeometry.ProEtale.CondensedRing
