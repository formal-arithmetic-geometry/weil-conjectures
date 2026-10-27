/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ChartLogSmoothDeformationCalculus
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# Normalized étale differential and tensor-pullback presentations

Source: the symbol presentation in lem-per-strict-log-differentials-pushout;
ILO VI 1.1 (log conventions), X 1.2 and XVI 3.6.3 (strict comparison).
(blueprint: def-per-etale-differential-pullback-presentation).

These are representing pairs, including their universal properties, rather than
choices of objects from existence alone. The strict-pushout theorem asserts their
existence; logarithmic differentials use the existing `differentialSheaf`.
A representing pair is unique up to its unique symbol-preserving isomorphism.
Ordinary differentials retain the existing tensor sections of `relativeDifferentials`.
The pullback presentation is the adjoint description of tensor inverse image; its
unit is specified on every relative étale diagram.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Module sheaves over the existing small-étale structure ring.
Source: ILO VI 1.1; Stacks 03DA
(blueprint: def-per-etale-differential-pullback-presentation). -/
abbrev DifferentialEtaleModules (X : Scheme.{u}) :=
  ringedSiteModules.{u} (X.logDifferentialStructureRing)

/-- An ordinary differential sheaf with its universal derivation. The comparison fixes
its underlying additive presheaf to the recorded tensor sections of the recorded
Zariski differential sheaf. The universal derivation determines the pair up to its
unique generator-preserving isomorphism; no replacement Kähler module is constructed.
Source: Stacks 01UM, 03DR and 03DU
(blueprint: def-per-etale-differential-pullback-presentation). -/
structure EtaleOrdinaryDifferentialPresentation {X S : Scheme.{u}} (f : X ⟶ S) where
  module : DifferentialEtaleModules X
  tensorSections : module.val.presheaf ≅
    Scheme.Modules.etaleTensorSectionsPresheaf f.relativeDifferentials
  derivation : module.val.Derivation (Scheme.etaleStructurePresheafToPullback f)
  universal : ∀ (T : DifferentialEtaleModules X)
    (D : T.val.Derivation (Scheme.etaleStructurePresheafToPullback f)),
    ∃! h : module ⟶ T, ∀ (U : X.Etale) (a : Γ(U.left, ⊤)),
      h.val.app (op U) (derivation.d (X := op U) a) = D.d (X := op U) a

/-- The adjoint presentation of a map `c⁻¹E → F`, semilinear over `c` on every
relative étale diagram. Both source and target restrictions are required.
Source: Stacks 03D2--03D3 and ILO VI 1.1
(blueprint: def-per-etale-differential-pullback-presentation). -/
structure EtaleDifferentialModuleMap {Z W : Scheme.{u}} (c : Z ⟶ W)
    (E : DifferentialEtaleModules W) (F : DifferentialEtaleModules Z) where
  app : ∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
    (_hk : k ≫ U.hom = V.hom ≫ c), E.val.obj (op U) →+ F.val.obj (op V)
  smul : ∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
    (hk : k ≫ U.hom = V.hom ≫ c) (a : Γ(U.left, ⊤)) (x : E.val.obj (op U)),
    app U V k hk (a • x) = k.appTop a • app U V k hk x
  naturality : ∀ (U₁ U₂ : W.Etale) (V₁ V₂ : Z.Etale)
    (a : U₁ ⟶ U₂) (b : V₁ ⟶ V₂) (k₁ : V₁.left ⟶ U₁.left)
    (k₂ : V₂.left ⟶ U₂.left)
    (h₁ : k₁ ≫ U₁.hom = V₁.hom ≫ c) (h₂ : k₂ ≫ U₂.hom = V₂.hom ≫ c),
    b.left ≫ k₂ = k₁ ≫ a.left → ∀ x : E.val.obj (op U₂),
      F.val.map b.op (app U₂ V₂ k₂ h₂ x) =
        app U₁ V₁ k₁ h₁ (E.val.map a.op x)

/-- The tensor pullback, specified by its unit and full module adjunction. This
universal property uniquely characterizes `O_Z ⊗[c⁻¹O_W] c⁻¹E`, including its unit
`1 ⊗ x`. It does not permit an arbitrary map or an arbitrary isomorphic module.
Source: Stacks 03D3, 03EK; the strict-pushout lemma's tensor convention
(blueprint: def-per-etale-differential-pullback-presentation). -/
structure EtaleDifferentialPullbackPresentation {Z W : Scheme.{u}} (c : Z ⟶ W)
    (E : DifferentialEtaleModules W) where
  module : DifferentialEtaleModules Z
  unit : EtaleDifferentialModuleMap c E module
  universal : ∀ (T : DifferentialEtaleModules Z) (τ : EtaleDifferentialModuleMap c E T),
    ∃! h : module ⟶ T, ∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ c) (x : E.val.obj (op U)),
      h.val.app (op V) (unit.app U V k hk x) = τ.app U V k hk x

end AlgebraicGeometry
