/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.SiteConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Adic-lisse modules over completed constant coefficients

Source: Stacks Project, proetale.tex, Tag 09BT, Definition `definition-adic`, clause (3)
(blueprint: def-weil-pbc-adic-lisse-module).

The index `n : ℕ` denotes exponent `n + 1`. All limits are genuine limits of sheaves.
Linearity over completed coefficients is expressed on the quotient projections, locally
lifting a scalar in a quotient to a section of the constant coefficient ring. This also
works over inverse-image coefficients without commuting inverse image with infinite limits.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The constant coefficient ring, with coefficients in the site universe.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
abbrev adicLisseConstantRing (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- Forget commutativity while retaining the actual constant coefficient sheaf.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
abbrev adicLisseRing (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (adicLisseConstantRing X A)

/-- The constant-ring sheafification unit, used by module sheafification.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def adicLisseConstantUnit (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ (adicLisseRing X A).obj :=
  Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- Forgetting commutativity leaves the underlying local injectivity condition unchanged.
Source: constant sheafification in Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
instance adicLisseConstantUnit_locallyInjective (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : Presheaf.IsLocallyInjective (ProEt.topology X)
      (adicLisseConstantUnit X A) :=
  (Presheaf.isLocallyInjective_forget_iff (ProEt.topology X)
    (adicLisseConstantUnit X A)).mp
      (inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X)
        (Functor.whiskerRight (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))))

/-- Forgetting commutativity leaves the underlying local surjectivity condition unchanged.
Source: constant sheafification in Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
instance adicLisseConstantUnit_locallySurjective (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : Presheaf.IsLocallySurjective (ProEt.topology X)
      (adicLisseConstantUnit X A) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget (ProEt.topology X)
    (adicLisseConstantUnit X A)).mpr
      (inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X)
        (Functor.whiskerRight (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))
          (CategoryTheory.forget CommRingCat.{u + 1}))))

/-- Pull the existing constant module presheaf on the one-object category back to the
actual small pro-etale site, then sheafify. This retains unequal site object/Hom universes.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def adicLisseConstantModules (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    ModuleCat.{u + 1} A ⥤ ringedSiteModules.{u + 1} (adicLisseRing X A) :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A)) ⋙
    PresheafOfModules.sheafification (adicLisseConstantUnit X A)

/-- Constant quotient ring sheaves with the actual quotient transition maps.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def adicLisseRingSystem (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    adicLisseConstantRing X (A ⧸ I ^ (n + 1))) (fun n : ℕ ↦
    (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1))))

/-- The completed coefficient ring is the inverse limit, computed sectionwise.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
abbrev adicLisseCompletedRing (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) := limit (adicLisseRingSystem X I)

/-- Quotient-module sheaves, with quotient transitions, before completing.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def adicLisseModuleSystem (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) :
    ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (adicLisseRing X A) :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    (adicLisseConstantModules X A).obj
      (ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))) (fun n : ℕ ↦
    (adicLisseConstantModules X A).map
      (ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1))))

/-- The completed constant module as a sheaf over the constant coefficient ring.
Its extension to completed scalars is specified by quotient projections in the local model.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
abbrev adicLisseCompletedModule (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) := limit (adicLisseModuleSystem X I N)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Forget commutativity for any coefficient sheaf and its maps.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
abbrev adicLisseForget (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- A local isomorphism to the completed constant module, linear over the completed
coefficient sheaf. The abelian-sheaf isomorphism is tested on every quotient projection.
For a completed scalar `r`, locally lift its `n`th residue to a constant-ring section `a`;
the displayed equality says that the projection of `r • x` is `a` times that of `x`.
The quotient-ring maps are epimorphisms, so such lifts exist locally. This is precisely
componentwise completed-scalar linearity; it also specifies the action after inverse image.
The limit in module sheaves has the sectionwise compatible-family underlying abelian sheaf.
Source: Tag 09BT (blueprint: def-weil-pbc-adic-lisse-module). -/
def IsAdicLisseLocalModel (X : Scheme.{u})
    (R₀ Rhat : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (Rₙ : ℕ → Sheaf (ProEt.topology X) RingCat.{u + 1})
    (ρ : ∀ n : ℕ, R₀ ⟶ Rₙ n) (π : ∀ n : ℕ, Rhat ⟶ Rₙ n)
    (S : ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} R₀)
    (F : ringedSiteModules.{u + 1} Rhat) (V : X.ProEt) : Prop :=
  ∃ e : ((SheafOfModules.toSheaf Rhat).obj F).over V ≅
      ((SheafOfModules.toSheaf R₀).obj (limit S)).over V,
    ∀ (n : ℕ) (W : (Over V)ᵒᵖ)
      (r : Rhat.obj.obj (op W.unop.left)) (a : R₀.obj.obj (op W.unop.left))
      (x : F.val.obj (op W.unop.left)),
      (ρ n).hom.app (op W.unop.left) a = (π n).hom.app (op W.unop.left) r →
        (limit.π S (op n)).val.app (op W.unop.left)
            (e.hom.hom.app W (r • x)) =
          a • (limit.π S (op n)).val.app (op W.unop.left) (e.hom.hom.app W x)

/-- Finite-type adic lissity on the small pro-etale site. Completeness is Mathlib's
`IsAdicComplete`, equivalent to bijectivity of the canonical residue-family map.
`Module.Finite A (N / IN)` is equivalently finite generation over `A/I`: the scalar
map is surjective and `I` annihilates this quotient. There is no freeness condition.
The sieve is a covering of the final object, hence a pro-etale covering of `X`.
Source: Tag 09BT, clause (3) (blueprint: def-weil-pbc-adic-lisse-module). -/
def IsAdicLisseModule (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (F : ringedSiteModules.{u + 1}
      ((adicLisseForget X).obj (adicLisseCompletedRing X I))) : Prop :=
  ∃ T : Sieve (⊤_ X.ProEt), T ∈ ProEt.topology X (⊤_ X.ProEt) ∧
    ∀ (V : X.ProEt) (f : V ⟶ ⊤_ X.ProEt), T f →
      ∃ N : ModuleCat.{u + 1} A, IsAdicComplete I N ∧
        Module.Finite A (N ⧸ (I • ⊤ : Submodule A N)) ∧
        IsAdicLisseLocalModel X (adicLisseRing X A)
          ((adicLisseForget X).obj (adicLisseCompletedRing X I))
          (fun n ↦ (adicLisseForget X).obj ((adicLisseRingSystem X I).obj (op n)))
          (fun n ↦ (adicLisseForget X).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
              (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
          (fun n ↦ (adicLisseForget X).map (limit.π (adicLisseRingSystem X I) (op n)))
          (adicLisseModuleSystem X I N) F V

/-- Relative finite-type adic lissity over the inverse image of completed coefficients.
Take inverse images of each quotient-module sheaf first and then their inverse limit.
The scalar test uses the image of each completed-ring projection, so its action factors
through the canonical map to the limit of inverse-image quotient rings. No preservation
of an infinite limit by inverse image is assumed, including for the identity morphism.
Source: Tag 09BT and the relative local-model clause of the blueprint
(blueprint: def-weil-pbc-adic-lisse-module). -/
def IsRelativelyAdicLisseModule {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : ringedSiteModules.{u + 1} ((adicLisseForget Y).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (adicLisseCompletedRing X I)))) : Prop :=
  ∃ T : Sieve (⊤_ Y.ProEt), T ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
    ∀ (V : Y.ProEt) (f : V ⟶ ⊤_ Y.ProEt), T f →
      ∃ N : ModuleCat.{u + 1} A, IsAdicComplete I N ∧
        Module.Finite A (N ⧸ (I • ⊤ : Submodule A N)) ∧
        IsAdicLisseLocalModel Y
          ((adicLisseForget Y).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (adicLisseConstantRing X A)))
          ((adicLisseForget Y).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (adicLisseCompletedRing X I)))
          (fun n ↦ (adicLisseForget Y).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              ((adicLisseRingSystem X I).obj (op n))))
          (fun n ↦ (adicLisseForget Y).map
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
              ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))
          (fun n ↦ (adicLisseForget Y).map
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
              (limit.π (adicLisseRingSystem X I) (op n))))
          (adicLisseModuleSystem X I N ⋙
            proEtaleModuleInverseImage g (adicLisseConstantRing X A)) F V

end AlgebraicGeometry.Scheme
