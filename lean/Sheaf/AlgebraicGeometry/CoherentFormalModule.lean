/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

/-! # Coherent formal modules and completion

Source: Stacks Project, Cohomology of Schemes, Section 0EHN, equation 0880,
the paragraph before Lemma 0889, proof of Theorem 088E, and Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module).

## Main definitions
* `CoherentFormalModule`: the full category of coherent adic inverse systems.
* `completion`: the functor taking quotients by positive powers of the ideal.
* `AnnihilatedBy`, `IsIdealPowerTorsion`, `SupportedOn`: annihilation predicates.
* `CohSupportProper`, `CohModuleSupportProper`: full proper-support subcategories.

The index `op n` represents level `n + 1`, so no level zero is imposed.
Products and powers are the shared `Scheme.idealModuleProduct` and `Scheme.idealSheafPower`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- Coherent modules as a full subcategory of all modules.
Source: Stacks, Section 0EHN (blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CoherentModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (C := X.Modules) (RingedSpace.IsCoherent X.toRingedSpace)

/-- The quotient by the image of multiplication by the nth power of a quasi-coherent ideal.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalModuleQuotient {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    X.Modules :=
  cokernel (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 F)

/-- The quotient projection.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalModuleQuotientπ {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) :
    F ⟶ formalModuleQuotient I n F :=
  cokernel.π (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2 F)

/-- The defining object conditions: coherence, annihilation by I^(n+1), and an induced
quotient isomorphism whose composite with the quotient projection is the transition map.
Source: Stacks, Section 0EHN (blueprint: def-weil-pbc-coherent-formal-module). -/
def IsCoherentFormalModule {X : Scheme.{u}} (I : X.IdealSheafData)
    : ObjectProperty (ℕᵒᵖ ⥤ X.Modules) := fun F ↦
  (∀ n : ℕ, RingedSpace.IsCoherent X.toRingedSpace (F.obj (op n))) ∧
  (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
    (Scheme.idealSheafPower I.toModulesι (n + 1)).2 (F.obj (op n)))) ∧
  (∀ n : ℕ, ∃ e : formalModuleQuotient I (n + 1) (F.obj (op (n + 1))) ≅ F.obj (op n),
    formalModuleQuotientπ I (n + 1) (F.obj (op (n + 1))) ≫ e.hom =
      F.map (homOfLE (Nat.le_succ n)).op)

/-- The full subcategory of inverse systems satisfying the coherent adic conditions.
This is Stacks' Coh(X, I); the object `op n` is the level `n + 1`. Morphisms are natural
transformations, hence precisely compatible families of module maps.
Source: Stacks, Section 0EHN (blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CoherentFormalModule (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) :=
  (IsCoherentFormalModule I).FullSubcategory

/-- Linear maps preserve ideal products; inclusion of powers for n ≤ m gives the
factorization needed for the canonical quotient map. Proof: node steps 1--3: on affine
opens u sends each sum a_i s_i to the sum a_i u(s_i); I^m F is contained in I^n F.
The quotient projection kills I^n F. Equality on the affine basis gives the sheaf equality.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModuleQuotient_map_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι m).2 F ≫
      f ≫ formalModuleQuotientπ I n G = 0 := by
  sorry

/-- Reduction of a linear map from level m to level n, n ≤ m, by the cokernel property.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalModuleQuotientMap {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (f : F ⟶ G) {m n : ℕ} (h : n ≤ m) :
    formalModuleQuotient I m F ⟶ formalModuleQuotient I n G :=
  cokernel.desc (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι m).2 F)
    (f ≫ formalModuleQuotientπ I n G) (formalModuleQuotient_map_zero I f h)

/-- Reduction preserves identities. Proof: node step 6; after precomposing with the
cokernel projection both sides are the projection, so the cokernel universal property
identifies them.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModuleQuotientMap_id {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) (n : ℕ) :
    formalModuleQuotientMap I (𝟙 F) (Nat.le_refl n) = 𝟙 (formalModuleQuotient I n F) := by
  sorry

/-- Reduction preserves composition, including transition maps between different levels.
Proof: node step 6; precompose with the source quotient projection, use the defining
factorization of each reduction, and cancel this epimorphism by the cokernel property.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModuleQuotientMap_comp {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) {l m n : ℕ}
    (h₁ : m ≤ l) (h₂ : n ≤ m) :
    formalModuleQuotientMap I (f ≫ g) (Nat.le_trans h₂ h₁) =
      formalModuleQuotientMap I f h₁ ≫ formalModuleQuotientMap I g h₂ := by
  sorry

/-- Canonical reductions form an inverse system. Proof: node steps 5--6; quotient
projections are epi, and both sides of each identity or composition law agree after
precomposition with the projection, by uniqueness in the cokernel universal property.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionSystem_laws {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : X.Modules) :
    (∀ n : ℕᵒᵖ, formalModuleQuotientMap I (𝟙 F)
      (Nat.succ_le_succ (leOfHom (𝟙 n).unop)) =
        𝟙 (formalModuleQuotient I (n.unop + 1) F)) ∧
    (∀ (a b c : ℕᵒᵖ) (f : a ⟶ b) (g : b ⟶ c),
      formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom (f ≫ g).unop)) =
        formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom f.unop)) ≫
          formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom g.unop))) := by
  sorry

/-- The inverse system F/I^(n+1)F, with the canonical surjections.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalCompletionSystem {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules) :
    ℕᵒᵖ ⥤ X.Modules where
  obj n := formalModuleQuotient I (n.unop + 1) F
  map f := formalModuleQuotientMap I (𝟙 F) (Nat.succ_le_succ (leOfHom f.unop))
  map_id := (formalCompletionSystem_laws I F).1
  map_comp f g := (formalCompletionSystem_laws I F).2 _ _ _ f g

/-- Reduction of a module map commutes with transitions. Proof: node step 6; both
composites after precomposition with the source quotient map are u followed by the target
quotient map, so uniqueness of cokernel factorization gives equality.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionMap_naturality {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (u : F ⟶ G) (a b : ℕᵒᵖ) (f : a ⟶ b) :
    (formalCompletionSystem I F).map f ≫
      formalModuleQuotientMap I u (Nat.le_refl (b.unop + 1)) =
    formalModuleQuotientMap I u (Nat.le_refl (a.unop + 1)) ≫
      (formalCompletionSystem I G).map f := by
  sorry

/-- The compatible family of reductions of a module map.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalCompletionMap {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : X.Modules} (u : F ⟶ G) : formalCompletionSystem I F ⟶ formalCompletionSystem I G
    where
  app n := formalModuleQuotientMap I u (Nat.le_refl (n.unop + 1))
  naturality := formalCompletionMap_naturality I u

/-- Completion of a coherent module satisfies the object conditions. Proof: node steps
1--5. Products and quotients are computed on affine opens; coherence of the quotient
follows from quasi-coherence and finite type on a locally Noetherian scheme. For M/I^n M,
I^n acts by zero, and (M/I^(n+1)M)/I^n(M/I^(n+1)M) is canonically M/I^n M by the third
isomorphism theorem. Checking this on the affine basis gives the induced sheaf isomorphism.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionSystem_coherent {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentModules X) :
    IsCoherentFormalModule I (formalCompletionSystem I F.obj) := by
  sorry

/-- The reduced maps satisfy functor laws. Proof: node step 6; check each component and
precompose with its quotient projection. For identities both sides give the projection;
for composition both sides give the original composite followed by the projection.
The cokernel property and componentwise equality identify the natural transformations.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletionMap_laws {X : Scheme.{u}} (I : X.IdealSheafData) :
    (∀ F : X.Modules, formalCompletionMap I (𝟙 F) = 𝟙 (formalCompletionSystem I F)) ∧
    (∀ (F G H : X.Modules) (f : F ⟶ G) (g : G ⟶ H),
      formalCompletionMap I (f ≫ g) = formalCompletionMap I f ≫ formalCompletionMap I g) := by
  sorry

/-- The functor to inverse systems, on objects the quotients and on maps their reductions.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def formalCompletionFunctor {X : Scheme.{u}} (I : X.IdealSheafData) :
    X.Modules ⥤ (ℕᵒᵖ ⥤ X.Modules) where
  obj := formalCompletionSystem I
  map := formalCompletionMap I
  map_id := (formalCompletionMap_laws I).1
  map_comp f g := (formalCompletionMap_laws I).2 _ _ _ f g

/-- The completion functor Coh(O_X) → Coh(X,I), with the specified quotient data.
Source: Stacks, equation 0880 (blueprint: def-weil-pbc-coherent-formal-module). -/
def completion (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) :
    CoherentModules X ⥤ CoherentFormalModule X I :=
  ObjectProperty.lift (IsCoherentFormalModule I)
    (ObjectProperty.ι (C := X.Modules) (RingedSpace.IsCoherent X.toRingedSpace) ⋙
      formalCompletionFunctor I)
    (formalCompletionSystem_coherent I)

/-- Annihilation by a quasi-coherent ideal means its product with each term is zero.
Source: Stacks, paragraph before Lemma 0889 and proof of Theorem 088E
(blueprint: def-weil-pbc-coherent-formal-module). -/
def AnnihilatedBy {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) : Prop :=
  ∀ n : ℕ, IsZero (Scheme.idealModuleProduct K.toModulesι (M.obj.obj (op n)))

/-- Uniform annihilation by a positive power of I, as opposed to the termwise adic condition.
Source: Stacks, paragraph before Lemma 0889
(blueprint: def-weil-pbc-coherent-formal-module). -/
def IsIdealPowerTorsion {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (M : CoherentFormalModule X I) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
    (Scheme.idealSheafPower I.toModulesι c).2 (M.obj.obj (op n)))

/-- Uniform annihilation by I^(c+1) is equivalent to stabilization at level c+1.
Proof: node step 7. On affine opens the transition from M_n to M_c is surjective with
kernel I^c M_n, by induction using I^(n-1) M_n ⊆ I^c M_n. Thus it is an isomorphism iff
I^c M_n=0 for n≥c; for smaller n this follows from I^c M_n ⊆ I^n M_n=0. The affine basis
criterion promotes these equalities and isomorphisms to sheaves.
Source: Stacks, paragraph before Lemma 0889
(blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalModule_annihilated_power_iff {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (M : CoherentFormalModule X I) (c : ℕ) :
    (∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower I.toModulesι (c + 1)).2 (M.obj.obj (op n)))) ↔
    ∀ (n : ℕ) (h : c ≤ n), IsIso (M.obj.map (homOfLE h).op) := by
  sorry

/-- Support on a closed subscheme means annihilation by its ideal, including its nilpotents.
Source: Stacks, proof of Theorem 088E (blueprint: def-weil-pbc-coherent-formal-module). -/
def SupportedOn {X Z : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (M : CoherentFormalModule X I) (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  AnnihilatedBy I i.ker M

/-- The analogous scheme-theoretic support condition for a coherent module.
Source: Stacks, proof of Theorem 088E (blueprint: def-weil-pbc-coherent-formal-module). -/
def CoherentModuleSupportedOn {X Z : Scheme.{u}} (F : CoherentModules X)
    (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  IsZero (Scheme.idealModuleProduct i.ker.toModulesι F.obj)

/-- Full subcategory of formal modules whose level 1 has support proper over the base.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CohSupportProper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (fun M : CoherentFormalModule X I ↦
      Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)))

/-- Full subcategory of coherent modules with support proper over the base.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
abbrev CohModuleSupportProper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :=
  ObjectProperty.FullSubcategory
    (fun F : CoherentModules X ↦ Scheme.Modules.HasSupportProperOver f F.obj)

/-- The support of F/IF is contained in the support of F.
Proof: node step 8. The quotient projection is surjective on sections over affine opens,
by lem-weil-pbc-quasi-coherent-module-cokernel-image, hence on stalks by the affine-basis
colimit description in def-weil-pbc-module-stalk. A quotient of a zero stalk is zero.
Therefore a nonzero quotient stalk can occur only at a nonzero original stalk.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletion_support_subset {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentModules X) :
    {x : X | ¬ Subsingleton ((formalModuleQuotient I 1 F.obj).presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (F.obj.presheaf.stalk x)} := by
  sorry

/-- Completion preserves proper support. Proof: node step 8. A coherent module has closed
support on a Noetherian scheme. The quotient projection is surjective on affine sections,
hence on stalks. A zero stalk of F therefore gives a zero stalk of F/IF. Its closed support
is contained in the closed support of F, and a closed subset of a support proper over the
base is proper (Lemma 0CYN). Thus the level-1 support has the required properness.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
theorem formalCompletion_support_proper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData)
    (F : CohModuleSupportProper f) :
    Scheme.Modules.HasSupportProperOver f (((completion X I).obj F.obj).obj.obj (op 0)) := by
  sorry

/-- Restriction of completion to the two proper-support full subcategories.
Source: Stacks, Section 0CYW, equation 088D
(blueprint: def-weil-pbc-coherent-formal-module). -/
def completionSupportProper {X S : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (I : X.IdealSheafData) :
    CohModuleSupportProper f ⥤ CohSupportProper f I :=
  ObjectProperty.lift
    (fun M : CoherentFormalModule X I ↦
      Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0)))
    (ObjectProperty.ι
      (fun F : CoherentModules X ↦ Scheme.Modules.HasSupportProperOver f F.obj) ⋙
      completion X I) (formalCompletion_support_proper f I)

end

end AlgebraicGeometry
