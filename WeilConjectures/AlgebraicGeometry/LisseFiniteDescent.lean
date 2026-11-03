/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentLisse
import WeilConjectures.AlgebraicGeometry.CoefficientFiniteDescentSections
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import all WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite coefficient descent of lisse diagrams

Source: Weil blueprint,
part-six-operations/sec-reduction-finite-coefficients/
sec-constructible-sheaves-with-field-coefficients/sk-lem-lisse-finite-descent/_section.md,
the entire lemma, and its one-paragraph proof in sk-lem-lisse-finite-descent.proof.md
(blueprint: sk-lem-lisse-finite-descent).

A finite quiver records the specified objects and arrows. Its path category records
composites without requiring the set of all paths to be finite. Two finite integral
linear combinations of paths specify each additive relation. This uses Mathlib's
existing path category and free abelian group, with no new diagram or relation notion.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Generator identifications extend to all paths by induction.
Source: the arrow assembly step (blueprint: sk-lem-lisse-finite-descent). -/
private lemma path_iso
    {A : Type*} [Quiver A] {C D : Type*} [Category C] [Category D]
    (V : A ⥤q C) (U : C ⥤ D) (F : Paths A ⥤ D)
    (θ : ∀ a : Paths A, U.obj ((Paths.lift V).obj a) ≅ F.obj a)
    (hθ : ∀ {a b : A} (q : Quiver.Hom a b),
      U.map ((Paths.lift V).map ((Paths.of A).map q)) ≫ (θ ((Paths.of A).obj b)).hom =
        (θ ((Paths.of A).obj a)).hom ≫ F.map ((Paths.of A).map q)) :
    Nonempty (Paths.lift V ⋙ U ≅ F) := by
  refine ⟨NatIso.ofComponents θ ?_⟩
  intro a b f
  induction f using Paths.induction with
  | id => simp
  | comp p q hp =>
    simp only [Functor.comp_map, Functor.map_comp] at hp ⊢
    rw [Category.assoc, hθ q, ← Category.assoc, hp, Category.assoc]

/-- Conjugating an arrow transports its commuting square.
Source: the arrow assembly step (blueprint: sk-lem-lisse-finite-descent). -/
private lemma conjugated_square
    {C : Type*} [Category C] {P P' Q Q' S T : C}
    (a : P ≅ P') (b : Q ≅ Q') (c : P ≅ S) (d : Q ≅ T)
    (f : P' ⟶ Q') (g : S ⟶ T)
    (h : a.hom ≫ f ≫ b.inv = c.hom ≫ g ≫ d.inv) :
    f ≫ (b.symm ≪≫ d).hom = (a.symm ≪≫ c).hom ≫ g := by
  apply (cancel_epi a.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]
  simp

/-- Additivity extends naturality to path sums, and faithfulness reflects equality.
Source: the relation assembly step (blueprint: sk-lem-lisse-finite-descent). -/
private lemma reflect_relation
    {J C D : Type*} [Category J] [Category C] [Category D]
    [Preadditive C] [Preadditive D]
    (U : C ⥤ D) [U.Additive] [U.Faithful] (G : J ⥤ C) (F : J ⥤ D)
    (e : G ⋙ U ≅ F) {a b : J} (p q : FreeAbelianGroup (a ⟶ b))
    (h : FreeAbelianGroup.lift (fun f : a ⟶ b ↦ F.map f) p =
      FreeAbelianGroup.lift (fun f : a ⟶ b ↦ F.map f) q) :
    FreeAbelianGroup.lift (fun f : a ⟶ b ↦ G.map f) p =
      FreeAbelianGroup.lift (fun f : a ⟶ b ↦ G.map f) q := by
  apply U.map_injective
  apply (cancel_mono (e.hom.app b)).mp
  have hsum (x : FreeAbelianGroup (a ⟶ b)) :
      U.map (FreeAbelianGroup.lift (fun f : a ⟶ b ↦ G.map f) x) ≫ e.hom.app b =
        e.hom.app a ≫ FreeAbelianGroup.lift (fun f : a ⟶ b ↦ F.map f) x := by
    let l := (Preadditive.rightComp _ (e.hom.app b)).comp
      (U.mapAddHom.comp (FreeAbelianGroup.lift (fun f : a ⟶ b ↦ G.map f)))
    let r := (Preadditive.leftComp _ (e.hom.app a)).comp
      (FreeAbelianGroup.lift (fun f : a ⟶ b ↦ F.map f))
    have hlr : l = r := FreeAbelianGroup.lift_ext _ _ (fun f ↦ by
      change U.map (FreeAbelianGroup.lift (fun f : a ⟶ b ↦ G.map f)
        (FreeAbelianGroup.of f)) ≫ e.hom.app b =
        e.hom.app a ≫ FreeAbelianGroup.lift (fun f : a ⟶ b ↦ F.map f)
          (FreeAbelianGroup.of f)
      simp only [FreeAbelianGroup.lift_apply_of]
      exact e.hom.naturality f)
    exact DFunLike.congr_fun hlr x
  rw [hsum, hsum, h]

/-- A finite family in the directed finite-field index has a common upper field.
Source: the compositum assertion (blueprint: def-weil-finite-subextension-directed-set). -/
private lemma finite_coefficient_upper_bound
    (ℓ : ℕ) [Fact ℓ.Prime] {I : Type*} [Finite I]
    (E : I → Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    ∃ H : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ), ∀ i, E i ≤ H := by
  let : Nonempty (Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :=
    ⟨Padic.finiteCoefficientBase ℓ (PadicAlgCl ℓ)⟩
  let : IsDirectedOrder (Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :=
    ⟨fun E F ↦ ⟨Padic.finiteCoefficientCompositum ℓ (PadicAlgCl ℓ) E F,
      (Padic.finiteCoefficientFields_properties ℓ (PadicAlgCl ℓ)).1 E F⟩⟩
  obtain ⟨H, hH⟩ := (Set.finite_range E).bddAbove
  exact ⟨H, fun i ↦ hH ⟨i, rfl⟩⟩

/-- Scalar extension takes the same local finite-free trivializations to finite-free ones.
Source: step 1 of the object descent assembly (blueprint: sk-lem-lisse-finite-descent). -/
private lemma lisse_coefficient_extend
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ' ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  have hi := free_map (Mod.extendScalars (coefficientMap a (U.X i)))
    (Mod.regularExtensionIso _) (hU i)
  exact free_of_iso hi ((CondensedRing.pullIso a (U.f i)).app M)

attribute [local irreducible] Mod.extendScalars lisseAlgClExtensionCompIso
  lisseFiniteExtensionCompIso

set_option maxHeartbeats 1000000 in
-- The tensor model assembly carries several field-dependent scalar comparisons.
/-- A finite collection of lisse algebraic-closure coefficient modules, specified arrows,
and finitely many additive relations descends to one finite coefficient field.
The natural isomorphism identifies every specified arrow as well as every object.
The input relations are equalities between finite integral sums of paths; empty paths
are identities, and zero, subtraction and sums of composites are included.

Source: blueprint
part-six-operations/sec-reduction-finite-coefficients/
sec-constructible-sheaves-with-field-coefficients/sk-lem-lisse-finite-descent/_section.md,
the entire lemma, and sk-lem-lisse-finite-descent.proof.md, the whole proof paragraph
(blueprint: sk-lem-lisse-finite-descent).

Proof plan:
1. Apply the object clause of det-lem-coefficient-finite-descent-lisse to each vertex.
Its proof uses a finite affine pro-etale trivializing cover, quasi-compact pair and triple
overlaps, and det-lem-coefficient-finite-descent-sections to place transition matrices
and their inverses in finite fields. Injectivity descends the cocycle equations.
Take their finite compositum using def-weil-finite-subextension-directed-set, or the base
field for an empty diagram. Extend the models to that field. They remain lisse:
the coefficient pullback comparison of sk-def-sfb-coefficient-change commutes extension
with pullback to the same covering, and extension sends regular modules
(lem-weil-pbc-regular-extension-comparison) and finite sums to the corresponding
regular modules and finite sums. The tower comparison of sk-def-sfb-change-of-scalars,
with lem-sfb-subfield-coefficient-map-comp, identifies their algebraic-closure extensions.
2. Conjugate each generating arrow by these object isomorphisms. The Hom clause of
det-lem-coefficient-finite-descent-lisse, using the filtered coefficient colimit of
sk-prop-sfb-qlbar-colimit-x, lifts each arrow after a finite enlargement. Take a common
compositum with the object field and extend every arrow to it; the canonical tower
comparisons preserve the arrow identifications. The generator equations give a natural
isomorphism on the path category by induction on paths, and additivity extends its
naturality to integral combinations of paths. Extension to the algebraic closure is
faithful (the injectivity of the Hom clause), so it reflects every relation at the
chosen field; no further enlargement is needed. Empty arrow and relation types require
no enlargement, and rank zero, varying ranks, and the empty scheme are all allowed. -/
theorem lisse_finite_descent
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type v) [Finite A] [Quiver.{w} A]
    [Finite (Σ a b : A, Quiver.Hom a b)]
    (F : Paths A ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClRingObj X ℓ))
    (hF : ∀ a : Paths A, IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) (F.obj a))
    (R : Type z) [Finite R] (s t : R → Paths A)
    (p q : ∀ r : R, FreeAbelianGroup (s r ⟶ t r))
    (hrel : ∀ r : R,
      FreeAbelianGroup.lift (fun f : s r ⟶ t r ↦ F.map f) (p r) =
        FreeAbelianGroup.lift (fun f : s r ⟶ t r ↦ F.map f) (q r)) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (G : Paths A ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ E)),
      (∀ a : Paths A, IsLisseCoefficientModule (Profinite.continuousMapRingObj E) (G.obj a)) ∧
      Nonempty (G ⋙ Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E) ≅ F) ∧
      ∀ r : R,
        FreeAbelianGroup.lift (fun f : s r ⟶ t r ↦ G.map f) (p r) =
          FreeAbelianGroup.lift (fun f : s r ⟶ t r ↦ G.map f) (q r) := by
  classical
  have hd := coefficient_finite_descent_lisse X ℓ
  choose E M hM eM using fun a : A ↦ hd.1 (F.obj a) (hF a)
  obtain ⟨E₀, hE₀⟩ := finite_coefficient_upper_bound ℓ E
  let N (a : A) := (Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hE₀ a))).obj (M a)
  have hN (a : A) : IsLisseCoefficientModule (Profinite.continuousMapRingObj E₀) (N a) :=
    lisse_coefficient_extend (Profinite.padicSubfieldRingObjMap ℓ (hE₀ a)) (M a) (hM a)
  let eN (a : A) :
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E₀)).obj (N a) ≅ F.obj a :=
    (lisseAlgClExtensionCompIso X ℓ (hE₀ a)).symm.app (M a) ≪≫ (eM a).some
  let I := Σ a b : A, Quiver.Hom a b
  have hlift (i : I) : ∃ (K : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E₀ ≤ K)
      (g : (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj (N i.1) ⟶
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).obj (N i.2.1)),
      lisseFiniteHomToAlgCl X ℓ h g =
        (eN i.1).hom ≫ F.map ((Paths.of A).map i.2.2) ≫ (eN i.2.1).inv := by
    obtain ⟨a, ha⟩ := (hd.2 E₀ (N i.1) (N i.2.1) (hN _) (hN _)).1
      ((eN i.1).hom ≫ F.map ((Paths.of A).map i.2.2) ≫ (eN i.2.1).inv)
    exact ⟨a.1.val, a.1.property, a.2, ha⟩
  choose K hK g hg using hlift
  obtain ⟨K₀, hK₀⟩ := finite_coefficient_upper_bound ℓ K
  let L := Padic.finiteCoefficientCompositum ℓ (PadicAlgCl ℓ) E₀ K₀
  have hEL : E₀ ≤ L :=
    ((Padic.finiteCoefficientFields_properties ℓ (PadicAlgCl ℓ)).1 E₀ K₀).1
  have hKL (i : I) : K i ≤ L := (hK₀ i).trans
    ((Padic.finiteCoefficientFields_properties ℓ (PadicAlgCl ℓ)).1 E₀ K₀).2
  let T := Mod.extendScalars (padicSubfieldRingObjMap X ℓ hEL)
  let U := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ L)
  let b (i : I) : T.obj (N i.1) ⟶ T.obj (N i.2.1) :=
    lisseFiniteHomTransition X ℓ (hK i) (hKL i) (g i)
  let V : A ⥤q Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ L) :=
    { obj := fun a ↦ T.obj (N a)
      map := fun {a b'} f ↦ b ⟨a, b', f⟩ }
  let G := Paths.lift V
  let θ (a : Paths A) : U.obj (G.obj a) ≅ F.obj a :=
    (lisseAlgClExtensionCompIso X ℓ hEL).symm.app (N a) ≪≫ eN a
  have hb {a b' : A} (f : Quiver.Hom a b') :
      U.map (G.map ((Paths.of A).map f)) ≫ (θ ((Paths.of A).obj b')).hom =
        (θ ((Paths.of A).obj a)).hom ≫ F.map ((Paths.of A).map f) := by
    let i : I := ⟨a, b', f⟩
    have hi := (lisseFiniteHomToAlgCl_transition X ℓ (hK i) (hKL i) (g i)).trans (hg i)
    change (lisseAlgClExtensionCompIso X ℓ hEL).hom.app (N i.1) ≫ U.map (b i) ≫
      (lisseAlgClExtensionCompIso X ℓ hEL).inv.app (N i.2.1) = _ at hi
    change U.map ((Paths.lift V).map f.toPath) ≫ _ = _
    rw [Paths.lift_toPath]
    change U.map (b i) ≫
        (((lisseAlgClExtensionCompIso X ℓ hEL).app (N b')).symm ≪≫ eN b').hom =
      (((lisseAlgClExtensionCompIso X ℓ hEL).app (N a)).symm ≪≫ eN a).hom ≫
        F.map ((Paths.of A).map f)
    exact conjugated_square
      ((lisseAlgClExtensionCompIso X ℓ hEL).app (N a))
      ((lisseAlgClExtensionCompIso X ℓ hEL).app (N b'))
      (eN a) (eN b') _ _ hi
  obtain ⟨e⟩ := path_iso V U F θ (fun f ↦ hb f)
  refine ⟨L, G, fun a ↦ ?_, ⟨e⟩, fun r ↦ ?_⟩
  · exact lisse_coefficient_extend (Profinite.padicSubfieldRingObjMap ℓ hEL) (N a) (hN a)
  · let : U.Faithful := coefficient_extension_faithful X ℓ L
    exact reflect_relation U G F e (p r) (q r) (hrel r)

end AlgebraicGeometry.ProEtale
