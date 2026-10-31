/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.RepresentationTheory.DiscreteModule.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# The field dictionary at an algebraic geometric point

Source: Stacks Project, Tags 04JQ, 04JM, 03QU and 03QW; blueprint
`sec-curve-estimates/sk-thm-br/lem-exc-field-discrete-modules.md`.
(blueprint: lem-exc-field-discrete-modules)

The equivalence and its action are the existing `etaleSheafEquivDiscreteModule`.
This statement includes its canonical comparison with the geometric stalk at an
algebraic closure containing the separable closure, and natural comparisons of
sections and of derived global sections with invariants and continuous cohomology.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

/-- The existing abelian structure on discrete modules, with its coefficient universe
kept explicit before specialization. This is Mathlib's full-subcategory instance,
using the closure and zero instances already proved in `DiscreteModule.Basic`.
Source: Stacks Project, Tag 04JQ (blueprint: lem-exc-field-discrete-modules). -/
@[instance_reducible]
noncomputable def DiscreteModule.abelianForFieldComparison
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Abelian (DiscreteModule.{w} G) := inferInstance

/-- Derived continuous invariants of a discrete module, viewed as a complex in degree
zero. This is the actual bounded-below right derived invariants functor, followed
by the inclusion into the unbounded derived category of abelian groups; no
cohomology groups are assembled into an artificial complex. The source derived
category uses the standard localization, which exists without a Grothendieck
abelian hypothesis. Enough injectives and additivity come from the existing
`DiscreteModule` API. All local instances here are existing constructions.
Source: Stacks Project, Tags 03QU and 0156, and the right-derived-invariants
notion in `def-exc-continuous-cohomology`.
(blueprint: lem-exc-field-discrete-modules) -/
noncomputable def DiscreteModule.derivedInvariantsForFieldComparison
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    DiscreteModule.{w} G ⥤ DerivedCategory AddCommGrpCat.{max u w} := by
  letI := DiscreteModule.abelianForFieldComparison.{w, u} G
  letI := HasDerivedCategory.standard (DiscreteModule.{w} G)
  exact DerivedCategory.Plus.singleFunctor (DiscreteModule.{w} G) 0 ⋙
    (DiscreteModule.invariants.{w} G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

namespace AlgebraicGeometry.Scheme

/-- Precomposition with the field embedding gives inverse natural maps on stalk colimits.
Source: Stacks Project, Tag 03QW; the lift existence and uniqueness lemmas.
(blueprint: lem-exc-field-discrete-modules) -/
private theorem fieldStalkComparison
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosed Ks] [Algebra K Ω] [IsAlgClosed Ω]
    (i : Ks →ₐ[K] Ω) :
    ∃ η : (galoisPoint K Ks).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
        (pointSmallEtale (specAlgebraMap K Ω)).sheafFiber,
      ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (X : (Spec (.of K)).Etale)
        (x : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X)
        (y : (pointSmallEtale (specAlgebraMap K Ω)).fiber.obj X),
        y.left = Spec.map (CommRingCat.ofHom i.toRingHom) ≫ x.left →
        (galoisPoint K Ks).toPresheafFiber X (ULift.up x) F.obj ≫ η.hom.app F =
          (pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X y F.obj := by
  classical
  let p := galoisPoint K Ks
  let r := pointSmallEtale (specAlgebraMap K Ω)
  let β := CommRingCat.ofHom i.toRingHom
  have hw : Spec.map β ≫ specAlgebraMap K Ks = specAlgebraMap K Ω := by
    rw [specAlgebraMap, ← Spec.map_comp]
    congr 1
    ext t
    exact i.commutes t
  let q (X : (Spec (.of K)).Etale) (x : p.fiber.obj X) : r.fiber.obj X :=
    Over.homMk (Spec.map β ≫ x.down.left) (by
      rw [Category.assoc, Over.w x.down]
      exact hw)
  have hq (X : (Spec (.of K)).Etale) : Function.Bijective (q X) := by
    constructor
    · intro x y h
      apply ULift.ext
      apply Over.OverMorphism.ext
      exact SpecMap_comp_injective β (congrArg (fun z ↦ z.left) h)
    · intro y
      obtain ⟨x, hxy, hx⟩ := X.hom.exists_SpecMap_comp_eq_of_isSepClosed β
        (specAlgebraMap K Ks) y.left ((Over.w y).trans hw.symm)
      refine ⟨ULift.up (Over.homMk x hx), ?_⟩
      exact Over.OverMorphism.ext hxy
  let a (X : (Spec (.of K)).Etale) := Equiv.ofBijective (q X) (hq X)
  have ha {X Y : (Spec (.of K)).Etale} (f : X ⟶ Y) (x : p.fiber.obj X) :
      r.fiber.map f (a X x) = a Y (p.fiber.map f x) := by
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _
  have hb {X Y : (Spec (.of K)).Etale} (f : X ⟶ Y) (y : r.fiber.obj X) :
      p.fiber.map f ((a X).symm y) = (a Y).symm (r.fiber.map f y) := by
    apply (a Y).injective
    rw [← ha, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let m (P : (Spec (.of K)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    p.presheafFiberDesc (fun X x ↦ r.toPresheafFiber X (a X x) P)
      (fun X Y f x ↦ by rw [r.toPresheafFiber_w, ha])
  let n (P : (Spec (.of K)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    r.presheafFiberDesc (fun X y ↦ p.toPresheafFiber X ((a X).symm y) P)
      (fun X Y f y ↦ by rw [p.toPresheafFiber_w, hb])
  have hm (P : (Spec (.of K)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (X : (Spec (.of K)).Etale) (x : p.fiber.obj X) :
      p.toPresheafFiber X x P ≫ m P = r.toPresheafFiber X (a X x) P :=
    p.toPresheafFiber_presheafFiberDesc _ _ X x
  have hn (P : (Spec (.of K)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (X : (Spec (.of K)).Etale) (y : r.fiber.obj X) :
      r.toPresheafFiber X y P ≫ n P = p.toPresheafFiber X ((a X).symm y) P :=
    r.toPresheafFiber_presheafFiberDesc _ _ X y
  let η : p.sheafFiber (A := AddCommGrpCat.{u + 1}) ≅ r.sheafFiber :=
    NatIso.ofComponents (fun F ↦
      { hom := m F.obj
        inv := n F.obj
        hom_inv_id := by
          apply p.presheafFiber_hom_ext
          intro X x
          change p.toPresheafFiber X x F.obj ≫ (m F.obj ≫ n F.obj) =
            p.toPresheafFiber X x F.obj ≫ 𝟙 _
          rw [← Category.assoc, hm, hn, Equiv.symm_apply_apply, Category.comp_id]
        inv_hom_id := by
          apply r.presheafFiber_hom_ext
          intro X y
          change r.toPresheafFiber X y F.obj ≫ (n F.obj ≫ m F.obj) =
            r.toPresheafFiber X y F.obj ≫ 𝟙 _
          rw [← Category.assoc, hn, hm, Equiv.apply_symm_apply, Category.comp_id] }) (by
      intro F F' f
      apply p.presheafFiber_hom_ext
      intro X x
      change p.toPresheafFiber X x F.obj ≫ (p.presheafFiber.map f.hom ≫ m F'.obj) =
        p.toPresheafFiber X x F.obj ≫ (m F.obj ≫ r.presheafFiber.map f.hom)
      rw [← Category.assoc, p.toPresheafFiber_naturality, Category.assoc, hm,
        ← Category.assoc, hm, r.toPresheafFiber_naturality])
  refine ⟨η, ?_⟩
  intro F X x y hy
  have hxy : a X (ULift.up x) = y := Over.OverMorphism.ext hy.symm
  change p.toPresheafFiber X (ULift.up x) F.obj ≫ m F.obj = _
  rw [hm, hxy]

/-- Evaluate the Galois-point equivalence unit at the unique lift of the terminal object.
Source: Stacks Project, Tag 04JM.
(blueprint: lem-exc-field-discrete-modules) -/
private theorem fieldSectionsComparison
    (K Ks : Type u) [Field K] [Field Ks]
    [Algebra K Ks] [IsSepClosed Ks] [Algebra.IsSeparable K Ks] :
    ∃ σ : Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≅
        (etaleSheafEquivDiscreteModule K Ks).functor ⋙
          DiscreteModule.invariants.{u + 1} Gal(Ks/K),
      ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (X : (Spec (.of K)).Etale)
        (x : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X),
        σ.hom.app F ≫ AddCommGrpCat.ofHom
            (DiscreteModule.invariantsSubgroup
              ((etaleSheafEquivDiscreteModule K Ks).functor.obj F)).subtype =
          F.ΓRes (op X) ≫ (galoisPoint K Ks).toPresheafFiber X (ULift.up x) F.obj := by
  classical
  let p := galoisPoint K Ks
  let act := galoisPointAct K Ks
  let E := etaleSheafEquivDiscreteModule K Ks
  let T := Etale.mk (𝟙 (Spec (.of K)))
  let hT : IsTerminal T := Etale.isTerminalMkId _
  let x0 : p.fiber.obj T := ULift.up
    (Over.homMk (specAlgebraMap K Ks) (by simp [T]))
  have hx (x : p.fiber.obj T) : x = x0 := by
    apply ULift.ext
    apply Over.OverMorphism.ext
    simpa [T, x0] using Over.w x.down
  let ev (M : DiscreteModule.{u + 1} Gal(Ks/K)) :
      p.equivariantMaps act M.obj T ≃+ DiscreteModule.invariantsSubgroup M :=
    { toFun f := ⟨f.val x0, fun g ↦ by
        have hh := f.property g x0
        rw [hx ((act g).app T x0)] at hh
        exact hh.symm⟩
      invFun m := ⟨fun _ ↦ m.val, fun g _ ↦ (m.property g).symm⟩
      left_inv f := by
        apply Subtype.ext
        funext x
        exact congrArg f.val (hx x).symm
      right_inv _ := rfl
      map_add' _ _ := rfl }
  have hres (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      IsIso (F.ΓRes (op T)) :=
    F.isLimitConeΓ.isIso_π_app_of_isInitial (op T) hT.op
  let e (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (Sheaf.Γ _ AddCommGrpCat.{u + 1}).obj F ≅
        (DiscreteModule.invariants.{u + 1} Gal(Ks/K)).obj (E.functor.obj F) := by
    let := hres F
    let := (isGaloisPoint_galoisPoint K Ks).isIso_toEquivariantSheaf F
    exact asIso (F.ΓRes (op T)) ≪≫
      ((sheafSections _ AddCommGrpCat.{u + 1}).obj (op T)).mapIso
        (asIso (p.toEquivariantSheaf act F)) ≪≫ (ev (E.functor.obj F)).toAddCommGrpIso
  have he (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      (e F).hom ≫ AddCommGrpCat.ofHom
          (DiscreteModule.invariantsSubgroup (E.functor.obj F)).subtype =
        F.ΓRes (op T) ≫ p.toPresheafFiber T x0 F.obj := by
    ext z
    rfl
  let σ : Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      E.functor ⋙ DiscreteModule.invariants.{u + 1} Gal(Ks/K) :=
    NatIso.ofComponents e (by
      intro F F' f
      ext z
      apply Subtype.ext
      change (p.toPresheafFiber T x0 F'.obj)
          ((F'.ΓRes (op T)) ((Sheaf.Γ _ AddCommGrpCat.{u + 1}).map f z)) =
        (p.presheafFiber.map f.hom)
          ((p.toPresheafFiber T x0 F.obj) ((F.ΓRes (op T)) z))
      have hr := congrArg (fun k ↦ k z) (Sheaf.ΓRes_naturality f (op T))
      change F'.ΓRes (op T) ((Sheaf.Γ _ AddCommGrpCat.{u + 1}).map f z) =
        f.hom.app (op T) (F.ΓRes (op T) z) at hr
      rw [hr]
      exact (congrArg (fun k ↦ k (F.ΓRes (op T) z))
        (p.toPresheafFiber_naturality f.hom T x0)).symm)
  refine ⟨σ, ?_⟩
  intro F X x
  change (e F).hom ≫ _ = _
  rw [he]
  let f : X ⟶ T := hT.from X
  have hfx : p.fiber.map f (ULift.up x) = x0 := hx _
  calc
    F.ΓRes (op T) ≫ p.toPresheafFiber T x0 F.obj =
        F.ΓRes (op T) ≫ F.obj.map f.op ≫
          p.toPresheafFiber X (ULift.up x) F.obj := by
      rw [p.toPresheafFiber_w, hfx]
    _ = F.ΓRes (op X) ≫ p.toPresheafFiber X (ULift.up x) F.obj := by
      rw [← Category.assoc, F.ΓRes_map]

/-- The existing Galois-module equivalence is exact and has the asserted geometric
fibre, sections and cohomology comparisons. The two hypotheses `IsSepClosed Ks`
and `Algebra.IsSeparable K Ks` are exactly the fields of `IsSepClosure K Ks`;
`IsAlgClosed Ω` and `Algebra.IsAlgebraic K Ω` similarly specify an algebraic closure.
The embedding `i` specifies the containment of the separable closure in that closure.

The germ equation characterizes the fibre comparison uniquely: it keeps the section
and precomposes its lift by `Spec i`. The action on its source is the existing
`galoisPointAct K Ks`, which changes a lift by precomposition with `Spec g`.
The target of the comparison is definitionally the recorded `pointedEtaleStalk`.
The sections comparison is characterized by its germ at every pointed etale
object. The last natural isomorphism compares the actual derived objects in
`DerivedCategory AddCommGrpCat`, before taking any cohomology.

Proof:
1. Precomposition by `Spec i` bijects the separably closed and geometric lifts:
existence is the separably closed etale lifting lemma and uniqueness is injectivity
of precomposition by a field map. These bijections commute with etale morphisms,
so the germ maps descend through both stalk colimits to mutually inverse natural
maps, giving the stalk comparison and its germ equation (`fieldStalkComparison`).
2. Exactness: `etaleSheafEquivDiscreteModule` is an equivalence, so it preserves
finite limits and finite colimits.
3. The equivalence unit identifies a sheaf with the sheaf of equivariant maps from
the point fibres to its Galois module. The terminal etale object `Spec K` has a
single lift, and evaluation there identifies equivariant maps with invariants.
Composed with terminal restriction of global sections this is the natural sections
comparison; the unit is the germ map, which gives the germ equation at every
pointed etale object (`fieldSectionsComparison`).
4. Derive the sections-invariants isomorphism on bounded-below derived categories.
The equivalence is additive and exact and preserves injectives, so
`rightDerivedFunctorPlusCompIso` identifies the derived composite with the
composite of the derived functors, the derived functor of the exact equivalence is
`mapDerivedCategoryPlus`, and this commutes with single complexes. Including into
the unbounded derived category, `rightDerivedFunctorPlusCompatibility` identifies
the result with `Etale.rightDerivedGlobalSections` on single sheaves.

Source: Stacks Project, Tags 04JQ, 04JM, 03QU and 03QW.
(blueprint: lem-exc-field-discrete-modules) -/
theorem fieldDiscreteModulesDerivedComparison
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosed Ks] [Algebra.IsSeparable K Ks]
    [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (i : Ks →ₐ[K] Ω) :
    PreservesFiniteLimits (etaleSheafEquivDiscreteModule K Ks).functor ∧
    PreservesFiniteColimits (etaleSheafEquivDiscreteModule K Ks).functor ∧
    ∃ η : (etaleSheafEquivDiscreteModule K Ks).functor ⋙
        DiscreteModule.forget₂Ab.{u + 1} Gal(Ks/K) ≅
          (pointSmallEtale (specAlgebraMap K Ω)).sheafFiber,
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (X : (Spec (.of K)).Etale)
        (x : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X)
        (y : (pointSmallEtale (specAlgebraMap K Ω)).fiber.obj X),
        y.left = Spec.map (CommRingCat.ofHom i.toRingHom) ≫ x.left →
        (galoisPoint K Ks).toPresheafFiber X (ULift.up x) F.obj ≫ η.hom.app F =
          (pointSmallEtale (specAlgebraMap K Ω)).toPresheafFiber X y F.obj) ∧
      (∃ σ : Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≅
          (etaleSheafEquivDiscreteModule K Ks).functor ⋙
            DiscreteModule.invariants.{u + 1} Gal(Ks/K),
        ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
          (X : (Spec (.of K)).Etale)
          (x : (pointSmallEtale (specAlgebraMap K Ks)).fiber.obj X),
          σ.hom.app F ≫ AddCommGrpCat.ofHom
              (DiscreteModule.invariantsSubgroup
                ((etaleSheafEquivDiscreteModule K Ks).functor.obj F)).subtype =
            F.ΓRes (op X) ≫
              (galoisPoint K Ks).toPresheafFiber X (ULift.up x) F.obj) ∧
      Nonempty
        (DerivedCategory.singleFunctor
            (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
          Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} (Spec (.of K)) ≅
        (etaleSheafEquivDiscreteModule K Ks).functor ⋙
          DiscreteModule.derivedInvariantsForFieldComparison.{u + 1, u} Gal(Ks/K)) := by
  obtain ⟨η, hη⟩ := fieldStalkComparison K Ks Ω i
  obtain ⟨σ, hσ⟩ := fieldSectionsComparison K Ks
  refine ⟨inferInstance, inferInstance, η, hη, ⟨σ, hσ⟩, ?_⟩
  let := DiscreteModule.abelianForFieldComparison.{u + 1, u} Gal(Ks/K)
  let := HasDerivedCategory.standard (DiscreteModule.{u + 1} Gal(Ks/K))
  let E := etaleSheafEquivDiscreteModule K Ks
  let : E.functor.Additive :=
    (isGaloisPoint_galoisPoint K Ks).additive_equivalence_functor
  let Γ := Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}
  let V := DiscreteModule.invariants.{u + 1} Gal(Ks/K)
  let e : Γ.rightDerivedFunctorPlus ≅
      E.functor.mapDerivedCategoryPlus ⋙ V.rightDerivedFunctorPlus :=
    Functor.rightDerivedFunctorPlusNatIso σ ≪≫
      Functor.rightDerivedFunctorPlusCompIso E.functor V ≪≫
      Functor.isoWhiskerRight E.functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        V.rightDerivedFunctorPlus
  let s := DerivedCategory.Plus.singleFunctor
    (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let t := DerivedCategory.Plus.singleFunctor (DiscreteModule.{u + 1} Gal(Ks/K)) 0
  let d : s ⋙ Γ.rightDerivedFunctorPlus ≅ E.functor ⋙ t ⋙ V.rightDerivedFunctorPlus :=
    Functor.isoWhiskerLeft s e ≪≫
      (Functor.associator s E.functor.mapDerivedCategoryPlus V.rightDerivedFunctorPlus).symm ≪≫
      Functor.isoWhiskerRight (E.functor.mapDerivedCategoryPlusSingleFunctor 0)
        V.rightDerivedFunctorPlus ≪≫ Functor.associator E.functor t V.rightDerivedFunctorPlus
  exact ⟨Functor.isoWhiskerLeft s Γ.rightDerivedFunctorPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight d DerivedCategory.Plus.ι⟩

set_option linter.unusedVariables false in
/-- Degreewise continuous cohomology comparison, as a corollary of the derived
comparison `fieldDiscreteModulesDerivedComparison`.

Proof: `nonempty_sheafH_extDerivedIso` identifies the degree-`q` derived global
sections of a single sheaf naturally with Ext from the constant integer sheaf. The
exact equivalence preserves injectives and is fully faithful, so its map on these
Ext groups is bijective in every degree (`mapExtPrecomp_bijective`), after
precomposing with the canonical identification of the image of the constant
integer sheaf with the trivial integer module. `mapExtPrecomp_comp_mk₀` gives
naturality. Degree zero is included; no degree exception is imposed.
Source: Stacks Project, Tag 03QU.
(blueprint: lem-exc-field-discrete-modules) -/
theorem fieldDiscreteModulesCohomologyComparison
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosed Ks] [Algebra.IsSeparable K Ks]
    [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] (i : Ks →ₐ[K] Ω) :
    ∀ q : ℕ, Nonempty
      (DerivedCategory.singleFunctor
          (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) (q : ℤ) ≅
      (etaleSheafEquivDiscreteModule K Ks).functor ⋙
        (@Abelian.extFunctor.{u + 1} (DiscreteModule.{u + 1} Gal(Ks/K)) inferInstance
          (DiscreteModule.abelianForFieldComparison.{u + 1, u} Gal(Ks/K))
          DiscreteModule.instHasExt.{u + 1, u} q).obj
          (op (DiscreteModule.intTrivial.{u + 1} Gal(Ks/K)))) := by
  let := DiscreteModule.abelianForFieldComparison.{u + 1, u} Gal(Ks/K)
  intro q
  let E := etaleSheafEquivDiscreteModule K Ks
  let : E.functor.Additive :=
    (isGaloisPoint_galoisPoint K Ks).additive_equivalence_functor
  let Z := (constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let c : E.functor.obj Z ≅ DiscreteModule.intTrivial.{u + 1} Gal(Ks/K) :=
    (isGaloisPoint_galoisPoint K Ks).functorObjConstantSheafIso _
  have hb (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Function.Bijective (fun f : Z ⟶ F ↦ c.inv ≫ E.functor.map f) := by
    constructor
    · intro f g h
      apply E.functor.map_injective
      exact (cancel_epi c.inv).mp h
    · intro f
      refine ⟨E.functor.preimage (c.hom ≫ f), ?_⟩
      simp
  let e : Sheaf.functorH.{u + 1} (Spec (.of K)).smallEtaleTopology q ≅
      E.functor ⋙ (@Abelian.extFunctor.{u + 1}
        (DiscreteModule.{u + 1} Gal(Ks/K)) inferInstance
        (DiscreteModule.abelianForFieldComparison.{u + 1, u} Gal(Ks/K))
        DiscreteModule.instHasExt.{u + 1, u} q).obj
        (op (DiscreteModule.intTrivial.{u + 1} Gal(Ks/K))) :=
    NatIso.ofComponents (fun F ↦
      (AddEquiv.ofBijective (E.functor.mapExtPrecomp c.inv F q)
        (E.functor.mapExtPrecomp_bijective c.inv
          (fun I hI ↦ by let := hI; infer_instance) hb F q)).toAddCommGrpIso)
      (by
        intro F F' f
        ext a
        exact E.functor.mapExtPrecomp_comp_mk₀ c.inv f a)
  exact ⟨(nonempty_sheafH_extDerivedIso (Spec (.of K)) q).some.symm ≪≫ e⟩

end AlgebraicGeometry.Scheme
