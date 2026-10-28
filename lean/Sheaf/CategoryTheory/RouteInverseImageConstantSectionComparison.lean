module

public import Sheaf.CategoryTheory.RouteInverseImageConstantSetComparison
import Mathlib.CategoryTheory.Sites.Limits

/-! # Normalization on constant sections. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private noncomputable def constantPointTerminal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    IsTerminal ((constantSheaf J (Type u)).obj PUnit.{u + 1}) :=
  (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type u)) _

private theorem point_section
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : Cᵒᵖ)
    (x : ((constantSheaf J (Type u)).obj PUnit.{u + 1}).obj.obj U) :
    x = (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{u + 1})).app U PUnit.unit := by
  let : Unique (((constantSheaf J (Type u)).obj PUnit.{u + 1}).obj.obj U) :=
    Types.isTerminalEquivUnique _
      (((constantPointTerminal J).isTerminalObj (sheafToPresheaf J (Type u)) _).isTerminalObj
        ((evaluation Cᵒᵖ (Type u)).obj U) _)
  exact Subsingleton.elim _ _

private theorem coeff_unit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{u}] (A : CommRingCat.{u}) (U : Cᵒᵖ) (a : A) :
    ((constantCommuteCompose J (forget CommRingCat)).inv.app A).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := by
  have h := sheafComposeIso_hom_fac J (forget CommRingCat) ((Functor.const Cᵒᵖ).obj A)
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ A (forget CommRingCat)).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type u))) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ A (forget CommRingCat)).inv) ≫
    (sheafifyComposeIso J (forget CommRingCat) ((Functor.const Cᵒᵖ).obj A)).hom).app U) a = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

private theorem constantMap_unit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (X Y : Type u) (f : X → Y) (U : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type u)).map (TypeCat.ofHom f)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app U (f x) := by
  exact (congrArg (fun g ↦ g.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

/-- The canonical comparison fixes sheafified constant sections.
Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(blueprint: lem-route-inverse-image-constant-section-comparison). -/
 theorem canonicalConstantSectionComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) :
      ∀ (a : CommRingCat.{u}) (x : a) (T : Sheaf JC (Type u))
        (s : T ⟶ (sheafCompose JC (forget CommRingCat)).obj
          ((constantSheaf JC CommRingCat.{u}).obj a)),
        (∀ (U : Cᵒᵖ) (y : T.obj.obj U),
          (@id (((constantSheaf JC CommRingCat.{u}).obj a).obj.obj U) (s.hom.app U y)) =
            (toSheafify JC ((Functor.const Cᵒᵖ).obj a)).app U x) →
        ∀ (W : Dᵒᵖ) (z : (L.obj T).obj.obj W),
          (@id (((constantSheaf JD CommRingCat.{u}).obj a).obj.obj W)
            ((constantRingSetComparison JC JD L kappa).hom.app a |>.hom.app W
              ((L.map s).hom.app W z))) =
            (toSheafify JD ((Functor.const Dᵒᵖ).obj a)).app W x := by
  intro A a T s hs W y
  let f : PUnit.{u + 1} ⟶ (A : Type u) := TypeCat.ofHom (fun _ ↦ a)
  let t := (constantPointTerminal JC).from T
  have hs' : s = t ≫ (constantSheaf JC (Type u)).map f ≫
      (constantCommuteCompose JC (forget CommRingCat)).inv.app A := by
    apply Sheaf.hom_ext
    ext U x
    change s.hom.app U x = _
    have hx := hs U x
    dsimp only [id_eq] at hx
    rw [hx]
    change _ = ((constantCommuteCompose JC (forget CommRingCat)).inv.app A).hom.app U
      (((constantSheaf JC (Type u)).map f).hom.app U (t.hom.app U x))
    erw [point_section JC U (t.hom.app U x), constantMap_unit, coeff_unit]
  have hn := kappa.hom.naturality f
  have hn' : L.map ((constantSheaf JC (Type u)).map f) ≫ kappa.hom.app A =
      kappa.hom.app PUnit.{u + 1} ≫ (constantSheaf JD (Type u)).map f := by
    simpa only [Functor.comp_map] using hn
  have heq : L.map s ≫ (constantRingSetComparison JC JD L kappa).hom.app A =
      L.map t ≫ kappa.hom.app PUnit.{u + 1} ≫
        (constantSheaf JD (Type u)).map f ≫
          (constantCommuteCompose JD (forget CommRingCat)).inv.app A := by
    rw [hs']
    change L.map (t ≫ (constantSheaf JC (Type u)).map f ≫
      (constantCommuteCompose JC (forget CommRingCat)).inv.app A) ≫
      (L.map ((constantCommuteCompose JC (forget CommRingCat)).hom.app A) ≫
        kappa.hom.app A ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app A) = _
    simp only [Functor.map_comp, Category.assoc]
    rw [← L.map_comp_assoc
      ((constantCommuteCompose JC (forget CommRingCat)).inv.app A)
      ((constantCommuteCompose JC (forget CommRingCat)).hom.app A),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun g ↦ L.map t ≫ g ≫ (constantCommuteCompose JD (forget CommRingCat)).inv.app A) hn'
  change (L.map s ≫ (constantRingSetComparison JC JD L kappa).hom.app A).hom.app W y = _
  rw [heq]
  change ((constantCommuteCompose JD (forget CommRingCat)).inv.app A).hom.app W
    (((constantSheaf JD (Type u)).map f).hom.app W
      ((kappa.hom.app PUnit.{u + 1}).hom.app W ((L.map t).hom.app W y))) = _
  erw [point_section JD W
    ((kappa.hom.app PUnit.{u + 1}).hom.app W ((L.map t).hom.app W y)),
    constantMap_unit, coeff_unit]


end CategoryTheory
