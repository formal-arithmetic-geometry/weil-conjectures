/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

/-!
# Split presentations of a pro-etale constant trivialization

The overlap isomorphism is stated explicitly. Its cocycle is expressed using the
recorded scheme descent datum, whose transport is required to preserve the same
sections. Thus its overlap isomorphism is the unique one already specified.

## References

* Stacks Project, Tags 098Z, 03P5, 03YW and 0AP6.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The codiagonal of the coproduct of copies of a scheme (Stacks, Tag 03YW). -/
noncomputable def proetaleSplitCodiagonal (V : Scheme.{u}) (S : Type w)
    [Small.{u} S] : (∐ fun _ : S ↦ V) ⟶ V :=
  Sigma.desc (fun _ : S ↦ 𝟙 V)

/-- Forget a localized pro-etale object to its underlying scheme over the cover
(Stacks, Tag 098Z). -/
def proetaleSliceToOver {X V : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p] :
    Over (Scheme.ProEt.mk p) ⥤ Over V :=
  Over.post (Scheme.ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)

/-- The first overlap projection as a morphism in the small pro-etale site
(Stacks, Tag 023V). -/
noncomputable def proetaleSplitOverlapFirst {X V : Scheme.{u}} (p : V ⟶ X)
    [WeaklyEtale p] :
    Scheme.ProEt.mk (pullback.fst p p ≫ p) ⟶ Scheme.ProEt.mk p :=
  MorphismProperty.Over.homMk (pullback.fst p p) rfl

/-- The second overlap projection as a morphism in the small pro-etale site
(Stacks, Tag 023V). -/
noncomputable def proetaleSplitOverlapSecond {X V : Scheme.{u}} (p : V ⟶ X)
    [WeaklyEtale p] :
    Scheme.ProEt.mk (pullback.fst p p ≫ p) ⟶ Scheme.ProEt.mk p :=
  MorphismProperty.Over.homMk (pullback.snd p p) (pullback.condition (f := p) (g := p)).symm

/-- The point in the labelled component of a split presentation (Stacks, Tag 03YW). -/
noncomputable def proetaleSplitLabel {X V : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p]
    (S : Type w) [Small.{u} S] (W : Over (Scheme.ProEt.mk p)) (s : S) :
    (proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S) :=
  Over.homMk (((proetaleSliceToOver p).obj W).hom ≫ Sigma.ι (fun _ : S ↦ V) s)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k : V ⟶ V ↦ ((proetaleSliceToOver p).obj W).hom ≫ k)
        (Sigma.ι_comp_desc (fun _ : S ↦ 𝟙 V) s)).trans (Category.comp_id _)))

/-- The representability and overlap/descent-data part of the split presentation: natural
bijections `rho` from maps over `V` into the labelled coproduct to the sections of `F`,
normalized on labels by `e`, the unique overlap isomorphism matching the two `rho`, and a
transport-form scheme descent datum preserving `rho`
(Stacks, Tags 098Z, 03P5, 03YW and 001P). -/
def proetaleConstantSplitDescentData {X V : Scheme.{u}} (p : V ⟶ X)
    [QuasiCompact p] [Surjective p] [WeaklyEtale p] [IsAffine V]
    (S : Type w) [Small.{u} S] [UnivLE.{u + 1, w}]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (e : F.over (Scheme.ProEt.mk p) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
        (Type w)).obj S) : Prop :=
  ∃ rho : ∀ W : Over (Scheme.ProEt.mk p),
      ((proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)) ≃
        F.obj.obj (op W.left),
    (∀ (W W' : Over (Scheme.ProEt.mk p)) (g : W' ⟶ W)
        (f : (proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)),
      rho W' ((proetaleSliceToOver p).map g ≫ f) =
        F.obj.map g.left.op (rho W f)) ∧
    (∀ (W : Over (Scheme.ProEt.mk p)) (s : S),
      rho W (proetaleSplitLabel p S W s) =
        e.inv.hom.app (op W)
          ((toSheafify ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
            ((Functor.const (Over (Scheme.ProEt.mk p))ᵒᵖ).obj S)).app (op W) s)) ∧
    (∃! alpha :
        (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S)) ≅
          (Over.pullback (pullback.snd p p)).obj
            (Over.mk (proetaleSplitCodiagonal V S)),
      ∀ (W : Over (Scheme.ProEt.mk (pullback.fst p p ≫ p)))
        (f : (proetaleSliceToOver (pullback.fst p p ≫ p)).obj W ⟶
          (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S))),
        rho ((Over.map (proetaleSplitOverlapFirst p)).obj W)
          (((Over.mapPullbackAdj (pullback.fst p p)).homEquiv _ _).symm f) =
        rho ((Over.map (proetaleSplitOverlapSecond p)).obj W)
          (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv _ _).symm
            (f ≫ alpha.hom))) ∧
    (∃ D : Over.DescentDatum p (Over.mk (proetaleSplitCodiagonal V S)),
      ∀ (W : X.ProEt) (a b : W ⟶ Scheme.ProEt.mk p)
        (f : Over.mk a.left ⟶ Over.mk (proetaleSplitCodiagonal V S)),
        rho (Over.mk b)
          (D.transport a.left b.left
            ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
        rho (Over.mk a) f)

/-- The representability and overlap/descent-data part of the split presentation
(Stacks, Tags 098Z, 03P5, 03YW and 001P). -/
theorem proetaleConstantSplitDescentData_proof {X V : Scheme.{u}} (p : V ⟶ X)
    [QuasiCompact p] [Surjective p] [WeaklyEtale p] [IsAffine V]
    (S : Type w) [Small.{u} S] [UnivLE.{u + 1, w}]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (e : F.over (Scheme.ProEt.mk p) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
        (Type w)).obj S) : proetaleConstantSplitDescentData p S F e := by
  sorry

/-- The split codiagonal is separated, etale, surjective for nonempty labels, and
ind-quasi-affine (Stacks, Tags 03YW and 0AP6). -/
theorem proetaleConstantSplitDescentGeometry {V : Scheme.{u}} (S : Type w)
    [Small.{u} S] [IsAffine V] :
    IsSeparated (proetaleSplitCodiagonal V S) ∧
      Etale (proetaleSplitCodiagonal V S) ∧
      (Nonempty S → Surjective (proetaleSplitCodiagonal V S)) ∧
      (∀ (B : V.Opens), IsAffineOpen B →
        ∀ (U : ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme.Opens),
          IsCompact (U : Set ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme) →
            U.toScheme.IsQuasiAffine) := by
  sorry

/-- A constant trivialization gives natural split scheme presentations, a unique
matching overlap isomorphism and its scheme descent cocycle. The codiagonal is
separated, etale, surjective for nonempty labels, and ind-quasi-affine
(Stacks, Tags 098Z, 03P5, 03YW, 001P, 023V and 0AP6). -/
theorem proetaleConstantSplitDescent {X V : Scheme.{u}} (p : V ⟶ X)
    [QuasiCompact p] [Surjective p] [WeaklyEtale p] [IsAffine V]
    (S : Type w) [Small.{u} S] [UnivLE.{u + 1, w}]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (e : F.over (Scheme.ProEt.mk p) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
        (Type w)).obj S) :
    (∃ rho : ∀ W : Over (Scheme.ProEt.mk p),
        ((proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)) ≃
          F.obj.obj (op W.left),
      (∀ (W W' : Over (Scheme.ProEt.mk p)) (g : W' ⟶ W)
          (f : (proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)),
        rho W' ((proetaleSliceToOver p).map g ≫ f) =
          F.obj.map g.left.op (rho W f)) ∧
      (∀ (W : Over (Scheme.ProEt.mk p)) (s : S),
        rho W (proetaleSplitLabel p S W s) =
          e.inv.hom.app (op W)
            ((toSheafify ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
              ((Functor.const (Over (Scheme.ProEt.mk p))ᵒᵖ).obj S)).app (op W) s)) ∧
      (∃! alpha :
          (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S)) ≅
            (Over.pullback (pullback.snd p p)).obj
              (Over.mk (proetaleSplitCodiagonal V S)),
        ∀ (W : Over (Scheme.ProEt.mk (pullback.fst p p ≫ p)))
          (f : (proetaleSliceToOver (pullback.fst p p ≫ p)).obj W ⟶
            (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S))),
          rho ((Over.map (proetaleSplitOverlapFirst p)).obj W)
            (((Over.mapPullbackAdj (pullback.fst p p)).homEquiv _ _).symm f) =
          rho ((Over.map (proetaleSplitOverlapSecond p)).obj W)
            (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv _ _).symm
              (f ≫ alpha.hom))) ∧
      (∃ D : Over.DescentDatum p (Over.mk (proetaleSplitCodiagonal V S)),
        ∀ (W : X.ProEt) (a b : W ⟶ Scheme.ProEt.mk p)
          (f : Over.mk a.left ⟶ Over.mk (proetaleSplitCodiagonal V S)),
          rho (Over.mk b)
            (D.transport a.left b.left
              ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
          rho (Over.mk a) f)) ∧
    IsSeparated (proetaleSplitCodiagonal V S) ∧
    Etale (proetaleSplitCodiagonal V S) ∧
    (Nonempty S → Surjective (proetaleSplitCodiagonal V S)) ∧
    (∀ (B : V.Opens), IsAffineOpen B →
      ∀ (U : ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme.Opens),
        IsCompact (U : Set ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme) →
          U.toScheme.IsQuasiAffine) := by
  classical
  exact ⟨by simpa [proetaleConstantSplitDescentData] using
      proetaleConstantSplitDescentData_proof p S F e,
    proetaleConstantSplitDescentGeometry S⟩

end AlgebraicGeometry
