/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Effective gluing of an étale framed line

Source: Stacks Project, Descent, Tags 03DX (2), 023T and 05VG
(blueprint: lem-trf-etale-framed-line-effective-gluing).

The localized site `Over U` presents the small étale site of `U.left`.
Products in `X.Etale` present scheme fibre products over `X`. The associated
additive sheaf is the recorded tensor-section sheaf; linearity below equips its
isomorphism with exactly the specified module-sheaf meaning.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Pull an overlap unit back to an arbitrary étale test scheme.
Source: Stacks, Descent, Tag 03DX (2), the transition functions in the descent datum
(blueprint: lem-trf-etale-framed-line-effective-gluing). -/
noncomputable def trfOverlapValue {X : Scheme.{u}} {U V W : X.Etale}
    (f : W ⟶ U) (h : W ⟶ V) (g : Γ((Limits.prod U V).left, ⊤)ˣ) : Γ(W.left, ⊤) :=
  (Limits.prod.lift f h).left.appTop (g : Γ((Limits.prod U V).left, ⊤))

/-- The pullback of an ordinary frame to a test scheme, with canonical tensor
composition and tensor-unit identifications. Its global-section map is precisely
`epsilon A(lambda) beta`, without choosing any comparison isomorphism.
Source: Stacks, Descent, Tags 03DX (2), 03LC (1)
(blueprint: lem-trf-etale-framed-line-effective-gluing). -/
noncomputable def trfPulledFrame {X : Scheme.{u}} {U W : X.Etale} (L : X.Modules)
    (lam : (Modules.tensorPullback U.hom).obj L ≅ SheafOfModules.unit U.left.ringCatSheaf)
    (f : W ⟶ U) :
    (Modules.tensorPullback W.hom).obj L ≅ SheafOfModules.unit W.left.ringCatSheaf :=
  eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj L) f.w.symm) ≪≫
    (Modules.tensorPullbackSectionComp f.left U.hom).app L ≪≫
    (Modules.tensorPullback f.left).mapIso lam ≪≫ (@asIso W.left.Modules inferInstance _ _
      (Modules.tensorPullbackObjUnitToUnit f.left)
      (Modules.tensorPullbackObjUnitToUnit_isIso f.left).1)

/-- An arbitrary jointly surjective étale family with the prescribed frames and
normalized transition units descends to an ordinary invertible module. Its associated
sheaf is uniquely isomorphic to the given sheaf with exactly these local maps.

Source: Stacks Project, Descent, Tag 03DX (2),
`proposition-equivalence-quasi-coherent`, proof; Tag 023T,
`proposition-fpqc-descent-quasi-coherent`; Tag 05VG,
`lemma-equivalence-quasi-coherent-properties`, rank one
(blueprint: lem-trf-etale-framed-line-effective-gluing).

Proof:
1. Give the trivial ordinary modules descent arrows multiplication by `g_ab` inverse.
   The cocycle and diagonal equations give a descent datum, with the arrow direction
   of `lem-pc-fpqc-descent`.
2. The arbitrary étale covering is fpqc by `lem-weil-pbc-fpqc-finer-than-etale`.
   Clause (3) of `lem-pc-fpqc-descent` gives an ordinary invertible L and frames
   lambda_a. Descent compatibility reads lambda_a = g_ab lambda_b.
3. Use the unit and composition comparisons of
   `lem-trf-etale-line-sections-normalized-comparisons`. The tensor-unit formula
   sends multiplication by g to multiplication by its pullback, so the local maps
   t_a A(lambda_a) agree at every object of each overlap site.
4. For W and s glue these local images on W times_X U_a using the sheaf equalizer.
   Uniqueness proves restriction naturality, additivity and scalar linearity and
   identifies the restriction of the glued map with every prescribed local map.
5. Glue the local inverse maps by the same equalizer argument. Their composites
   restrict to identities, hence are identities. Separatedness proves uniqueness
   of the global isomorphism and both displayed sectionwise characterizations.
No quasi-compactness, separatedness or nonempty-cover assumption is used. -/
theorem etale_framed_line_effective_gluing
    (X : Scheme.{u}) (G : ringedSiteModules.{u} (Modules.smallEtaleModuleRing X))
    {I : Type v} (U : I → X.Etale)
    (hcover : ∀ x : X, ∃ (a : I) (y : (U a).left), (U a).hom y = x)
    (t : ∀ a : I,
      SheafOfModules.unit ((Modules.smallEtaleModuleRing X).over (U a)) ≅ G.over (U a))
    (g : ∀ a b : I, Γ((Limits.prod (U a) (U b)).left, ⊤)ˣ)
    (hframes : ∀ (a b : I) (W : X.Etale) (f : W ⟶ U a) (h : W ⟶ U b)
      (r : Γ(W.left, ⊤)),
      (t b).hom.val.app (op (Over.mk h)) r =
        (t a).hom.val.app (op (Over.mk f)) (trfOverlapValue f h (g a b) * r))
    (hcocycle : ∀ (a b c : I) (W : X.Etale)
      (f : W ⟶ U a) (h : W ⟶ U b) (k : W ⟶ U c),
      trfOverlapValue f h (g a b) * trfOverlapValue h k (g b c) =
        trfOverlapValue f k (g a c))
    (hdiag : ∀ a : I, trfOverlapValue (𝟙 (U a)) (𝟙 (U a)) (g a a) = 1) :
    ∃ (L : X.Modules) (hL : L.IsInvertible)
      (lam : ∀ a : I, (Modules.tensorPullback (U a).hom).obj L ≅
        SheafOfModules.unit (U a).left.ringCatSheaf),
      (∀ (a b : I) (W : X.Etale) (f : W ⟶ U a) (h : W ⟶ U b)
        (s : Γ((Modules.tensorPullback W.hom).obj L, ⊤)),
        (trfPulledFrame L (lam a) f).hom.app ⊤ s =
          trfOverlapValue f h (g a b) *
            (@id (Γ(W.left, ⊤)) ((trfPulledFrame L (lam b) h).hom.app ⊤ s))) ∧
      ∃! e : (@Modules.etaleTensorSectionsSheaf _ L
          (@Modules.IsInvertible.isQuasicoherent _ L hL)) ≅
          (SheafOfModules.toSheaf (Modules.smallEtaleModuleRing X)).obj G,
        (∀ (W : X.Etale) (r : Γ(W.left, ⊤))
          (s : Γ((Modules.tensorPullback W.hom).obj L, ⊤)),
          e.hom.hom.app (op W) ((((Modules.tensorPullback W.hom).obj L).smul r).hom s) =
            r • (@id (G.val.obj (op W)) (e.hom.hom.app (op W) s))) ∧
        (∀ (a : I) (W : X.Etale) (f : W ⟶ U a)
          (s : Γ((Modules.tensorPullback W.hom).obj L, ⊤)),
          e.hom.hom.app (op W) s =
            (t a).hom.val.app (op (Over.mk f)) ((trfPulledFrame L (lam a) f).hom.app ⊤ s)) ∧
        (∀ (a b : I) (W : X.Etale) (f : W ⟶ U a) (h : W ⟶ U b)
          (s : Γ((Modules.tensorPullback W.hom).obj L, ⊤)),
          (t a).hom.val.app (op (Over.mk f)) ((trfPulledFrame L (lam a) f).hom.app ⊤ s) =
            (t b).hom.val.app (op (Over.mk h)) ((trfPulledFrame L (lam b) h).hom.app ⊤ s)) ∧
        (∀ (W : X.Etale) (s : Γ((Modules.tensorPullback W.hom).obj L, ⊤))
          (y : G.val.obj (op W)),
          (∀ a : I,
            G.val.map (Limits.prod.fst (X := W) (Y := U a)).op y =
              (t a).hom.val.app (op (Over.mk (Limits.prod.snd (X := W) (Y := U a))))
                ((trfPulledFrame L (lam a) (Limits.prod.snd (X := W) (Y := U a))).hom.app ⊤
                  (Modules.etaleTensorSectionsRestriction L
                    (Limits.prod.fst (X := W) (Y := U a)) s))) ↔
            y = e.hom.hom.app (op W) s) ∧
        (∀ (W : X.Etale) (y : G.val.obj (op W))
          (s : Γ((Modules.tensorPullback W.hom).obj L, ⊤)),
          (∀ a : I,
            Modules.etaleTensorSectionsRestriction L (Limits.prod.fst (X := W) (Y := U a)) s =
              (trfPulledFrame L (lam a) (Limits.prod.snd (X := W) (Y := U a))).inv.app ⊤
                ((t a).inv.val.app (op (Over.mk (Limits.prod.snd (X := W) (Y := U a))))
                  (G.val.map (Limits.prod.fst (X := W) (Y := U a)).op y))) ↔
            s = e.inv.hom.app (op W) y) := by
  sorry

end AlgebraicGeometry.Scheme
