/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Scalar-compatible comparison for additive first cohomology -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compare the larger-coefficient derived additive cohomology with ordinary
structure-sheaf cohomology, including its canonical scalar maps.
Source: Stacks Project, Tags 03P2 and 03FD; the coefficient-universe argument
is the separated-case finite affine open cover argument of Tag 03P2,
applied in each coefficient universe.
(blueprint: lem-sc-additive-cohomology-scalar-comparison)

Proof: Identify G sectionwise with the universe lift of the associated etale
sheaf of the unit O_C-module. The unit tensor-pullback identifications turn a
into this sheaf isomorphism; ha is precisely its naturality. Apply the natural
Ext/derived comparison to the sheaf in degree zero. C is quasi-compact and
separated: IsCurve f supplies quasi-compactness and separatedness over Spec k,
and the latter is separated over the terminal scheme. Choose a finite affine
open cover of C. All finite intersections are affine. Both the associated
etale sheaf and its coefficient lift are acyclic on these intersections by
affine quasi-coherent acyclicity in their respective coefficient universes.
Thus the Cech-to-cohomology spectral sequence has only its degree-zero row
and identifies each degree-one group with the Cech complex's first homology.
In every degree the cover tuples form a finite set. Lowering the finitely
many lifted components identifies the two cochain groups and commutes with
restrictions and alternating sums. It identifies kernels and images, hence
induces an additive equivalence of first cohomology. These comparisons are
natural in module endomorphisms: their maps act componentwise on this same
cover and commute with the differentials. No preservation of injective
objects by ULift is used. Compose with the natural etale/Zariski comparison
and the natural module/underlying-abelian comparison. Reindex Ext universes
through their Hom-in-the-derived-category descriptions, naturally in both
arguments. The result is e with codomain the source library's ordinary H^1.
For each c, the section formula identifies mu uniquely with multiplication
by the global section f^*(c). Pullback of the unit module identifies this
map on an etale object with multiplication by its pulled-back section.
The comparisons above therefore intertwine these maps. By the definition
of moduleH and moduleHOfField, the map on ordinary H^1 is precisely c-smul.
This gives the stated identity, without properness, smoothness or finiteness. -/
theorem exists_addEquiv_etaleCohomology_one_structureSheaf
    {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    let T := DerivedCategory.singleFunctor
      (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
    ∃ e : T.obj G ≃+ Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1,
      ∀ (c : k) (μ : G ⟶ G),
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) →
        ∀ x : T.obj G, e (T.map μ x) = c • e x := by
  sorry

end AlgebraicGeometry
