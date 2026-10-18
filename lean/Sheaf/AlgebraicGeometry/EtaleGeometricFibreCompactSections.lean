module

public import Sheaf.AlgebraicGeometry.CompactlySupportedSections
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Compact sections of a quasi-compact étale geometric fibre

Source: `literature/stacks-project/etale-cohomology.tex`, Tag 09Z9, assertion (1),
and Tag 0F4Y (blueprint: lem-sfb-etale-geometric-fibre-compact-sections).
This statement is revalidated for the NE stage-2 delivery.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Scheme Scheme.Hom

/-- Let `h : V ⟶ T` be separated, quasi-compact, and étale, and let `t` be a geometric
point of `T` over an algebraically closed field `Ω`. The geometric fibre is finite and its
canonical coproduct decomposition is an isomorphism. Every fibre section has proper reduced
support, and the canonical restriction-and-germ map identifies compactly supported sections
with the coproduct of the geometric stalks. The final clause gives the germ formula for the
extension by zero from a pointed étale neighbourhood.

Source: Stacks Project, Étale Cohomology, Tag 09Z9, assertion (1), and more-etale.tex,
Tag 0F4Y (blueprint: lem-sfb-etale-geometric-fibre-compact-sections).
Proof: base change preserves étaleness, separatedness and quasi-compactness; Tag 09Z9
splits the fibre over `Spec Ω` into finitely many copies of `Spec Ω`, yielding the stated
coproduct isomorphism. The clopen decomposition identifies sections with their component
germs, and the upper-star stalk comparison identifies each fibre germ with the stalk at the
corresponding point of `V`. The support is a finite union of point components and is proper
over `Spec Ω`, so every section is compactly supported and the finite coproduct map is an
isomorphism. Finally, the graph of an étale lift is clopen in the fibre product; gluing the
given section with zero off the graph gives the extension and the stated germ formula.
-/
theorem etaleGeometricFibreCompactSections
    (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (h : V ⟶ T) [IsSeparated h] [QuasiCompact h] [Etale h]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    let C := Limits.pullback h t
    let r := Limits.pullback.fst h t
    let I := Scheme.Hom.GeometricFiber h t
    Finite I ∧
      IsIso (Sigma.desc (fun v : I ↦
        Limits.pullback.lift v.1 (𝟙 (Spec (.of Ω))) (by simpa using v.2)) :
        (∐ fun _ : I ↦ Spec (.of Ω)) ⟶ Limits.pullback h t) ∧
      IsIso (compactlySupportedSections.ι A (Limits.pullback.snd h t)
        ((Etale.upperStar (ModuleCat.{u + 1} A) r).obj F) ≫
        etaleGeometricFibreRestrictionMap A h Ω t F) ∧
      (∀ (s : (Etale.sectionsFunctor (ModuleCat.{u + 1} A) C).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) r).obj F)),
        Etale.SectionHasProperSupport A
          ((Etale.upperStar (ModuleCat.{u + 1} A) r).obj F)
          (Scheme.Etale.mk (𝟙 C)) (Limits.pullback.snd h t) s) ∧
      (∀ (W : T.Etale) (w : Spec (.of Ω) ⟶ W.left)
          (lift : W.left ⟶ V) [Etale lift]
          (hw : w ≫ W.hom = t) (hlift : lift ≫ h = W.hom)
          (z : F.obj.obj (op (Scheme.Etale.mk lift))),
        let P := Limits.pullback h W.hom
        let p := Limits.pullback.fst h W.hom
        let γ := Limits.pullback.lift lift (𝟙 W.left) (by simp [hlift])
        ∃ zext : F.obj.obj (op (Scheme.Etale.mk p)),
          (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
              (x : Spec (.of Ω') ⟶ P),
            x default ∉ Set.range γ.base →
              ((Scheme.pointSmallEtale (x ≫ p)).toPresheafFiber
                (Scheme.Etale.mk p) (CategoryTheory.Over.homMk x) F.obj).hom zext = 0) ∧
          F.obj.map (MorphismProperty.Over.homMk
            (A := Scheme.Etale.mk lift) (B := Scheme.Etale.mk p) γ
              (by simp [p, γ])).op zext = z ∧
          (etaleGeometricFibreRestrictionMap A h Ω t F).hom
              ((etaleSectionPullbackToGlobal A r p
                (Limits.pullback.lift r (Limits.pullback.snd h t ≫ w)
                  (by simpa only [r, Category.assoc, hw] using
                    (Limits.pullback.condition (f := h) (g := t))))
                (by simp [p]) F).hom zext) =
              (Sigma.ι (fun v : Scheme.Hom.GeometricFiber h t ↦
                (Scheme.pointSmallEtale v.1).sheafFiber.obj F)
                ⟨w ≫ lift, by simp [hw, hlift]⟩)
                (((Scheme.pointSmallEtale (w ≫ lift)).toPresheafFiber
                  (Scheme.Etale.mk lift) (CategoryTheory.Over.homMk w) F.obj).hom z)) := by
  sorry

end AlgebraicGeometry
