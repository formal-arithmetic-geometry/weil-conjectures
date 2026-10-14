module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Remaining chart ring presentation data; the geometric construction is deferred.
Source: Stacks Project, Tag 01ZR. (blueprint: new-affine-chart-section-ring-presentations-tail).

Proof: restrict the limiting affine cone to the upper tail and reindex it by
the antisymmetrization representatives. The affine pullback and section-ring
comparison supplied by the affine chart construction yield the initial ring
isomorphism and, stage by stage, the corresponding isomorphisms. Pullback
functoriality identifies their maps on sections; the displayed equations are
exactly these compatibility equations. This establishes every conjunction and
existential in the statement, including empty-chart and zero-ring cases. The
detailed geometric construction remains this named stage-3 hole for
independent completion. -/
theorem affine_chart_section_ring_presentations_tail
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    :
    let rep := (OrderEmbedding.ofAntisymmetrization
      (α := {k : I // j ≤ k})).monotone.functor
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
    let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
    let kₜ := rep.obj t
    let s := pullback.snd (Spec.map (R.map (homOfLE kₜ.property))) g
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    IsAffine ((U.pullback₁ q₀).X a) ∧
    ∃ (ρ₀ : ↑(colimit F) ≃+* Γ((U.pullback₁ q₀).X a, ⊤)),
      (∀ b, ρ₀ (r₀ (s.appTop b)) = (U.pullbackHom q₀ a).appTop b) ∧
      ∀ (x : Antisymmetrization {k : I // j ≤ k} (· ≤ ·)) (htx : t ≤ x),
        let k := (rep.obj x).val
        let hjk := (rep.obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        let Uk : (pullback f (Spec.map
          (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := U.pullback₁ q
        let V : (pullback f (c.π.app (op i))).OpenCover.{u} := Uk.pullback₁ p
        let v : V.X a ⟶ (U.pullback₁ q₀).X a := pullback.lift (V.f a)
          (Uk.pullbackHom p a ≫ U.pullbackHom q a)
          (by
            dsimp only [V]
            rw [Category.assoc, U.pullbackHom_map,
              ← Category.assoc, Uk.pullbackHom_map, Category.assoc, w])
        ∃ (ρₓ : ↑(F.obj x) ≃+* Γ((U.pullback₁ q).X a, ⊤)),
          (∀ b, ρₓ (r (s.appTop b)) = (U.pullbackHom q a).appTop b) ∧
          IsAffine (Uk.X a) ∧
          (∀ b, v.appTop (ρ₀ (r₁ b)) = (Uk.pullbackHom p a).appTop (ρₓ b)) := by sorry


end AlgebraicGeometry
