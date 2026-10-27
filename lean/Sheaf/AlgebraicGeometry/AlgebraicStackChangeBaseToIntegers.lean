/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Viewing algebraic stacks over the integers

Source: Stacks Project, Algebraic Stacks, Tags 04X5 and 04X6; Morphisms of Stacks,
Tags 050U and 04YW (blueprint: lem-sfb-algebraic-stack-change-base-to-integers).

The total category is unchanged. The equivalence of 2-categories is expressed by
algebraicity in both directions and equivalences of the categories of morphisms of
pairs, normalized on their underlying functors and natural transformations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Composition of the projection with change of base, without changing the total category.
Source: Stacks 04X6, construction A (blueprint:
lem-sfb-algebraic-stack-change-base-to-integers). -/
abbrev moduliChangeBase {S B : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ B)
    (F : BasedCategory.{v₁, w₁} (Over S)) : BasedCategory (Over B) :=
  BasedCategory.ofFunctor (F.p ⋙ Over.map g)

/-- The same functor, regarded over the smaller base.
Source: Stacks 04X5 (blueprint: lem-sfb-algebraic-stack-change-base-to-integers). -/
abbrev moduliChangeBaseMap {S B : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ B)
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : BasedFunctor (moduliChangeBase g F) (moduliChangeBase g G) where
  toFunctor := f.toFunctor
  w := by
    change f.toFunctor ⋙ (G.p ⋙ Over.map g) = F.p ⋙ Over.map g
    rw [← Functor.assoc, f.w]

/-- The canonical identification of a scheme chart after forgetting the base.
It sends a scheme map to the very same scheme map.
Source: Stacks 04X5, preservation of presentations
(blueprint: lem-sfb-algebraic-stack-change-base-to-integers). -/
def moduliChangeBaseScheme {S B : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ B)
    (U : Over S) :
    BasedFunctor (moduliChangeBase g (discreteModuli (yoneda.obj U)))
      (discreteModuli (yoneda.obj ((Over.map g).obj U))) where
  obj x := CostructuredArrow.mk (yoneda.map ((Over.map g).map (yoneda.preimage x.hom)))
  map {x y} a := CostructuredArrow.homMk ((Over.map g).map a.left) (by
    dsimp only [CostructuredArrow.mk_hom_eq_self]
    rw [← yoneda.map_comp, ← Functor.map_comp]
    congr 2
    apply yoneda.map_injective
    simp [CostructuredArrow.w a])
  map_id x := by
    apply CostructuredArrow.hom_ext
    change (Over.map g).map (𝟙 x.left) = 𝟙 _
    simp
  map_comp a b := by
    apply CostructuredArrow.hom_ext
    change (Over.map g).map (a.left ≫ b.left) =
      (Over.map g).map a.left ≫ (Over.map g).map b.left
    simp
  w := rfl

/-- Morphisms of the pairs `(j_! F, j_! F → S)`. The full subcategory retains
natural transformations over the smaller base; their compatibility over `S` follows
from faithfulness of `Over.map g` and the displayed equality of projections.
Source: Stacks 04X5 and stacks.tex 04WV
(blueprint: lem-sfb-algebraic-stack-change-base-to-integers). -/
abbrev moduliChangeBasePairHom {S B : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ B)
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S)) :=
  ObjectProperty.FullSubcategory (fun f :
    BasedFunctor (moduliChangeBase g F) (moduliChangeBase g G) ↦
      f.toFunctor ⋙ G.p = F.p)

/-- The absolute product over the integers, with no condition on the original base.
It is the existing 2-fibre product of the structure maps of the two stacks regarded
over the integers, to the base category itself; no product over `S` is used.
Source: Stacks 050L, proof of (5)--(8)
(blueprint: lem-sfb-algebraic-stack-change-base-to-integers). -/
abbrev moduliProductOverIntegers {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S)) :
    BasedCategory (Over (AlgebraicGeometry.Spec (.of (ULift.{u} ℤ)))) :=
  moduliTwoFiberProduct
    (H := BasedCategory.ofFunctor (𝟭 (Over (AlgebraicGeometry.Spec (.of (ULift.{u} ℤ))))))
    ⟨(moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) F).p, rfl⟩
    ⟨(moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) G).p, rfl⟩

/-- The structure map to the represented `S`, modeled by its slice category.
Its underlying functor is precisely the original projection.
Source: Stacks 04X5, construction A
(blueprint: lem-sfb-algebraic-stack-change-base-to-integers). -/
def moduliChangeBaseProjection {S B : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ B)
    (F : BasedCategory.{v₁, w₁} (Over S)) :
    BasedFunctor (moduliChangeBase g F) (BasedCategory.ofFunctor (Over.map g)) where
  toFunctor := F.p
  w := rfl

/-- The absolute diagonal is the existing relative diagonal of the structure map of the
stack regarded over the integers; it sends an object to `(x, x, id)`.
Source: Stacks 050L and 04YW
(blueprint: lem-sfb-algebraic-stack-change-base-to-integers). -/
def moduliDiagonalOverIntegers {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) :
    BasedFunctor
      (moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) F)
      (moduliProductOverIntegers F F) :=
  moduliRelativeDiagonal
    (G := BasedCategory.ofFunctor (𝟭 (Over (AlgebraicGeometry.Spec (.of (ULift.{u} ℤ))))))
    ⟨(moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) F).p, rfl⟩

/-- Change of base to the integers preserves algebraicity and every given smooth
surjective scheme atlas, gives the equivalence with algebraic stacks mapping to `S`,
preserves 2-fibre products, and preserves and reflects the intrinsic qcqs predicates.
Source: Stacks 04X5, 04X6, 050U, 04YW and 050L
(blueprint: lem-sfb-algebraic-stack-change-base-to-integers).

Proof:
1. Apply lem-sfb-etale-stack-localization with base Spec Z: the total category,
   its projection to Sch/S, functors of pairs and their 2-isomorphisms are unchanged.
2. For the absolute diagonal, two objects over T may have different maps a,b to S.
   Form E = T ×_(S ×_Z S) S. An absolute isomorphism forces a = b after restriction,
   so its Isom space is the relative Isom space over E, composed with E → T.
   Use lem-sfb-space-change-base-to-integers to view this space over the integers.
   This proves the absolute algebraic-space diagonal without a separation assumption.
3. A scheme test of j_! F inherits its S-map. Its base change of a given atlas has
   the same objects, arrows and projection as the relative base change. The space
   change-of-base lemma retains its scheme charts, so smoothness and surjectivity
   agree. Conversely any absolute atlas inherits an S-map by composition.
4. For an absolute stack with a map to S, isomorphisms over an S-scheme are already
   over S since the represented S has discrete fibres. Its absolute Isom spaces
   become relative spaces by the space lemma. Thus algebraicity holds both ways.
   Construction A and B are inverse, including their morphism categories; forgetting
   the S-map changes neither underlying functors nor natural transformations.
5. A triple (x,y,alpha) in an absolute pullback has equal S-structures because alpha
   maps to an identity over S. Its triples, arrows and projections are consequently
   exactly the relative ones. This gives the comparison equivalence over the base.
6. Quasi-compactness is existence of a quasi-compact smooth atlas, so step 3 preserves
   and reflects it. Every absolute algebraic test stack mapping to the target inherits
   its S-map. Steps 4 and 5 identify all tests of quasi-compactness of a morphism.
7. The space change-of-base equivalence similarly preserves quasi-compact spaces,
   their morphisms and their relative diagonals, hence quasi-separated space maps.
8. Step 5 identifies the relative stack diagonal. Its scheme tests and space
   projections are identical by the space lemma, and step 7 identifies their qcqs.
   This proves quasi-separatedness in both directions. The absolute product and
   diagonal use the stacks over Spec Z, not the relative product over S. -/
theorem algebraicStack_changeBase_toIntegers (S : AlgebraicGeometry.Scheme.{u}) :
    (∀ (F : BasedCategory.{v₁, w₁} (Over S)), IsAlgebraicModuliStack F →
      IsAlgebraicModuliStack
        (moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) F) ∧
      (∀ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
        IsSmoothModuliAtlas F U a →
        ∃ b : BasedFunctor
          (discreteModuli (yoneda.obj
            ((Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)).obj U)))
          (moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) F),
          IsSmoothModuliAtlas _ _ b ∧
          Nonempty (ModuliTwoIso
            (moduliChangeBaseMap (AlgebraicGeometry.specULiftZIsTerminal.from S) a)
            ((moduliChangeBaseScheme (AlgebraicGeometry.specULiftZIsTerminal.from S) U).comp
              b)))) ∧
    (∀ (G : BasedCategory.{v₁, w₁}
        (Over (AlgebraicGeometry.Spec (.of (ULift.{u} ℤ)))))
      (q : G.obj ⥤ Over S),
      q ⋙ Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S) = G.p →
      (IsAlgebraicModuliStack G ↔ IsAlgebraicModuliStack (BasedCategory.ofFunctor q))) ∧
    (∀ (F : BasedCategory.{v₁, w₁} (Over S))
      (G : BasedCategory.{v₂, w₂} (Over S)),
      IsAlgebraicModuliStack F → IsAlgebraicModuliStack G →
      ∃ E : BasedFunctor F G ≌
          moduliChangeBasePairHom (AlgebraicGeometry.specULiftZIsTerminal.from S) F G,
        (∀ f : BasedFunctor F G, (E.functor.obj f).obj.toFunctor = f.toFunctor) ∧
        (∀ (f h : BasedFunctor F G) (α : f ⟶ h),
          HEq ((E.functor.map α).hom).toNatTrans α.toNatTrans)) ∧
    (∀ (F : BasedCategory.{v₁, w₁} (Over S))
      (G : BasedCategory.{v₂, w₂} (Over S))
      (H : BasedCategory.{v₃, w₃} (Over S))
      (f : BasedFunctor F H) (g : BasedFunctor G H),
      IsAlgebraicModuliStack F → IsAlgebraicModuliStack G → IsAlgebraicModuliStack H →
      ∃ e : BasedFunctor
        (moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S)
          (moduliTwoFiberProduct f g))
        (moduliTwoFiberProduct
          (moduliChangeBaseMap (AlgebraicGeometry.specULiftZIsTerminal.from S) f)
          (moduliChangeBaseMap (AlgebraicGeometry.specULiftZIsTerminal.from S) g)),
        e.toFunctor.IsEquivalence ∧
        (∀ x, (e.obj x).obj = x.obj) ∧
        (∀ (x y) (a : x ⟶ y), HEq (e.map a).hom a.hom)) ∧
    (∀ (F : BasedCategory.{v₁, w₁} (Over S)), IsAlgebraicModuliStack F →
      (IsQuasiCompactModuli F ↔ IsQuasiCompactModuli
        (moduliChangeBase (AlgebraicGeometry.specULiftZIsTerminal.from S) F))) ∧
    (∀ (F : BasedCategory.{v₁, w₁} (Over S))
      (G : BasedCategory.{v₂, w₂} (Over S)) (f : BasedFunctor F G),
      IsAlgebraicModuliStack F → IsAlgebraicModuliStack G →
      (IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₄, w₄} f ↔
        IsQuasiCompactAlgebraicModuliMap.{u, v₁, w₁, v₂, w₂, v₄, w₄}
          (moduliChangeBaseMap (AlgebraicGeometry.specULiftZIsTerminal.from S) f)) ∧
      (IsQuasiSeparatedAlgebraicModuliMap f ↔ IsQuasiSeparatedAlgebraicModuliMap
        (moduliChangeBaseMap (AlgebraicGeometry.specULiftZIsTerminal.from S) f))) := by
  sorry

end CategoryTheory
