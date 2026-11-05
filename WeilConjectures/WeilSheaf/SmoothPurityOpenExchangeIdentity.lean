module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Shriek
public import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange

/-! # The compactification exchange with identity proper part -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.ExchangeFormalism

variable {C : Type*} [Category C] {O : MorphismProperty C}
  (F : ExchangeFormalism C O) {X Y X' Y' : C}
  (i : X ⟶ Y) (i' : X' ⟶ Y') [Fact (O i)] [Fact (O i')]
  (g' : X' ⟶ X) (g : Y' ⟶ Y) (wi : g' ≫ i = i' ≫ g)
  (wp : g ≫ 𝟙 Y = 𝟙 Y' ≫ g) [IsIso (F.baseChange g' i' i g wi).natTrans]

/-- With identity proper parts, compact-support exchange is inverse open exchange,
after removing the identity pushforwards. -/
theorem purity_shriekBaseChange_id_app (K : F.obj X) :
    (F.shriekBaseChange i (𝟙 Y) i' (𝟙 Y') g' g g wi wp).natTrans.app K ≫
        (F.pfId Y').hom.app ((F.sh i').obj ((F.pb g').obj K)) ≫
        (F.baseChange g' i' i g wi).natTrans.app K =
      (F.pb g).map ((F.pfId Y).hom.app ((F.sh i).obj K)) := by
  rw [shriekBaseChange_app]
  simp only [Category.assoc, NatTrans.naturality_assoc, Functor.id_map,
    IsIso.inv_hom_id, Category.comp_id]
  exact F.pfBaseChange_id_vert_app g wp ((F.sh i).obj K)

end CategoryTheory.ExchangeFormalism
