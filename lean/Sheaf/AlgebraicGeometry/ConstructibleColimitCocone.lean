module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.ConstructibleSheaf.FinitePushforward

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Constructible-source factorization and refinement of relations recognize a
filtered colimit cocone. No constructibility assumption on the diagram is needed.

Source: Stacks Project, Tags 09Z4, 03EW(3), 03S8(3), and 03SA(3).
(blueprint: lem-weil-pbc-module-sheaf-colimit-constructible-cocone).

Proof: Form the colimit `L` of `D` in module sheaves and the comparison `t : L -> F`
induced by `ι`. For a constructible `G`, 09Z4 identifies `Hom(G,L)` with the filtered
colimit of `Hom(G,D.obj a)`. The factorization hypothesis says `Hom(G,t)` is
surjective; the refinement hypothesis says it is injective, by the usual equality
criterion for filtered colimits of sets. Constructible sheaves generate: extensions
by zero of finite free modules on affine etale objects are constructible by 03S8(3),
and the coproduct of their maps to any sheaf is epic by 03EW(3). Thus they separate
morphisms. Injectivity of all `Hom(G,t)` makes `t` monic. Surjectivity implies that
the generating epimorphism onto `F` factors through `t`, hence `t` is epic. The
category of module sheaves is abelian, so `t` is an isomorphism. Transport the
colimit cocone for `L` along this isomorphism to obtain the colimit structure on
the given cocone `Cocone.mk F ι`. -/
theorem exists_constructible_colimit_cocone
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A : Type (u + 1)) [SmallCategory A] [IsFiltered A]
    (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ι : D ⟶ (Functor.const A).obj F)
    (hfactor : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleEtaleModuleSheaf G → ∀ p : G ⟶ F,
        ∃ (a : A) (q : G ⟶ D.obj a), q ≫ ι.app a = p)
    (hrelations : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleEtaleModuleSheaf G → ∀ (a b : A)
        (p : G ⟶ D.obj a) (q : G ⟶ D.obj b),
        p ≫ ι.app a = q ≫ ι.app b →
        ∃ (c : A) (f : a ⟶ c) (g : b ⟶ c), p ≫ D.map f = q ≫ D.map g) :
    Nonempty (IsColimit (Cocone.mk F ι)) := by
  sorry

end AlgebraicGeometry.Scheme
