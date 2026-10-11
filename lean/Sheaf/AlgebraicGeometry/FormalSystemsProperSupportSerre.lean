import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Serre subcategories of coherent formal modules with proper support

Source: Stacks Project, Cohomology of Schemes, Lemma 0CYV
(blueprint: lem-weil-pbc-formal-systems-proper-support-serre).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The two full subcategories of coherent formal modules in Lemma 0CYV are Serre
subcategories.  The proof uses the support and annihilator calculations from the
node proof, together with abelianity of `CoherentFormalModule`.
Source: Stacks Project, Cohomology of Schemes, Lemma 0CYV.
(blueprint: lem-weil-pbc-formal-systems-proper-support-serre).
Proof: supports in a short exact sequence are the union of the outer supports;
proper closed subsets and finite unions remain proper.  For the second class,
annihilators pass to subobjects and quotients, while extensions are annihilated
by the product ideal and the corresponding scheme-theoretic union. -/
theorem formalSystems_properSupport_serre
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
    (I : X.IdealSheafData) :
    Nonempty (Abelian (@CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I)) ∧
    ∀ [Ab : Abelian (@CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I)],
      ObjectProperty.IsSerreClass
        (fun M : @CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I ↦
          Scheme.Modules.HasSupportProperOver f (M.obj.obj (op 0))) ∧
      ObjectProperty.IsSerreClass
        (fun M : @CoherentFormalModule X (isNoetherian_of_locallyOfFiniteType f) I ↦
          ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
            IsProper (i ≫ f) ∧
            ∀ n : ℕ, IsZero (Scheme.idealModuleProduct i.ker.toModulesι
              (M.obj.obj (op n)))) := by
  sorry

end AlgebraicGeometry
