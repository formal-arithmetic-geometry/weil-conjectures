module
public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- One component of Stacks 065R. The induction on `n` starts at `n = 0`, where a
resolution of length zero is equivalent to projectivity and the Ext-one criterion gives
vanishing in every positive degree. For the successor step, take the kernel of a
projective epimorphism onto `X`; its resolution bound drops by one. The contravariant
long exact Ext sequence for the resulting short exact sequence identifies the relevant
Ext group of `X` with a neighboring Ext group of the kernel, while Ext of the projective
term vanishes. This proves the forward implication. Conversely, choose the canonical
free module surjecting onto `X`; the same long exact sequence and the vanishing
hypothesis give the required vanishing for the kernel, so the induction hypothesis
provides its shorter resolution, which is spliced with the free epimorphism. The
construction is carried out in `ModuleCat` and uses `HasExt.standard` only to select the
standard small Ext model.
Source: Stacks Project, Algebra, Lemma 065R.
(blueprint: lem-weil-pbc-projective-resolution-ext-degree). -/
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ Y : ModuleCat.{max u v} R,
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y (n + 1))) := by
  sorry
end ModuleCat
