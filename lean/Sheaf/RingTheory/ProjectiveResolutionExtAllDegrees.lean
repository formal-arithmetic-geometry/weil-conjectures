module
public import Sheaf.RingTheory.GlobalDimension
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.RingTheory.ProjectiveResolutionExtDegree
@[expose] public section
universe u v
open CategoryTheory
namespace ModuleCat
/-- One component of Stacks 065R. Induct on the resolution bound. A bounded projective
resolution gives a long exact Ext sequence whose projective term contributes no positive
Ext; shifting along the sequence and applying the induction hypothesis yields vanishing
in every degree at least `n + 1`. Conversely, the all-degrees hypothesis includes the
degree `n + 1` case, and the kernel of a free epimorphism onto `X` inherits the shifted
vanishing needed by the induction hypothesis. Splicing the resulting shorter resolution
with that epimorphism gives a resolution of `X` of length at most `n`. The argument is
performed in `ModuleCat`; `HasExt.standard` merely chooses the standard small Ext model.
Source: Stacks Project, Algebra, Lemma 065R.
(blueprint: lem-weil-pbc-projective-resolution-ext-all-degrees). -/
theorem projective_resolution_ext_all_degrees
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    (HasProjectiveResolutionLE X n ↔
      ∀ (Y : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i →
        Subsingleton
          (@Abelian.Ext _ _ _ (HasExt.standard (ModuleCat.{max u v} R)) X Y i)) := by
  constructor
  · intro h Y i hi
    have hle : HasProjectiveResolutionLE X (i - 1) := by
      obtain ⟨P, hP⟩ := h
      refine ⟨P, fun j hj => hP j (by omega)⟩
    have hdeg := (projective_resolution_ext_degree X (i - 1)).mp hle Y
    have hi0 : 0 < i := by omega
    have heq : i - 1 + 1 = i := by omega
    rw [← heq]
    exact hdeg
  · intro h
    apply (projective_resolution_ext_degree X n).mpr
    intro Y
    exact h Y (n + 1) (by omega)
end ModuleCat
