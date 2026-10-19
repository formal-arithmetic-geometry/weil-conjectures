module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible

@[expose] public section

/-!
# Sections vanishing on a closed subscheme

Source: Stacks Project, varieties.tex, Tag 0FD5, lemma-generate-over-complement
(blueprint: lem-zl-bertini-sections).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/--
For a proper scheme over a field and an ample invertible module, sections vanishing on a
closed subscheme eventually generate on its complement and define an immersion into projective
space. The kernel is represented as a `k`-submodule, and a finite basis of it supplies the
homogeneous coordinates.

Source: Stacks Project, varieties.tex, Tag 0FD5, lemma-generate-over-complement
(blueprint: lem-zl-bertini-sections).

Proof: Let `U` be the open complement of the closed subscheme. Coherence of its ideal sheaf and
Serre's global-generation theorem identify the kernel of restriction with sections generating the
restriction of the tensor powers to `U`. Finite-dimensionality of global sections supplies a
finite basis. The morphism classified by the restricted basis sections is an immersion on each
standard affine chart, by the projective embedding argument of Tag 0FD5; the charts cover `U`,
so the morphism is an immersion.
-/
theorem exists_eventual_immersion_vanishingSections
    (k : Type u) [Field k] {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (hL : IsAmple (Y ↘ Spec (.of k)) L)
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    ∃ (n₀ : ℕ) (U : Y.Opens),
      (∀ y : Y, y ∈ U ↔ y ∉ Set.range i.base) ∧
      ∀ (n : ℕ), n₀ ≤ n →
        letI : Module k Γ(L.tensorPow n, ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (Y ↘ Spec (CommRingCat.of k)).appTop).hom
        ∃ (V : Submodule k Γ(L.tensorPow n, ⊤))
          (I : Type u) (_hI : Finite I) (s : I → (L.tensorPow n).sections)
          (t : I → ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n)).sections),
          (∀ v : Γ(L.tensorPow n, ⊤),
            v ∈ V ↔ (AlgebraicGeometry.pullbackΓ i (L.tensorPow n)) v = 0) ∧
          Submodule.span k (Set.range (fun j : I ↦
            (s j).val (Opposite.op ⊤)) : Set Γ(L.tensorPow n, ⊤)) = V ∧
          LinearIndependent (M := Γ(L.tensorPow n, ⊤)) k
            (fun j : I ↦ (s j).val (Opposite.op ⊤)) ∧
          (∀ j : I, (t j).val (Opposite.op ⊤) =
            (AlgebraicGeometry.pullbackΓ U.ι (L.tensorPow n))
              ((s j).val (Opposite.op ⊤))) ∧
          ∃ (ht : Epi ((SheafOfModules.freeHomEquiv
            ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n))).symm t)),
            IsImmersion (@ProjectiveSpace.homOfGeneratingSections I _ U.toScheme
              (Spec (.of k)) (U.ι ≫ (Y ↘ Spec (.of k)))
              ((Scheme.Modules.pullback U.ι).obj (L.tensorPow n)) inferInstance t ht)
    := by
  sorry

end AlgebraicGeometry
