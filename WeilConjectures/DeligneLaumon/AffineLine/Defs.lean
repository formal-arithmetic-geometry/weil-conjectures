/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.WeilSheaf.Defs

/-!
# Lisse Weil sheaves on a dense open of the affine line

This file fixes the conventions of the Deligne–Laumon affine-line estimate
(`WeilConjectures.DeligneLaumon.AffineLine.Upper`) and of its auxiliary statements, following
the blueprint subsection `sk-d-dl-a1-setup`. The `ℓ`-adic formalism they are phrased against is
the provisional interface of `WeilConjectures.WeilSheaf.Defs`; what this block owns is the two
conditions on a lisse Weil sheaf on a dense open of the affine line, and the bundling of that
situation.

The affine line `A₀ = 𝔸¹_{k₀}` is `AlgebraicGeometry.affineLine k₀`, and the dual affine line
`A'₀` of the Fourier transform is another copy of it.

Both conditions are phrased without the geometric fundamental group, which does not exist in
the repository yet. Geometric constancy asks that the underlying étale sheaf on the geometric
fiber `U ⊗ k` be constant. Being unramified at infinity asks that the sheaf extend to a lisse
Weil sheaf on an open neighbourhood of `∞` in `ℙ¹_{k₀}`, for an open immersion `𝔸¹ ↪ ℙ¹` of
`k₀`-schemes; it is stated existentially, so that no compactification has to be constructed.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant`: trivial geometric monodromy.
- `AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`: trivial inertia at `∞ ∈ ℙ¹`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`: a dense open immersion `j : U₀ ↪ 𝔸¹_{k₀}`
  together with a lisse Weil sheaf on `U₀`, with its direct image, its extension by zero, its
  boundary sheaf and its curve perverse middle extension.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section Over

variable {S P : Scheme.{u}}

/-- The structure of `S`-scheme on an open `V` of an `S`-scheme `P`, through `V ↪ P`. It is not
an instance, since `V` is also canonically over `P`. -/
@[implicit_reducible]
noncomputable def Scheme.Opens.overOfOver (V : P.Opens) (S : Scheme.{u}) [P.Over S] :
    V.toScheme.Over S :=
  ⟨V.ι ≫ (P ↘ S)⟩

lemma Scheme.Opens.isOver_ι_overOfOver [P.Over S] (V : P.Opens) :
    letI := V.overOfOver S
    V.ι.IsOver S :=
  letI := V.overOfOver S
  ⟨rfl⟩

variable {U V : Scheme.{u}} [U.Over S]

/-- The structure of `S`-scheme on the fibre product `U ×_P V` of a morphism `f : U ⟶ P` from an
`S`-scheme, through its first projection. -/
@[implicit_reducible]
noncomputable def Scheme.pullbackOverOfFst (f : U ⟶ P) (g : V ⟶ P) (S : Scheme.{u})
    [U.Over S] : (Limits.pullback f g).Over S :=
  ⟨Limits.pullback.fst f g ≫ (U ↘ S)⟩

lemma Scheme.isOver_fst_pullbackOverOfFst (f : U ⟶ P) (g : V ⟶ P) :
    letI := Scheme.pullbackOverOfFst f g S
    (Limits.pullback.fst f g).IsOver S :=
  letI := Scheme.pullbackOverOfFst f g S
  ⟨rfl⟩

lemma Scheme.isOver_snd_pullbackOverOfFst [P.Over S] [V.Over S] (f : U ⟶ P) (g : V ⟶ P) [f.IsOver S]
    [g.IsOver S] :
    letI := Scheme.pullbackOverOfFst f g S
    (Limits.pullback.snd f g).IsOver S := by
  let := Scheme.pullbackOverOfFst f g S
  constructor
  change _ = Limits.pullback.fst f g ≫ (U ↘ S)
  rw [← comp_over g S, ← Limits.pullback.condition_assoc, comp_over f S]

end Over

namespace WeilSheaf

section Infinity

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf is *geometrically constant* if the geometric fundamental group `π₁(U ⊗ k)`
acts trivially on it, i.e. if its underlying étale sheaf on the geometric fiber `Ū = U ⊗ k` is
constant; its Frobenius module may still be nontrivial.
(blueprint: `sk-d-dl-a1-setup`) -/
def IsGeometricallyConstant (F : WeilSheaf k₀ l U) : Prop :=
  Sheaf.IsConstant (U ↘ Spec (CommRingCat.of k₀)).geometricFiber.smallEtaleTopology F.obj.carrier

/-- A lisse Weil sheaf `F` on an open `U₀` of the affine line is *unramified at infinity* if the
inertia group at `∞ ∈ ℙ¹` acts trivially on its geometric generic fibre. We state the equivalent
condition that `F` extends to a lisse Weil sheaf on an open neighbourhood of `∞` in `ℙ¹`: for
some open immersion `ι : 𝔸¹ ↪ ℙ¹` of `k₀`-schemes, whose complement is the point `∞`, there are
an open `V ⊆ ℙ¹` containing `∞` and a lisse Weil sheaf `G` on `V` whose restriction to
`U₀ ∩ V = U₀ ×_{ℙ¹} V` is isomorphic to that of `F`.
(blueprint: `sk-d-dl-a1-setup`) -/
def IsUnramifiedAtInfinity (F : WeilSheaf k₀ l U) (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] : Prop :=
  ∃ (ι : affineLine k₀ ⟶ ProjectiveLine (Spec (CommRingCat.of k₀))) (_ : IsOpenImmersion ι)
    (_ : ι.IsOver (Spec (CommRingCat.of k₀)))
    (V : (ProjectiveLine (Spec (CommRingCat.of k₀))).Opens),
    (Set.range ι.base)ᶜ ⊆ V ∧
      letI := V.overOfOver (Spec (CommRingCat.of k₀))
      letI := Scheme.pullbackOverOfFst (j ≫ ι) V.ι (Spec (CommRingCat.of k₀))
      haveI := V.isOver_ι_overOfOver (S := Spec (CommRingCat.of k₀))
      haveI := Scheme.isOver_fst_pullbackOverOfFst (S := Spec (CommRingCat.of k₀)) (j ≫ ι) V.ι
      haveI := Scheme.isOver_snd_pullbackOverOfFst (S := Spec (CommRingCat.of k₀)) (j ≫ ι) V.ι
      ∃ G : WeilSheaf k₀ l V.toScheme, G.IsLisse ∧
        Nonempty ((WeilSheaf.upperStar (Limits.pullback.snd (j ≫ ι) V.ι)).obj G ≅
          (WeilSheaf.upperStar (Limits.pullback.fst (j ≫ ι) V.ι)).obj F)

end Infinity

/-- The standing situation of the affine-line estimate: a dense open immersion
`j : U₀ ↪ 𝔸¹_{k₀}` together with a lisse Weil `ℚ̄_ℓ`-sheaf on `U₀`. Bundling the data avoids
carrying six instance arguments through every statement, and makes the existential statements
of the block — which produce a new dense open of the dual line — readable. -/
structure LisseOnDenseOpen (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] where
  /-- The dense open subscheme `U₀`. -/
  U : Scheme.{u}
  [overBase : U.Over (Spec (CommRingCat.of k₀))]
  /-- The open immersion `j : U₀ ↪ 𝔸¹_{k₀}`. -/
  j : U ⟶ affineLine k₀
  [isOpenImmersion : IsOpenImmersion j]
  [isOver : j.IsOver (Spec (CommRingCat.of k₀))]
  [isDominant : IsDominant j]
  /-- The lisse Weil sheaf on `U₀`. -/
  sheaf : WeilSheaf k₀ l U
  /-- The sheaf is lisse. -/
  lisse : sheaf.IsLisse

namespace LisseOnDenseOpen

attribute [instance] overBase isOpenImmersion isOver isDominant

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (D : LisseOnDenseOpen k₀ l)

/-- The sheaf of the datum is unramified at infinity. -/
def IsUnramifiedAtInfinity : Prop := D.sheaf.IsUnramifiedAtInfinity D.j

/-- The sheaf of the datum is geometrically constant. -/
def IsGeometricallyConstant : Prop := D.sheaf.IsGeometricallyConstant

/-- The ordinary direct image `j_*M` of the datum, a Weil sheaf on the whole affine line. -/
noncomputable def directImage : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.directImage D.j).obj D.sheaf

/-- The extension by zero `j_!M` of the datum. -/
noncomputable def extensionByZero : WeilSheaf k₀ l (affineLine k₀) :=
  (WeilSheaf.extensionByZero D.j).obj D.sheaf

/-- The curve perverse middle extension `j_{!*}(M[1]) = (j_*M)[1]` of the datum. -/
noncomputable def middleExtension : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧

/-- The boundary sheaf `B = j_*M / j_!M`: the cokernel of the canonical map `j_!M → j_*M`, a
punctual sheaf supported on the finite complement of `U₀`. -/
noncomputable def boundarySheaf : WeilSheaf k₀ l (affineLine k₀) :=
  Limits.cokernel ((WeilSheaf.extensionByZeroToDirectImage D.j).app D.sheaf)

/-- The shifted zero extension `j_!M[1]`, a curve perverse sheaf. -/
noncomputable def shiftedExtensionByZero : WeilComplex k₀ l (affineLine k₀) :=
  (WeilSheaf.toComplex.obj D.extensionByZero)⟦(1 : ℤ)⟧

end LisseOnDenseOpen

end WeilSheaf

end AlgebraicGeometry
