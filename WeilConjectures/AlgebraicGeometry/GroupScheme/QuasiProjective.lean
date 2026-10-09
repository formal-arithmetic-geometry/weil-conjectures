/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Reduced
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# Group schemes of finite type over a field are quasi-projective

A group scheme of finite type over a field `k` is quasi-projective over `k` (Stacks 0BF7).
Over a field, quasi-projectivity amounts to an immersion into a projective space `ℙ(α; Spec k)`
with finitely many homogeneous coordinates, and this is the form in which it is stated here.

Following Stacks 0BF7, the statement is reduced to the case of an algebraically closed field:
the base change of `G` to an algebraic closure `K` of `k` is again a group scheme of finite type,
and quasi-projectivity descends from `K` to `k`
(`AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_pullback`, Stacks 0BDE).

## Main statements

- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed`: the case of an
  algebraically closed field.
- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`: a group scheme of finite type
  over a field admits an immersion into a projective space over the field.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **Smooth group schemes of finite type over an algebraically closed field carry an ample
invertible module.** A smooth group scheme `G` of finite type over an algebraically closed field
`k` carries an invertible module `ℒ` with finitely many global sections `s i` whose non-vanishing
loci `G_{s i}` are affine and cover `G`; that is, `ℒ` is ample in the sense of Stacks 01PS.

This is the geometric core of Stacks 0BF7. One takes for `D` the complement of an affine open
neighbourhood of the identity in each connected component, which is an effective Cartier divisor
because the local rings of `G` are regular, hence factorial (Stacks 0AG0, 0BCW), and shows that
translates of `D` spread out over an étale chart define a single ample invertible module
(Stacks 0AGA, 0BEH, 01PS). -/
theorem GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [QuasiCompact G.hom] :
    ∃ (L : G.left.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ G.left.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl = ⊤ :=
  sorry

/-- **Group schemes of finite type over an algebraically closed field carry an ample invertible
module.** A group scheme `G` of finite type over an algebraically closed field `k` carries an
invertible module `ℒ` with finitely many global sections `s i` whose non-vanishing loci `G_{s i}`
are affine and cover `G`.

In characteristic zero `G` is reduced by Cartier's theorem, hence smooth; in characteristic `p`
the reduction `G_red` is a smooth group scheme, a power of the Frobenius gives a surjective affine
morphism `G ⟶ G_red`, and the ample family of `G_red`
(`AlgebraicGeometry.GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth`) pulls back
to `G`. -/
theorem GrpObj.exists_isAffineOpen_compl_support_zeroLocus [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (L : G.left.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ G.left.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl = ⊤ := by
  obtain ⟨f, -, _⟩ := GrpObj.exists_surjective_isAffineHom_reduction G
  have : QuasiCompact (GrpObj.reduction G).hom :=
    inferInstanceAs (QuasiCompact (G.left.nilradical.subschemeι ≫ G.hom))
  obtain ⟨L, _, ι, _, s, hs, hcov⟩ :=
    GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth (GrpObj.reduction G)
  obtain ⟨L', hL', s', hs', hcov'⟩ :=
    Scheme.Modules.exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom f L s hs hcov
  exact ⟨L', hL', ι, ‹_›, s', hs', hcov'⟩

/-- **Group schemes of finite type over an algebraically closed field are quasi-projective.**
A group scheme `G` of finite type over an algebraically closed field `k` admits an immersion
`G ⟶ ℙ(α; Spec k)` over `Spec k` into a projective space with finitely many homogeneous
coordinates.

`G` is separated over `k` (`AlgebraicGeometry.GrpObj.isSeparated_hom`, Stacks 047L) and carries
an ample invertible module
(`AlgebraicGeometry.GrpObj.exists_isAffineOpen_compl_support_zeroLocus`), whose sections give the
immersion (`AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_isAffineOpen`). It is the
input of `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`, used for blueprint
`lem-sc-abelian-variety-projective` and the subsection `sk-prop-av-projective`. -/
theorem GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom := by
  obtain ⟨L, _, ι, _, s, hs, hcov⟩ := GrpObj.exists_isAffineOpen_compl_support_zeroLocus G
  exact exists_isImmersion_projectiveSpace_of_isAffineOpen G.hom L s hs hcov

/-- **Group schemes of finite type over a field are quasi-projective.** A group scheme `G` of
finite type over a field `k` admits an immersion `G ⟶ ℙ(α; Spec k)` over `Spec k` into a
projective space with finitely many homogeneous coordinates.

The base change of `G` to an algebraic closure of `k` is a group scheme of finite type over an
algebraically closed field, hence quasi-projective
(`AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed`), and
quasi-projectivity descends along field extensions (Stacks 0BDE).

This is the input (Stacks 0BF7) used in the proof of blueprint `lem-sc-abelian-variety-projective`
and of the subsection `sk-prop-av-projective`. -/
@[stacks 0BF7]
theorem GrpObj.exists_isImmersion_projectiveSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let : GrpObj (Over.mk (Limits.pullback.snd G.hom g)) := Over.grpObjMkPullbackSnd
  have : LocallyOfFiniteType (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : QuasiCompact (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.hom g))
  obtain ⟨α, _, j, hj, hjG⟩ :=
    exists_isImmersion_projectiveSpace_of_isAlgClosed (Over.mk (Limits.pullback.snd G.hom g))
  exact exists_isImmersion_projectiveSpace_of_pullback G.hom j hjG

end AlgebraicGeometry
