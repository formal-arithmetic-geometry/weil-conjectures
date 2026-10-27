/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.SNCFiniteFibreData
public import Mathlib.Algebra.Category.ModuleCat.AB

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary

/-!
# Finite tame sheaves are closed under finite scalar extension

Source: ILO IX Proposition 2.1, printed pages 133--134; Bhatt--Scholze Section 5.1
(blueprint: lem-sfb-snc-finite-tame-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

/-- Only the geometric closure assertion for scalar extension. The canonical stalk
comparison and its equivariance are separate from this statement.
Source: ILO IX Proposition 2.1, pp.133--134; Bhatt--Scholze Section 5.1
(blueprint: lem-sfb-snc-finite-tame-scalar-extension).

Proof: The finite tame root-model and universal-residual root-splitting lemmas make M
finite constant on a finite root level after passing to H. Finite operations on a
connected splitting give its constant fibre the induced R-module structure. Left scalar
extension commutes with inverse image and with constants by the two adjunctions. The
extended module is finite: a finite generating list of the original finite module gives
an epimorphism from a finite power of S. Thus the sheafified scalar extension is finite
constant on the same full root tower. Its descent permutations are those induced by
scalar extension and factor through a finite root group. To recover membership in the
specified essential image, decompose this finite abelian inertia set into transitive
orbits. At a common prime-to-p level n each is Gamma_n/K. A subgroup K of (Z/n)^r is
stable under multiplication by every unit modulo n, so it defines a subgroup of the
finite etale group scheme mu_n^r over the original chart, even when the roots of unity
are not in B. Quotient the punctured parameter-root torsor by that subgroup, and take
the finite disjoint union over the orbits. It is finite etale on the chart puncture and
is tame on every punctured strict-local tower. After pullback to H, root coordinates
identify its finite inertia set with the scalar-extended one. Effective descent along
the root covering identifies the two sheaves. This supplies the required original-chart
finite tame sheaf, not merely constancy after pullback to the full tower. The zero module
has a singleton underlying set; zero rings and the empty parameter tuple cause no change
to the argument. No degree condition, flatness or commutativity of R and S is used. -/
theorem sncFiniteTame_scalarExtension
    {p : ℕ} [Fact p.Prime] {Y : Scheme.{u}} {a : ℕ}
    {C : Fin a → Y.IdealSheafData} {I : Finset (Fin a)} (Q : SNCResidualChart p C I)
    (k : Type u) [Field k] [CharP k p]
    [(Spec Q.B).Over (Spec (.of k))]
    [LocallyOfFiniteType ((Spec Q.B) ↘ Spec (.of k))]
    [QuasiCompact ((Spec Q.B) ↘ Spec (.of k))]
    [IsSeparated ((Spec Q.B) ↘ Spec (.of k))]
    (_hD : IsStrictNormalCrossingsBoundary Q.chartBoundary)
    (R S : Type (u + 1)) [Ring R] [Ring S] [Finite R] [Finite S] (φ : R →+* S)
    (E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    (_adj : E ⊣ ModuleCat.restrictScalars φ)
    (M : Sheaf (Scheme.ProEt.topology Q.puncturedResidual) (ModuleCat.{u + 1} R))
    (_hM : Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} R))).obj M)) :
    Q.finiteTame ((sheafCompose (Scheme.ProEt.topology Q.puncturedResidual)
      (forget (ModuleCat.{u + 1} S))).obj
        ((presheafToSheaf (Scheme.ProEt.topology Q.puncturedResidual)
          (ModuleCat.{u + 1} S)).obj (M.obj ⋙ E))) := by
  sorry

end AlgebraicGeometry.ProEtale
