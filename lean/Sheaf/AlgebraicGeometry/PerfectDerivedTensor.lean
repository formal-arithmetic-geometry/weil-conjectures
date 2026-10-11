module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct

/-! # Derived tensor products of perfect complexes

Source: literature/stacks-project/cohomology.tex, Lemma 09J5
(blueprint: lem-sc-perfect-derived-tensor-perfect).
-/

@[expose] public section

universe uT wT

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 256 in
/-- (blueprint: lem-sc-perfect-derived-tensor-perfect) If `K, L` are perfect objects of
`D(𝒪_X)`, then so is `K ⊗^L_{𝒪_X} L`.
Source: Stacks Project, Cohomology of Sheaves, Lemma 09J5.

There is no derived tensor bifunctor on `D(𝒪_X)`; as in
def-pc-derived-tensor-cohomology-vanishes, lem-pc-derived-pullback-tensor-qcoh and
lem-pc-derived-pullback-tensor-product, `K ⊗^L L` is stated through K-flat representatives:
for K-flat complexes `P, N` of `𝒪_X`-modules with `Q(P) ≅ K` and `Q(N) ≅ L`,
`K ⊗^L L ≅ Q(Tot(P ⊗_{𝒪_X} N))` (tensor `SheafOfModules.monoidalCategory X.sheaf`,
def-pc-tensor-complex-sheaves). K-flat resolutions exist (lem-pc-kflat-resolution), so
quantifying over all such `P, N` covers every pair `K, L`.

Proof (Stacks 09J5): perfectness is local. Given `x`, choose opens around `x` on which `K`
and `L` are isomorphic to strictly perfect complexes and intersect them to `U`. Restriction to
`U` commutes with the representative tensor, and on `U` the derived tensor is computed by the
strictly perfect (bounded, termwise finite projective, hence K-flat) models; their total
tensor complex is bounded with terms direct summands of finite free `𝒪_U`-modules, i.e.
strictly perfect. Hence `Q(Tot(P ⊗ N))` is perfect by the definition of `IsPerfect`. -/
theorem perfect_derivedTensor (X : Scheme.{uT})
    [HasDerivedCategory.{wT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wT}
        (SheafOfModules.{uT} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (hK : Scheme.IsPerfect X K) (hL : Scheme.IsPerfect X L)
    (P N : CochainComplex (SheafOfModules.{uT} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlat (R := X.sheaf) N)
    (eP : DerivedCategory.Q.obj P ≅ K) (eN : DerivedCategory.Q.obj N ≅ L) :
    Scheme.IsPerfect X (DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P N
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) := by
  sorry

end AlgebraicGeometry
