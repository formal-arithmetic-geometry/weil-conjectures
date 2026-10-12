module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A small filtered system of constructible maps to `F`, with factorization and
refinement of relations tested on constructible sources.

Source: Stacks Project, Tags 03SA(3), 095N and 03RZ; the category of finite
presentations over `F` in Modules on Sites, Lemma 093C.
(blueprint: lem-weil-pbc-module-sheaf-colimit-constructible-data).

Proof: Choose representatives of constructible module sheaves. They form a set in
universe `u + 1`: by 095N each is the cokernel of a map between finite sums of the
extensions by zero of finite free modules on qcqs etale objects; these objects have
a small skeleton, and the morphisms form sets in this universe. Include the zero
sheaf, finite sums, and cokernels. These operations preserve constructibility by
03S8 and 03RZ. Take the category of pairs `(G, G -> F)` on these representatives,
with commuting triangles as morphisms, and its forgetful diagram `D`. It is small.
Zero gives an object, direct sum gives a common successor, and the cokernel of the
difference of parallel maps gives an equalizing successor, so it is filtered.
The maps to `F` give the natural transformation `ι`. Every constructible map to `F`
is an object up to an isomorphism, which proves factorization. Given the two
factorizations in the last condition, form the cokernel of the map from `G` to
`D.obj a ⊕ D.obj b` with components `p` and `-q`. The assumed equality makes the
map from the sum to `F` descend to this cokernel. Its two inclusions give `f, g`,
and the cokernel equation is precisely `p ≫ D.map f = q ≫ D.map g`.
This constructs the system and its relations without asserting a universal
property for arbitrary cocones. -/
theorem exists_filtered_constructible_data
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (A : Type (u + 1)) (_ : SmallCategory A) (_ : IsFiltered A)
      (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const A).obj F),
      (∀ a : A, IsConstructibleEtaleModuleSheaf (D.obj a)) ∧
      (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsConstructibleEtaleModuleSheaf G → ∀ p : G ⟶ F,
          ∃ (a : A) (q : G ⟶ D.obj a), q ≫ ι.app a = p) ∧
      (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsConstructibleEtaleModuleSheaf G → ∀ (a b : A)
          (p : G ⟶ D.obj a) (q : G ⟶ D.obj b),
          p ≫ ι.app a = q ≫ ι.app b →
          ∃ (c : A) (f : a ⟶ c) (g : b ⟶ c), p ≫ D.map f = q ≫ D.map g) := by
  sorry

end AlgebraicGeometry.Scheme
