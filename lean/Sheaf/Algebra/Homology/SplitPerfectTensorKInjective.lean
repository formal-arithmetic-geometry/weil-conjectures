/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.KInjectiveHomComplex
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Tensoring K-injectives with bounded split-projective complexes

Source: Stacks Project, Cohomology on Sites, Tags 0A96, 06YQ, 0FPR;
Modules on Sites, Tag 0FNY; More on Algebra, Tag 0FNK
(blueprint: lem-weil-pbc-split-perfect-tensor-kinjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Tensoring a K-injective complex with a bounded complex of finite-free retracts
preserves K-injectivity. Neither boundedness of `I` nor a zero differential on `P` is required.
Source: Stacks Project, Tags 0A96, 06YQ, 0FPR, 0FNY, 0FNK
(blueprint: lem-weil-pbc-split-perfect-tensor-kinjective).

Proof:
1. Form `D = Hom(P, R[0])` using `def-pur-hom-complex`. Its term in degree `q` is
   the dual of `P.X (-q)`, with differential `(-1)^(q+1)` times precomposition.
   If `P` is supported in `[a,b]`, then `D` is supported in `[-b,-a]`.
   Dualizing the given retraction exhibits each term of `D` as a finite-free retract.
2. Tensoring with such a retract is a retract of a finite direct sum of the identity
   functor, hence is exact (`def-pc-flat-sheaf-modules`). Thus every term of `D` is flat.
3. Apply `lem-pc-bounded-above-flat-kflat-site` to conclude that `D` is K-flat.
4. Write `c_j = p(e_j)` and let `lambda_j` be the coordinates of `i`.
   Evaluation sends `x tensor y` to `(phi maps to x phi(y))`; its inverse sends `f`
   to the sum of `f(lambda_j) tensor c_j`. The retraction identity proves both inverse
   identities, compatibly with restrictions (`def-pur-sheaf-tensor-product`,
   `def-pur-sheaf-hom`). Finite support identifies the total sums with the Hom products.
   Multiply evaluation on `I.X a tensor P.X r` by `(-1)^r` to obtain `alpha`.
5. The Hom differential (`def-pur-hom-complex`) gives components
   `(-1)^r d_I(x) phi(y)` and `(-1)^(a+r+1) x phi(d_P(y))`. These equal the images
   under `alpha` of the two terms of the signed tensor differential
   (`def-pc-tensor-complex-sheaves`). Thus `alpha` is an isomorphism of complexes.
6. Apply `lem-pur-hom-kflat-into-kinjective` to `D` and `I`. Any map from an acyclic
   complex into the tensor total complex becomes null-homotopic after composing with
   `alpha`. Compose the homotopy with `alpha` inverse to obtain a null homotopy of the
   original map (`def-pur-kinjective-complex`). -/
theorem isKInjective_mapBifunctor_of_bounded_splitFree
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R : Sheaf J CommRingCat.{u}}
    (I P : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    [I.IsKInjective]
    (hbounded : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r))
    (hsplit : ∀ r : ℤ, ∃ N : ℕ,
      ∃ i : P.X r ⟶ ∏ᶜ (fun _ : Fin N =>
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
      ∃ p : (∏ᶜ (fun _ : Fin N =>
        SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
          ⟶ P.X r, i ≫ p = 𝟙 (P.X r)) :
    (mapBifunctor I P
      (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory R))).IsKInjective :=
  sorry

end CochainComplex
