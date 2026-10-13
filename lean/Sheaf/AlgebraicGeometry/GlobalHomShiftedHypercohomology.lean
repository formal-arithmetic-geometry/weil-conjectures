/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Shift and global-section comparison for internal derived Hom
Source: Stacks Project, Tags 08JA and 0B6A.
(blueprint: lem-sc-global-hom-shifted-hypercohomology).
-/

@[expose] public section

set_option autoImplicit false
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Cohomology of module-valued global Hom agrees with zeroth additive-group-valued
hypercohomology of the internal Hom of shifted arguments. This comparison concerns
only cohomology, not the identification with derived morphisms.
Source: Stacks Project, Tag 08JA, proof of Lemma 21.35.1; Tag 0B6A, Section 20.44.
(blueprint: lem-sc-global-hom-shifted-hypercohomology).

Proof: Represent P by a K-flat complex L and Q by a K-injective complex I. Their
sheaf Hom complex is K-injective, so its termwise global sections compute RΓ.
The shifted complexes L[m] and I[n] remain K-flat and K-injective. The standard
signed reindexing identifies Hom(L[m], I[n]) with Hom(L,I)[n-m]: in degree k,
reindex a component from p to p+m and multiply it by (-1)^(m*k). The differential
on each side is d_I a - (-1)^degree a d_L, with the shift signs included; thus this
is an isomorphism of complexes, natural in the second argument. Taking global
sections and H⁰ gives H^(n-m) of the unshifted global Hom complex.
Evaluation at the unit sheaf gives the additive isomorphism between the underlying
group of module-valued global sections and Hom_O(O,-), the functor used in
ringedSiteZerothHypercohomology. On each open this evaluation sends a module map
O → F to the image of 1; its inverse sends a section s to multiplication by s.
Both maps commute with differentials and morphisms. Right-derived resolution
comparisons and localization therefore give the displayed additive equivalences,
independent of the chosen representatives. A derived morphism q can be represented
after K-injective replacement, and all the comparisons commute with its map and
with its shift, proving the displayed naturality. These constructions use all
integer degrees and do not require boundedness, quasi-coherence, or any relation
between the sheaf and module localization universes. -/
theorem schemeGlobalHom_shiftedHypercohomology_equiv
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    (X : Scheme.{u}) :
    ∃ c : ∀ (P Q : schemeDerivedCategory X) (m n : ℤ),
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
          ((schemeGlobalDerivedHom X).obj (op P, Q))) ≃+
        ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
            (op (P⟦m⟧), Q⟦n⟧))),
      ∀ (P Q Q' : schemeDerivedCategory X) (m n : ℤ) (q : Q ⟶ Q')
        (x : ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (n - m)).obj
            ((schemeGlobalDerivedHom X).obj (op P, Q)))),
        c P Q' m n
          (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) (n - m)).map
              ((schemeGlobalDerivedHom X).map ((𝟙 P).op, q))) x) =
          (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X) X.sheaf).map
            ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
              ((𝟙 (P⟦m⟧)).op, q⟦n⟧')) (c P Q m n x) := by sorry

end AlgebraicGeometry
