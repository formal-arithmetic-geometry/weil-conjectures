module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.SectionClearingDenominatorsQCQS
import WeilConjectures.AlgebraicGeometry.SectionRestrictionSTorsion
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Ample positive twists detect nonzero quasi-coherent complexes

Source: Stacks Project, perfect.tex, Tag 0BQR, lemma-nonzero-some-cohomology
(blueprint: lem-sfb-ample-twist-hypercohomology-detection).

There is no boundedness assumption on the complex. Hypercohomology is the
cohomology of the shared unbounded derived global sections functor.
-/

@[expose] public section

set_option autoImplicit false

universe u w wA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

/-- A nonzero unbounded complex with quasi-coherent cohomology has nonzero
hypercohomology after tensoring with a nonnegative power of an ample line bundle.
Source: Stacks Project, perfect.tex, Tag 0BQR, lemma-nonzero-some-cohomology
(blueprint: lem-sfb-ample-twist-hypercohomology-detection).

Proof:
1. Ampleness includes quasi-compactness, and implies separatedness by
   lem-weil-pbc-ample-scheme-separated. Thus X is quasi-separated. Use
   lem-sfb-qc-separated-quasicoherent-complex-model to represent K by a complex F
   of quasi-coherent modules, without imposing any bound.
2. Some cohomology sheaf of F is nonzero, since otherwise F -> 0 would be a
   quasi-isomorphism (def-weil-abstract-derived-category). By the germ description
   of def-weil-pbc-module-stalk and the sheaf axiom, it has a nonzero stalk at x.
   Ampleness supplies n > 0 and s in Gamma(X,L^n) with x in the affine open X_s.
   Set M = L^n; s trivializes M on this open.
3. The cycle sheaf Z = ker(d^p) is quasi-coherent by
   lem-weil-pbc-quasi-coherent-module-kernel. Its quotient H = H^p(F) is
   quasi-coherent, and Z(X_s) -> H(X_s) is surjective, by
   lem-weil-pbc-quasi-coherent-module-cokernel-image. The affine counit of
   lem-weil-pbc-affine-tilde-gamma-adjunction detects H(X_s) nonzero. Choose a
   nonzero section tau, lift it to a cycle a, and choose y with tau_y nonzero.
4. Apply lem-sc-p1-section-clearing-denominators-qcqs to extend a times s^b
   to a global section t of F^p tensor M^b. Its differential restricts to zero.
   The quasi-coherent coefficient F^(p+1) tensor M^b is locally F^(p+1), so
   lem-sc-p1-section-restriction-s-torsion kills that differential by s^c.
   The resulting global cycle z restricts to a times s^(b+c).
5. Tensoring by a line bundle is exact on local frames, so its degree-zero
   complex is K-flat (def-pc-kflat-complex). The shared derived tensor
   construction therefore identifies F tensor M^(b+c) with K tensor L^(n*(b+c)).
   Exactness of stalks (lem-weil-pbc-module-stalk-exact) identifies its stalk
   cohomology class at y with tau_y times the basis s_y^(b+c), which is nonzero.
6. Choose a K-injective resolution rho:G -> I of this tensor complex using
   prop-pur-kinjective-resolutions-exist on the small Zariski site of opens.
   By def-pc-global-derived-rhom, Gamma(X,I) computes derived global sections.
   If rho(z) were a boundary globally, its germ would be a boundary at y.
   Exactness of stalks makes rho_y a quasi-isomorphism, contradicting step 5.
   Hence degree p hypercohomology is nonzero, with exponent n*(b+c) >= 0. -/
theorem exists_nonzero_hypercohomology_ample_twist (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (ModuleCat.{u}
      ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L)
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (hne : ¬ IsZero K) :
    ∃ (m : ℕ) (p : ℤ),
      ¬ IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) p).obj
          ((schemeDerivedGlobalSections X).obj
            (K ⊗ (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
                (L.tensorPow m)))) := by
  sorry

end AlgebraicGeometry
