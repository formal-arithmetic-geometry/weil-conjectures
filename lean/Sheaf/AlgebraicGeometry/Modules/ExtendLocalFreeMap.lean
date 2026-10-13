module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # Clearing denominators for a local map from a finite free module

Source: Stacks Project, Tag 01PW, specialized to the structure sheaf on a quasi-affine open.
(blueprint: new-sbc-local-free-map-extension)
-/

@[expose] public section
noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A local map from a finite free module extends after an invertible change of its source
on a smaller neighbourhood. The local map need not be an isomorphism.

(blueprint: new-sbc-local-free-map-extension)

Source: Stacks Project, Tag 01PW, applied with the invertible module O_V, as in the
global-generation input cited in Tag 0EKP, proof of (2) to (3).

Proof: choose an ambient principal open D(f) containing x and contained in U (viewed
as an open of Spec R). Its corresponding open W of V is the nonvanishing locus of
the restriction of f to V. The Noetherian hypothesis makes V quasi-compact, and its
inclusion into Spec R is separated. For every i in the finite set I, restrict the
image under the local map of the i-th standard basis section to W. Apply Tag 01PW
to this section, the quasi-coherent module N, the invertible module O_V and the
section f. Identify N tensor O_V to any power with N. Thus some global section
restricts to f^m_i times the given image. Take a common exponent m at least every
m_i, and multiply each global section by f^(m-m_i). The universal property of the
free sheaf gives a global map phi from these sections. On W its restriction is
the original local map precomposed with multiplication by f^m on the source.
Since f is a unit on W, that multiplication is an automorphism a. The displayed
identity follows on standard basis sections, hence on the free sheaf. The
restriction comparison c only identifies the single restriction with the two
successive restrictions. If I is empty, take the unique map and the identity
automorphism, with m = 0. No local freeness of N outside U is required. -/
theorem exists_global_map_of_local_free_map
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (N : V.toScheme.Modules) [N.IsQuasicoherent]
    (U : V.toScheme.Opens) (x : V.toScheme) (hx : x ∈ U)
    (I : Type u) [Finite I]
    (ψ : (restrictFunctor U.ι).obj (free (R := V.toScheme.ringCatSheaf) I) ⟶
      N.restrict U.ι) :
    ∃ (W : V.toScheme.Opens) (hWU : W ≤ U), x ∈ W ∧
      ∃ (φ : free (R := V.toScheme.ringCatSheaf) I ⟶ N),
        ∃ (a : (restrictFunctor W.ι).obj (free (R := V.toScheme.ringCatSheaf) I) ≅
          (restrictFunctor W.ι).obj (free (R := V.toScheme.ringCatSheaf) I)),
          let g := V.toScheme.homOfLE hWU
          let c := restrictFunctorCongr (V.toScheme.homOfLE_ι hWU).symm ≪≫
            restrictFunctorComp g U.ι
          (restrictFunctor W.ι).map φ = a.hom ≫
            c.hom.app (free (R := V.toScheme.ringCatSheaf) I) ≫
            (restrictFunctor g).map ψ ≫ c.inv.app N := by
  sorry

end AlgebraicGeometry.Scheme.Modules
