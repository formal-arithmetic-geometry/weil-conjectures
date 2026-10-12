module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.AlgebraicGeometry.FlatModelFiniteFreeConstruction

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback homology comparison for a local finite-free replacement.
Source: Stacks Project, Tags 06YD and 06YJ, as used in
`lem-pc-flat-model-finite-free-shortening`.
Proof: assume the displayed quasi-isomorphism from P to the restriction of C.
The bounded flat representatives compute derived pullback termwise; the
quasi-isomorphism is preserved, and taking homology gives the displayed
isomorphism for every scheme map and degree.
(blueprint: lem-pc-flat-model-finite-free-shortening-comparison).
Proof: The construction argument supplies the stated local data and its induced
quasi-isomorphism. Pulling it back along any scheme map preserves it for these
finite-free and flat complexes; taking homology gives the displayed isomorphism.
-/
theorem local_finiteFree_homology_comparison {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T)
    (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ)
    (hstruct : t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (P.X n ≅ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))))
    (eP : P ⟶ ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj C)
    (heP : QuasiIso eP) :
    ∀ {T' : Scheme.{u}} (g : T' ⟶ V.toScheme) (q : ℕ),
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
        (((Modules.pullback (g ≫ T.homOfLE hVU)).mapHomologicalComplex _).obj C).homology q) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
