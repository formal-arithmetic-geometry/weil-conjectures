/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Fiber

import Sheaf.AlgebraicGeometry.GenericGeometricallyReducedAffineModel

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A finite type family over an irreducible base admits, after shrinking and a finite
universal homeomorphism from an integral affine base, a reduced pullback that is flat,
finitely presented, and has geometrically reduced generic fibres.

Source: Stacks Project, Tag 0550, lemma-make-generic-fibre-geometrically-reduced.
(blueprint: lem-pur-generic-geometrically-reduced-preparation)
-/
theorem exists_generic_geometricallyReduced_preparation {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IrreducibleSpace S] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      ∃ T : Scheme.{u}, IsIntegral T ∧ IsAffine T ∧
        ∃ q : T ⟶ U.toScheme, IsFinite q ∧
          (topologically IsHomeomorph).universally q ∧
          Flat ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          LocallyOfFinitePresentation ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          QuasiCompact ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          QuasiSeparated ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          ∀ η : T, IsGenericPoint η Set.univ →
            GeometricallyReduced
              (((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
                pullback.snd f (q ≫ U.ι)).fiberToSpecResidueField η) := by
  obtain ⟨U, hU, _hUa, T, hTi, hTa, q, hqf, hqu, hflat, hfp, hqc, hqs, η, hη, hgeom⟩ :=
    exists_generic_geometricallyReduced_affine_model f
  refine ⟨U, hU, T, hTi, hTa, q, hqf, hqu, hflat, hfp, hqc, hqs, ?_⟩
  intro η' hη'
  have heq : η' = η := hη'.eq hη
  subst η'
  exact hgeom

end AlgebraicGeometry
