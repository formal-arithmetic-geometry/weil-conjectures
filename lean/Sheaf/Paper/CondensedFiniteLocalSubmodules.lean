/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields

/-!
# Descending compatible local submodules to one finite coefficient field

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph
(blueprint: lem-weil-pbc-condensed-finite-local-submodules).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- After a finite enlargement, the adjoints of the local model isomorphisms
are compatible embeddings into the restriction of the given module.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(blueprint: lem-weil-pbc-condensed-finite-local-submodules).

Proof: choose the supplied local isomorphisms. Their adjoints into the restrictions
of M are monomorphisms: each finite coefficient extension is finite free and faithfully
flat, and the algebraic closure is the filtered union of those extensions; the same
holds after inverse image to X and its covering schemes. On each pairwise overlap,
compose one extended local isomorphism with the inverse of the other. Quasi-separatedness
of X and affineness of the covering schemes make these overlaps qcqs. Transport to
sectionwise modules by the internal-module equivalence. Tensor adjunction and the Hom
part of the qcqs section calculus descend each comparison and its inverse to a finite
field. There are finitely many pairs, so choose a common finite upper field containing E.
Eventual equality in the same Hom colimit enforces the inverse identities after one
further enlargement. The descended comparisons commute with the adjoints into M:
transpose their defining equality after scalar extension. This gives exactly the
underlying overlap isomorphisms and equations displayed below. Scalar extension of
each adjoint is still the chosen local isomorphism, after the tensor composition
comparison, and hence is invertible. No global module or effective gluing is asserted.
If the cover is empty there are no maps or equations to descend and F = E works. -/
theorem exists_finiteCoefficient_compatible_local_monomorphisms
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F),
      let R := (upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)
      let S := (upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)
      let a := (upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)
      let L := fun i ↦ (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i)
      ∃ q : ∀ i, L i ⟶ ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj
        ((Mod.comap a).obj M),
        (∀ i, Mono (q i)) ∧
        (∀ i, IsIso (((Mod.extendRestrictAdjunction
          ((upperStar Ab.{u + 1} (U.f i)).map a)).homEquiv (L i)
            (((upperStar Ab.{u + 1} (U.f i)).mapMod S).obj M)).symm
              (q i ≫ ((upperStar Ab.{u + 1} (U.f i)).mapModComapIso a).hom.app M))) ∧
        (∀ i j, ∃ c :
          (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i).X ≅
            (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j).X,
          c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j).hom =
            (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i).hom ≫
              (upperStarCompIso Ab.{u + 1}
                (pullback.condition (f := U.f i) (g := U.f j))).hom.app
                  ((Mod.comap a).obj M).X) := by
  sorry

end AlgebraicGeometry.ProEtale
