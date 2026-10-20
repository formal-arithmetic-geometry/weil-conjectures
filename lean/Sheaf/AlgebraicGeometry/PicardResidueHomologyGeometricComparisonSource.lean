/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison
import Sheaf.AlgebraicGeometry.PicardResidueHomologySourceFibreComparison
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Geometric naturality after passing to residue homology

Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: lem-sc-picard-residue-homology-geometric-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The source residue homology agrees with degree-one structure-sheaf fibre cohomology.
Source: Stacks Project, Tags 0B91, 0BF2, 01XK and 010V.
(blueprint: new-picard-residue-homology-comparison-source)

Proof: Put A = Gamma(W,U). Each retraction of K.X j from a finite free sheaf
remains a retraction after affine sections. Thus its section module is finite
projective, including rank zero, and the bounded section complex is K-flat.
Affine quasi-coherent sheaves are equivalent to A-modules, so derived restriction
of Q(K) to the residue point is computed by tensoring this section complex.
Its degree-one homology is precisely the kernel of d(1,2) modulo the image of
d(0,1), the quotient used in affineResidueCycleHomology. The equation hp
identifies the residue field of p with W.residueField w. Since k is an immersion
and k(w)=s, its map on residue fields is an isomorphism, so this field is also
S.residueField s. The isomorphism hE transports this calculation to the derived
direct image of the pullback of L. The invertible coefficient is finitely
presented and flat relative to the base because f is flat. Arbitrary derived
base change for the proper finitely presented morphism therefore identifies
the residue calculation with derived global sections of L on the fibre X_s.
Use tau to replace that fibre coefficient by its structure sheaf. Taking
homology in degree one and forgetting scalars gives the stated additive
equivalence. This argument requires projective terms, not chosen free frames;
it does not tensor cohomology in place of tensoring the complex. -/
theorem picard_residue_homology_geometric_comparison_source
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    :
    Nonempty (affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1) := by
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  obtain ⟨e₁⟩ := picard_residue_homology_source_residue_comparison W E w
    U hwU hU p hp K hK hE
  obtain ⟨e₂⟩ := picard_residue_homology_source_fibre_comparison f L W k w s hw τ
  exact ⟨e₁.trans e₂⟩

end Scheme

end AlgebraicGeometry
