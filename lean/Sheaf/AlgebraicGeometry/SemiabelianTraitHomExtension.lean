module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-! # Extension of semiabelian homomorphisms over a trait

Source: Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1, printed pages 10-11, including its opening DVR case.
(blueprint: lem-sfb-semiabelian-trait-hom-extension)

The generic fibres and restriction of homomorphisms use the canonical group-object
base-change functor along the spectrum of the fraction-field inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Every group homomorphism between the generic fibres extends uniquely over the trait.
No completeness, excellence, residue-characteristic or properness assumption is made.

Source: Faltings, Finiteness Theorems for Abelian Varieties over Number Fields,
Chapter II, section 2, Lemma 1, printed pages 10-11, opening complete-DVR case
and its faithfully flat descent to an arbitrary DVR.
(blueprint: lem-sfb-semiabelian-trait-hom-extension)

Proof plan from the accepted DAG split:
1. Identify the generic scheme fibres G_L and H_L with their base changes along
   Spec L to Spec R, by def-pc-scheme-fibre and def-pc-base-change. Writing the
   same fraction field as F changes neither the induced group structures nor v.
2. Apply lem-sfb-trait-semiabelian-hom-extension to the same R, L, G, H and v.
   Its DVR, smoothness, separatedness, finite-presentation and semiabelian-fibre
   hypotheses are exactly these hypotheses. Its unique extension is the required
   extension. The accepted split reuses this existing identical trait input;
   it does not claim to expand the source's omitted complete-DVR argument. -/
theorem semiabelian_trait_hom_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]
    (G H : Grp (Over (Spec (.of R)))) [IsCommMonObj G.X] [IsCommMonObj H.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [Smooth H.X.hom] [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (hH : HasSemiabelianGeometricFibres H)
    (v : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj G ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.obj H) :
    ∃! vbar : G ⟶ H,
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mapGrp.map vbar = v := by
  sorry

end AlgebraicGeometry
