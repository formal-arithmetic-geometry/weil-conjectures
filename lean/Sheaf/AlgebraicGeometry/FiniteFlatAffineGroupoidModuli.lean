/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood
import Sheaf.AlgebraicGeometry.AffineGroupoidEtaleInvariantComparison
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

import Mathlib.AlgebraicGeometry.Morphisms.Affine

import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Limits

import Mathlib.AlgebraicGeometry.Pullbacks

import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # The invariant spectrum of a finite locally free affine groupoid

Source: Stacks Project, Tags 0DUM, 0DUP, 0DUR, 03BK and 03BL
(blueprint: lem-sfb-finite-flat-affine-groupoid-moduli).

The quotient is specified by its fppf presentation, retaining the original composition.
The structure map is normalized on the atlas. Flat-base-change functions are expressed
as actual compatible families with their canonical pullback, including the zero ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

variable {k E L : Type u} [Field k] [CommRing E] [CommRing L]
  [Algebra k E] [Algebra k L]

/-- The invariant spectrum with its inherited k-structure.
Source: Stacks, Tag 0DUP (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def affineGroupoidModuliBase (σ τ : E →ₐ[k] L) : Over (Spec (.of k)) :=
  (Spec (.of (AlgHom.equalizer σ τ))).asOver (Spec (.of k))

/-- The invariant inclusion induces the specified atlas-to-moduli morphism.
Source: Stacks, Tag 0DUP (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def affineGroupoidModuliAtlasMap (σ τ : E →ₐ[k] L) :
    (Spec (.of E)).asOver (Spec (.of k)) ⟶ affineGroupoidModuliBase σ τ :=
  (Spec.map (CommRingCat.ofHom (AlgHom.equalizer σ τ).val.toRingHom)).asOver (Spec (.of k))

/-- The invariant ring acts on the arrow ring by either endpoint map.
Source: Stacks, Tag 03BK (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
instance affineGroupoidInvariantArrowAlgebra (σ τ : E →ₐ[k] L) :
    Algebra (AlgHom.equalizer σ τ) L :=
  (σ.toRingHom.comp (AlgHom.equalizer σ τ).val.toRingHom).toAlgebra

/-- The source coordinate map as a homomorphism over the invariant ring.
Source: Stacks, Tag 03BK (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def affineGroupoidInvariantSource (σ τ : E →ₐ[k] L) :
    E →ₐ[AlgHom.equalizer σ τ] L where
  __ := σ.toRingHom
  commutes' _ := rfl

/-- The target coordinate map over the same invariant ring, using the equalizer equality.
Source: Stacks, Tag 03BK (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def affineGroupoidInvariantTarget (σ τ : E →ₐ[k] L) :
    E →ₐ[AlgHom.equalizer σ τ] L where
  __ := τ.toRingHom
  commutes' x := x.property.symm

/-- An affine chart over the invariant spectrum, with its composite k-structure.
Source: Stacks, Tag 03BK (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def affineGroupoidModuliChart (σ τ : E →ₐ[k] L)
    (D : Type u) [CommRing D] [Algebra (AlgHom.equalizer σ τ) D] :
    Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (AlgHom.equalizer σ τ) D)) ≫
    (affineGroupoidModuliBase σ τ).hom)

/-- The actual affine base-change map to the invariant spectrum.
Source: Stacks, Tag 03BK (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def affineGroupoidModuliChartMap (σ τ : E →ₐ[k] L)
    (D : Type u) [CommRing D] [Algebra (AlgHom.equalizer σ τ) D] :
    affineGroupoidModuliChart σ τ D ⟶ affineGroupoidModuliBase σ τ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (AlgHom.equalizer σ τ) D))) rfl

/-- The actual 2-base change, with a specified comparison isomorphism in every object.
Source: Stacks, Tag 0DUP (blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
abbrev affineGroupoidModuliBaseChange (σ τ : E →ₐ[k] L)
    {F : BasedCategory.{v, w} (Over (Spec (.of k)))}
    (f : BasedFunctor F (discreteModuli (yoneda.obj (affineGroupoidModuliBase σ τ))))
    (D : Type u) [CommRing D] [Algebra (AlgHom.equalizer σ τ) D] :=
  moduliTwoFiberProduct
    (discreteModuliMap (yoneda.map (affineGroupoidModuliChartMap σ τ D))) f

/-- The structural pullback of d evaluated on one object of a stack over Spec D.
This is a component of a compatible family, with the same canonical ULift as the
recorded structure sheaf. Source: Stacks, Tag 06W6
(blueprint: lem-sfb-finite-flat-affine-groupoid-moduli). -/
def moduliAffineFunctionValue {S : Scheme.{u}} {D : Type u} [CommRing D]
    {F : BasedCategory.{v, w} (Over S)} {m : Spec (.of D) ⟶ S}
    (p : BasedFunctor F (discreteModuli (yoneda.obj (Over.mk m))))
    (d : D) (x : F.obj) : (moduliStructurePresheaf F).obj (op x) :=
  ULift.up ((Scheme.Γ.map
    (eqToHom (congrArg (fun T : Over S ↦ T.left) (p.w_obj x)).symm ≫
      (yoneda.preimage (p.obj x).hom).left).op) ((Scheme.ΓSpecIso (.of D)).inv d))

/-- The invariant-spectrum map is uniform categorical, qcqs, a universal homeomorphism,
induces the geometric isomorphism-class bijection, and identifies structure sheaves.
Invariants commute with every flat affine base change, and the resulting scalar ring
is exactly the global-function ring through the displayed structural pullback.

Source: Stacks, Tags 0DUM, 0DUP, 0DUR, 03BK and 03BL
(blueprint: lem-sfb-finite-flat-affine-groupoid-moduli).

Proof, following the nine steps of the DAG node:
1. The flat-groupoid quotient theorem gives algebraicity and the finite locally free
surjective atlas. Stackification descent identifies maps into discrete spaces with
invariant maps on U. The inclusion C into E therefore gives the canonical f; the
spectrum correspondence gives categorical factorization for affine targets.
2. The affine flatness criterion and flat tensor exactness applied to
0 → C → E → L identify the base-changed equalizer with D. The affine fibre-product
formula and fppf-presentation theorem identify the pulled-back quotient with the
base-changed groupoid. Quasi-coherent algebra descent identifies its global functions
with that equalizer, naturally on restrictions. On affine etale tests these are the
components of the canonical structure-sheaf isomorphism.
3. A geometric object lifts through the nonempty finite locally free atlas: a maximal
ideal of its finite-dimensional algebra has residue field the algebraically closed
base field. Arrows in R are precisely isomorphisms between lifts. The orbit-fibre
lemma then gives the required bijection of geometric isomorphism classes.
4. Integrality over invariants makes U → M universally closed. Closed subsets descend
along the surjective atlas, so f is universally closed on affine tests. Step 3 makes
it universally bijective. For arbitrary algebraic-stack tests, use smooth scheme
atlases, the point-surjectivity of 2-fibre products and the smooth-atlas topology.
Thus every such point map is a homeomorphism.
5. Each affine test pulls the atlas back to an affine scheme, proving quasi-compactness.
The diagonal pulls back along U ×_M U to the affine map R → U ×_M U. Representable
fppf locality gives an affine diagonal and hence quasi-separatedness.
6. For two factorizations to a space Y their equalizer H over M is a scheme monomorphism
through which f factors. Step 4 makes it a universal homeomorphism, hence affine.
Affine-target categoricity then makes H → M an isomorphism, proving uniqueness.
7. An affine etale neighbourhood of U → Y and the finite-set affine-neighbourhood
lemma give invariant affine opens in the pulled-back groupoid. Their stabilizer and
endpoint squares are cartesian. The etale invariant-comparison theorem gives etale
N → M and O = U ×_M N; the fppf-presentation theorem identifies the quotient base change.
8. The invariant map O → V factors through N by the affine calculation. Repeating
around each point gives etale-local factorizations to Y. Step 6 makes them agree on
overlap affine opens; the algebraic-space sheaf property glues them uniquely.
9. Step 2 applies this argument after all flat affine base changes. Affine etale covers
of an arbitrary flat algebraic-space base and uniqueness glue the factorization there.
All arguments allow the zero ring, nonreduced finite covers and variable rank.
-/
theorem finiteFlatAffineGroupoid_moduli
    (k E L : Type u) [Field k] [CommRing E] [CommRing L]
    [Algebra k E] [Algebra k L] (σ τ : E →ₐ[k] L)
    (e : Spec (.of E) ⟶ Spec (.of L)) (i : Spec (.of L) ⟶ Spec (.of L))
    (c : pullback (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (Spec.map (CommRingCat.ofHom τ.toRingHom)) ⟶ Spec (.of L))
    [(Spec.map (CommRingCat.ofHom σ.toRingHom)).IsFiniteLocallyFree]
    [(Spec.map (CommRingCat.ofHom τ.toRingHom)).IsFiniteLocallyFree]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (a : BasedFunctor (discreteModuli (yoneda.obj
      ((Spec (.of E)).asOver (Spec (.of k))))) F)
    (P : SchemeGroupoidQuotientPresentation
      ((Spec.map (CommRingCat.ofHom σ.toRingHom)).asOver (Spec (.of k)))
      ((Spec.map (CommRingCat.ofHom τ.toRingHom)).asOver (Spec (.of k))) e i c F a) :
    ∃ hF : IsAlgebraicModuliStack F,
    ∃ f : BasedFunctor F (discreteModuli (yoneda.obj (affineGroupoidModuliBase σ τ))),
      a.comp f = discreteModuliMap (yoneda.map (affineGroupoidModuliAtlasMap σ τ)) ∧
      IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, 0, 0} f ∧
      IsQuasiSeparatedAlgebraicModuliMap f ∧
      (∀ (B : AlgebraicSpace (Spec (.of k)))
        (b : B.obj.obj ⟶ yoneda.obj (affineGroupoidModuliBase σ τ)),
        (∀ (T : Over (Spec (.of k))) (h : yoneda.obj T ⟶ B.obj.obj),
          AlgebraicSpace.IsEtale h → Flat (yoneda.preimage (h ≫ b)).left) →
        ∀ Y : AlgebraicSpace (Spec (.of k)),
          Function.Bijective (fun h : B.obj.obj ⟶ Y.obj.obj ↦
            (moduliTwoFiberFst (discreteModuliMap b) f).comp (discreteModuliMap h))) ∧
      (∀ (Z : BasedCategory.{max u v v', max (u + 1) w w'} (Over (Spec (.of k))))
        (g : BasedFunctor Z (discreteModuli (yoneda.obj (affineGroupoidModuliBase σ τ)))),
        IsAlgebraicModuliStack Z →
          IsHomeomorph (moduliPointMap (moduliTwoFiberFst g f))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (j : k →+* Ω),
        Function.Bijective ((moduliFiberMap f
          (Over.mk (Spec.map (CommRingCat.ofHom j)))).mapSkeleton.obj)) ∧
      IsIso (moduliStructureMap hF.1.1
        (AlgebraicSpace.schemeSpace (affineGroupoidModuliBase σ τ)) f) ∧
      ∀ (D : Type u) [CommRing D] [Algebra (AlgHom.equalizer σ τ) D]
        [Module.Flat (AlgHom.equalizer σ τ) D],
        Function.Injective
          (Algebra.TensorProduct.includeRight : D →ₐ[AlgHom.equalizer σ τ]
            E ⊗[AlgHom.equalizer σ τ] D) ∧
        (∀ x : E ⊗[AlgHom.equalizer σ τ] D,
          Algebra.TensorProduct.map (affineGroupoidInvariantSource σ τ)
            (AlgHom.id (AlgHom.equalizer σ τ) D) x =
          Algebra.TensorProduct.map (affineGroupoidInvariantTarget σ τ)
            (AlgHom.id (AlgHom.equalizer σ τ) D) x ↔
          ∃ d : D, Algebra.TensorProduct.includeRight d = x) ∧
        ∀ s : RingCat.sectionsSubring
          (moduliStructurePresheaf (affineGroupoidModuliBaseChange σ τ f D) ⋙
            forget₂ CommRingCat RingCat),
          ∃! d : D, ∀ x : (affineGroupoidModuliBaseChange σ τ f D).obj,
            s.val (op x) = moduliAffineFunctionValue
              (moduliTwoFiberFst
                (discreteModuliMap (yoneda.map (affineGroupoidModuliChartMap σ τ D))) f) d x := by
  sorry

end AlgebraicGeometry
