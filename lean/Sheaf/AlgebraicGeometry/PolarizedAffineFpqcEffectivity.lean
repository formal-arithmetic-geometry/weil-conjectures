module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import WeilConjectures.AlgebraicGeometry.AmpleFiniteAffineCover
import Sheaf.AlgebraicGeometry.AmpleProjLocalChart
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import Sheaf.AlgebraicGeometry.QuasiAffineRelativeSpecEmbedding
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent

/-! # Effective affine fpqc descent of polarized schemes

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §6.1, Theorem 7, printed p.138,
affine-base specialization (blueprint: lem-sfb-polarized-affine-fpqc-effectivity).

The scheme datum is the recorded `Over.DescentDatum`. The module comparison is
written in the equivalent transport form: it compares the pullbacks to every test
scheme, naturally in that scheme, and satisfies the cocycle. `HEq` only transports
across equal scheme maps, namely the naturality and cocycle equations of the given
scheme datum. The composition comparisons are the section-normalized tensor ones.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Effective descent of a scheme with a compatible ample invertible module along a
faithfully flat map of affine bases. The natural family `ell` is the pullback, to all
test schemes, of the specified isomorphism on the double overlap. Its naturality
`hell_natural` and cocycle `hell_cocycle` express exactly that overlap datum. No separate
identity condition is required: it follows from the cocycle and invertibility.
The cartesian square in the conclusion supplies the pair's base-change isomorphism;
the next two clauses recover the prescribed scheme and module data, respectively.

Source: BLR, Néron Models, §6.1 Theorem 7, printed p.138 (PDF p.144)
(blueprint: lem-sfb-polarized-affine-fpqc-effectivity).

Proof plan:
1. The spectrum map is flat, surjective and affine, hence singleton fpqc
   (flat-affine criterion, faithfully flat spectrum surjectivity, fpqc axioms).
   Ampleness makes the upstairs scheme separated and quasi-compact.
2. Push forward every nonnegative tensor power of `M'`. Quasi-coherence and
   canonical flat base change in degree zero give compatible descent data on their
   section modules. Descend them by fpqc module descent; affine sections identify
   their scalar extensions with the original sections.
3. The finite affine section cover and the ample Proj charts identify `X'` with an
   open subscheme of the Proj of its section ring, over the affine upstairs base.
4. Every positive-degree nonvanishing open is a quasi-compact open in an affine
   Proj chart. Finite affine intersections prove quasi-compactness, so it is
   quasi-affine over the upstairs base (relative-Spec embedding criterion).
5. Write each section as a finite linear combination of descended invariant
   sections. At a point where it is nonzero, one invariant summand is nonzero.
   Their nonvanishing opens cover `X'` and inherit transport-compatible data.
6. Quasi-affine fpqc effectivity descends each open. Effective invariant-open
   gluing descends the scheme and recovers its entire prescribed transport.
7. The resulting map `q` is fpqc. Its double overlap is identified using the
   given scheme datum; `ell` is then ordinary module descent along `q`. Fpqc module
   descent, including descent of rank one, gives `M` and the compatible `e`.
8. Relative ampleness descends fpqc (Stacks 0D3C, scheme specialization).
   Affine-base ample canonical data identify upstairs absolute ampleness with
   relative ampleness; affineness of the downstairs base makes `M` ample.
   The argument includes empty schemes and the zero-ring base. -/
theorem exists_polarized_affine_fpqc_descent
    {B C : Type u} [CommRing B] [CommRing C] (φ : B →+* C)
    (hφ : φ.FaithfullyFlat) (V : Over (Spec (CommRingCat.of C)))
    [QuasiCompact V.hom]
    (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom φ)) V)
    (M' : V.left.Modules) [M'.IsInvertible] (hM' : Scheme.Modules.IsAmple V.left M')
    (ell : ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ Spec (CommRingCat.of C))
      (h : f₀ ≫ Spec.map (CommRingCat.ofHom φ) = f₁ ≫ Spec.map (CommRingCat.ofHom φ))
      (a : Over.mk f₀ ⟶ V),
      (Scheme.Modules.tensorPullback a.left).obj M' ≅
        (Scheme.Modules.tensorPullback (D.transport f₀ f₁ h a).left).obj M')
    (hell_natural : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T)
      (f₀ f₁ : T ⟶ Spec (CommRingCat.of C))
      (h : f₀ ≫ Spec.map (CommRingCat.ofHom φ) = f₁ ≫ Spec.map (CommRingCat.ofHom φ))
      (a : Over.mk f₀ ⟶ V),
      HEq
        ((Scheme.Modules.tensorPullbackSectionComp g a.left).app M' ≪≫
          (Scheme.Modules.tensorPullback g).mapIso (ell f₀ f₁ h a) ≪≫
          ((Scheme.Modules.tensorPullbackSectionComp g
            (D.transport f₀ f₁ h a).left).app M').symm)
        (ell (g ≫ f₀) (g ≫ f₁)
          (by rw [Category.assoc, Category.assoc, h])
          ((Over.homMk g : Over.mk (g ≫ f₀) ⟶ Over.mk f₀) ≫ a)))
    (hell_cocycle : ∀ {T : Scheme.{u}} (f₀ f₁ f₂ : T ⟶ Spec (CommRingCat.of C))
      (h₀₁ : f₀ ≫ Spec.map (CommRingCat.ofHom φ) = f₁ ≫ Spec.map (CommRingCat.ofHom φ))
      (h₁₂ : f₁ ≫ Spec.map (CommRingCat.ofHom φ) = f₂ ≫ Spec.map (CommRingCat.ofHom φ))
      (a : Over.mk f₀ ⟶ V),
      HEq ((ell f₀ f₁ h₀₁ a) ≪≫ (ell f₁ f₂ h₁₂ (D.transport f₀ f₁ h₀₁ a)))
        (ell f₀ f₂ (h₀₁.trans h₁₂) a)) :
    ∃ (X : Over (Spec (CommRingCat.of B))) (q : V.left ⟶ X.left)
      (M : X.left.Modules) (hM : M.IsInvertible)
      (e : (Scheme.Modules.tensorPullback q).obj M ≅ M'),
      @Scheme.Modules.IsAmple X.left M hM ∧
      IsPullback q V.hom X.hom (Spec.map (CommRingCat.ofHom φ)) ∧
      (∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ Spec (CommRingCat.of C))
        (h : f₀ ≫ Spec.map (CommRingCat.ofHom φ) = f₁ ≫ Spec.map (CommRingCat.ofHom φ))
        (a : Over.mk f₀ ⟶ V), (D.transport f₀ f₁ h a).left ≫ q = a.left ≫ q) ∧
      (∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ Spec (CommRingCat.of C))
        (h : f₀ ≫ Spec.map (CommRingCat.ofHom φ) = f₁ ≫ Spec.map (CommRingCat.ofHom φ))
        (a : Over.mk f₀ ⟶ V),
        HEq ((Scheme.Modules.tensorPullbackSectionComp a.left q).app M ≪≫
            (Scheme.Modules.tensorPullback a.left).mapIso e ≪≫ ell f₀ f₁ h a)
          ((Scheme.Modules.tensorPullbackSectionComp
              (D.transport f₀ f₁ h a).left q).app M ≪≫
            (Scheme.Modules.tensorPullback (D.transport f₀ f₁ h a).left).mapIso e)) := by
  sorry

end AlgebraicGeometry
