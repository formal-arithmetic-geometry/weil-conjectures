module

public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Pushouts of affine commutative group extensions

Source: Milne, *Algebraic Groups* (2017), Proposition 5.18, Theorem 5.13 and
Proposition 14.48 (printed pp. 102--103, 100--101 and 296)
(blueprint: lem-sfb-affine-commutative-extension-pushout).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The additive group object used in the antidiagonal pushout.
Source: Milne, *Algebraic Groups* (2017), Proposition 14.48 (p. 296)
(blueprint: lem-sfb-affine-commutative-extension-pushout). -/
noncomputable def affineExtensionAdditive (k : Type u) [Field k] :
    Grp (Over (Spec (.of k))) :=
  Grp.mk (StandardGroupSchemes.additive k)

/-- The antidiagonal homomorphism `(i,-φ)` into `B × Gₐ`.
Source: Milne, *Algebraic Groups* (2017), Proposition 14.48 (p. 296)
(blueprint: lem-sfb-affine-commutative-extension-pushout). -/
noncomputable def affineExtensionAntidiagonal
    {k : Type u} [Field k]
    {N B : Grp (Over (Spec (.of k)))}
    (i : N ⟶ B) (φ : N ⟶ affineExtensionAdditive k) :
    N.X ⟶ (B ⊗ affineExtensionAdditive k).X :=
  lift i.hom.hom (φ.hom.hom ≫ ι[(affineExtensionAdditive k).X])

/-- The two canonical maps into the product used in the pushout.
Source: Milne, *Algebraic Groups* (2017), Proposition 14.48 (p. 296)
(blueprint: lem-sfb-affine-commutative-extension-pushout). -/
noncomputable def affineExtensionLeftInclusion
    {k : Type u} [Field k] (B : Grp (Over (Spec (.of k)))) :
    B ⟶ B ⊗ affineExtensionAdditive k :=
  Grp.homMk (lift (𝟙 B.X) (toUnit B.X ≫ η[(affineExtensionAdditive k).X]))

/-- The additive inclusion into the product used in the pushout.
Source: Milne, *Algebraic Groups* (2017), Proposition 14.48 (p. 296)
(blueprint: lem-sfb-affine-commutative-extension-pushout). -/
noncomputable def affineExtensionRightInclusion
    {k : Type u} [Field k] (B : Grp (Over (Spec (.of k)))) :
    affineExtensionAdditive k ⟶ B ⊗ affineExtensionAdditive k :=
  Grp.homMk (lift (toUnit (affineExtensionAdditive k).X ≫ η[B.X]) (𝟙 _))

/-- Affine representability of the pushout of a commutative affine group extension.

Source: Milne, *Algebraic Groups* (2017), Proposition 5.18, Theorem 5.13 and
Proposition 14.48 (printed pp. 102--103, 100--101 and 296)
(blueprint: lem-sfb-affine-commutative-extension-pushout).

Proof (the six steps of the DAG node):
1. The product has coordinate algebra k[B][T]. The antidiagonal coordinate map extends
   the surjection i* and sends T to -φ*(T), so it is surjective and the antidiagonal is
   closed (the affine fibre-product formula and closed-immersion criterion). Its image
   is normal since every algebra-valued group of points is commutative.
2. Apply lem-sfb-affine-normal-quotient-geometry to obtain E and its fppf quotient map.
   Local lifts through this map show that E is commutative. Define b and j using the
   two product inclusions.
3. The map q pr_B kills the antidiagonal. The faithfully flat quotient universal
   property gives q', with q'ρ=q pr_B. The antidiagonal relation gives bi=jφ and q'b=q.
4. If j(t)=0, the kernel of ρ gives (0,t)=(i(n),-φ(n)); injectivity of i forces n=t=0.
   For e in ker(q'), lift locally to (x,t). Then x=i(n), so e=j(t+φ(n)). These additive
   coordinates agree on overlaps by injectivity and glue by fpqc representable descent.
   Yoneda identifies Gₐ with the scheme-theoretic kernel, hence j is its closed embedding.
5. Quotient E by this closed kernel, giving p:E→D. Factor pb through q as u:Q→D,
   and q' through p as v:D→Q using lem-sfb-faithfully-flat-group-quotient-universal.
   Uniqueness gives vu=1 from vuq=q; it gives uv=1 from uvpρ=pρ, using
   ρ(x,t)=b(x)+j(t) and pj=0. Thus q'=vp is faithfully flat and finitely presented.
6. For f:B→H and g:Gₐ→H with fi=gφ, the map (x,t)↦f(x)+g(t) kills the antidiagonal.
   It factors uniquely through the orbit presheaf and then its sheafification by
   def-weil-pbc-sheafification. The resulting map satisfies hb=f and hj=g; its formula
   on local lifts proves uniqueness. This works for all commutative fppf sheaves,
   and therefore for every represented commutative group scheme H.
-/
theorem affine_commutative_extension_pushout
    {k : Type u} [Field k]
    (N B Q : Grp (Over (Spec (.of k))))
    [IsCommMonObj N.X] [IsCommMonObj B.X] [IsCommMonObj Q.X]
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [IsAffine B.X.left] [LocallyOfFiniteType B.X.hom] [QuasiCompact B.X.hom]
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom]
    (i : N ⟶ B) (q : B ⟶ Q)
    [IsClosedSubgroupScheme i.hom.hom]
    (hqker : IsPullback i.hom.hom (toUnit N.X) q.hom.hom η[Q.X])
    (hqflat : q.hom.hom.left.appTop.hom.FaithfullyFlat)
    (hqfp : LocallyOfFinitePresentation q.hom.hom.left)
    (φ : N ⟶ affineExtensionAdditive k) :
    ∃ (a : N ⟶ B ⊗ affineExtensionAdditive k),
    a.hom.hom = affineExtensionAntidiagonal i φ ∧
    IsClosedImmersion a.hom.hom.left ∧
    ∃ (E : Grp (Over (Spec (.of k)))) (ρ : B ⊗ affineExtensionAdditive k ⟶ E),
      IsCommMonObj E.X ∧
      IsAffine E.X.left ∧ LocallyOfFiniteType E.X.hom ∧ QuasiCompact E.X.hom ∧
      IsFppfGroupQuotient a ρ ∧
      ρ.hom.hom.left.appTop.hom.FaithfullyFlat ∧
      Flat ρ.hom.hom.left ∧ Surjective ρ.hom.hom.left ∧
      LocallyOfFinitePresentation ρ.hom.hom.left ∧
      ∃ (q' : E ⟶ Q),
        ρ ≫ q' = fst B (affineExtensionAdditive k) ≫ q ∧
        IsClosedSubgroupScheme
          ((affineExtensionRightInclusion B ≫ ρ).hom.hom) ∧
        IsPullback (affineExtensionRightInclusion B ≫ ρ).hom.hom
          (toUnit (affineExtensionAdditive k).X)
          q'.hom.hom η[Q.X] ∧
        q'.hom.hom.left.appTop.hom.FaithfullyFlat ∧
        Flat q'.hom.hom.left ∧ Surjective q'.hom.hom.left ∧
        LocallyOfFinitePresentation q'.hom.hom.left ∧
        i ≫ affineExtensionLeftInclusion B ≫ ρ = φ ≫ affineExtensionRightInclusion B ≫ ρ ∧
        affineExtensionLeftInclusion B ≫ ρ ≫ q' = q ∧
        (∀ (H : Grp (Over (Spec (.of k)))) [IsCommMonObj H.X]
          (f : B ⟶ H) (g : affineExtensionAdditive k ⟶ H),
          i ≫ f = φ ≫ g →
          ∃! h : E ⟶ H, affineExtensionLeftInclusion B ≫ ρ ≫ h = f ∧
            affineExtensionRightInclusion B ≫ ρ ≫ h = g) := by
  sorry

end AlgebraicGeometry
