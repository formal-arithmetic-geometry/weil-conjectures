module

public import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Shrinking a nodal chart along its missed nodes

Source: Illusie--Laszlo--Orgogozo, Exposé VI, Proposition 1.9, printed p. 71,
equation (1.a); Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-chart-boundary-shrinking)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The coordinate `u` or `v` on the nodal model over `V`, pulled back from the
universal model. Source: Stacks Project, curves.tex, Tag 0CBY.
(blueprint: lem-trf-nodal-chart-boundary-shrinking) -/
noncomputable def nodalChartCoordinate {V : Scheme.{u}} (h : Γ(V, ⊤)) (k : Fin 2) :
    Γ(pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h), ⊤) :=
  (pullback.fst (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).appTop
    ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
      (Ideal.Quotient.mk _ (MvPolynomial.X k)))

/-- The closed node locus missed by the chart, projected to the base as a set.
Closedness is asserted in the theorem below, rather than assumed here.
Source: ILO VI, Proposition 1.9, printed p. 71, equation (1.a).
(blueprint: lem-trf-nodal-chart-boundary-shrinking) -/
noncomputable def nodalChartMissedNodes {V U : Scheme.{u}} (h : Γ(V, ⊤))
    (e : U ⟶ pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) : Set V :=
  (pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) ''
    ((pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocus
      (Set.range (nodalChartCoordinate h)) \ Set.range e)

/-- Remove the missed nodes from the base of an étale nodal chart. All surviving
nodes lift to the restricted chart, the chosen point survives, and the parameter
is a unit on the surviving open away from the closed boundary.

Source: ILO VI, Proposition 1.9, printed p. 71, equation (1.a), and Stacks 0CBY.
(blueprint: lem-trf-nodal-chart-boundary-shrinking)

Proof:
1. On Spec A the quotient by u and v of A[u,v]/(uv-h) is A/(h).
   These coefficient-preserving identifications commute with restriction, giving
   N ≅ V(h). The projection N → V is a closed immersion. The image of e is open
   by lem-weil-pbc-etale-morphism-open-map. Thus the missed nodes form a closed
   subset of N with closed image Z in V. Injectivity of N → V and e(t) ∈ N imply
   p(t) ∉ Z.
2. A node over V \ Z is in e(U) by the definition of Z. Choose its lift r.
   Its base point is in V \ Z, so r lifts to the open base change U°.
   The same open-fibre-product identification retains t. This uses
   lem-weil-pbc-open-fibre-product.
3. The model projection is flat and locally finitely presented by
   lem-trf-nodal-polynomial-free-flat. Apply
   lem-trf-nodal-model-etale-smooth-locus with f the model projection, b the
   identity, q=e, and p=e followed by the projection. It is nonsmooth at each
   lift of a node. A zero of h in V° \ T supplies such a lift by step 2,
   contradicting the assumed smoothness over V \ T.
4. Hence h has no zero in V° \ T. On every affine open there, no prime contains
   h; a maximal ideal containing the proper ideal (h) would contradict this.
   Thus h has an inverse on each such affine open. Uniqueness makes the inverses
   agree on overlaps, and the sheaf glues them to a global inverse, also when
   the open is empty. No reducedness assumption is used.
-/
theorem nodalChart_boundary_shrinking
    {V U : Scheme.{u}} (h : Γ(V, ⊤))
    (e : U ⟶ pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) [Etale e]
    (t : U)
    (ht : e t ∈ (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocus
      (Set.range (nodalChartCoordinate h)))
    (T : Set V) (hT : IsClosed T)
    (hSmooth : Smooth (pullback.snd (C := Scheme.{u})
      (e ≫ pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h))
      (Scheme.Opens.ι (X := V) ⟨Tᶜ, hT.isOpen_compl⟩))) :
    IsClosed (nodalChartMissedNodes h e) ∧
      (e ≫ pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) t ∉
        nodalChartMissedNodes h e ∧
      ∃ Vcirc : V.Opens,
        (Vcirc : Set V) = (nodalChartMissedNodes h e)ᶜ ∧
        (∀ s : V, s ∈ V.zeroLocus {h} → s ∈ Vcirc →
          ∃ r : pullback (C := Scheme.{u})
              (e ≫ pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) Vcirc.ι,
            (e ≫ pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h))
                ((pullback.fst (C := Scheme.{u})
                  (e ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h)) Vcirc.ι) r) = s ∧
              e ((pullback.fst (C := Scheme.{u})
                  (e ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h)) Vcirc.ι) r) ∈
                (pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).zeroLocus
                  (Set.range (nodalChartCoordinate h))) ∧
        (∃ t' : pullback (C := Scheme.{u})
            (e ≫ pullback.snd (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) Vcirc.ι,
          (pullback.fst (C := Scheme.{u})
            (e ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h)) Vcirc.ι) t' = t) ∧
        IsUnit (V.presheaf.map
          (homOfLE (le_top :
            Vcirc ⊓ (⟨Tᶜ, hT.isOpen_compl⟩ : V.Opens) ≤ ⊤)).op h) := by
  sorry

end AlgebraicGeometry
