/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap
import Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsOverlapMate

/-! # Resolved relative short exact rows before tensor pullback -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A resolved relative comparison of short exact rows, before the cone-to-quotient passage.
Source: Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY;
resolved-row construction in the proof of
lem-pc-relative-mv-direct-image-homotopy-comparison.
(blueprint: lem-pc-relative-mv-direct-image-rows).

Proof: Choose injective-term K-injective representatives I and J of K and K'.
Transpose phi under the pinned adjunction for g'. Resolve g'_* J by an
injective-term K-injective L, with quasi-isomorphism rho:g'_* J -> L, and
represent the transpose by r:I -> L. Restriction preserves K-injectivity,
and direct image along an open immersion preserves it because restriction
is its exact left adjoint. Form the restriction-unit/difference rows of
I and L, and the inverse-image restriction row of J. Apply f_* to the first
two rows to obtain rows S and R on S, and f'_* to the last to obtain P' on S'.
All three rows are short exact on sections: sheaf gluing gives the kernel,
and injective flasqueness gives the surjectivity. In particular T = G(P')
is also short exact, since its sections are sections of P' on inverse images.
The sectionwise open-image and composition comparisons identify T with
f_* of the restriction row of g'_* J. Naturality gives strict row maps
u:S -> R from r and v:T -> R from rho.

Each component of v is a quasi-isomorphism. For this unbounded assertion use
RingedSpace.isIso_moduleDirectImage_unit_on_kInjective, not merely termwise
flasqueness. Apply it to g' and each restricted g' followed by the appropriate
open immersion and by f. The complexes on X' used here are restrictions of
J followed by open direct image, hence K-injective. Both sides then compute
the same derived composite direct image, and naturality of its localization
unit identifies the localized v with the image of the quasi-isomorphism rho.
The same unit calculation for f' followed by g identifies eta at P'.X_i.

Construct the homotopy pullback of u and v in the category of rows. Explicitly,
put P_i^n = S_i^n plus T_i^n plus R_i^(n-1), with differential
(s,t,z) |-> (ds,dt,-dz+u(s)-v(t)); use the three horizontal row maps on the
summands. Their commutation with u and v makes these horizontal maps chain
maps, and P is short exact degreewise because S, T and R are short exact.
The projections p:P -> S and m:P -> T are strict row maps. The kernel of
each p_i is the shifted cone of v_i, up to the harmless sign on v_i; it is
acyclic since v_i is a quasi-isomorphism. Thus p_i is a quasi-isomorphism.
Projection to the third summand is a row homotopy u p ~ v m. Consequently,
in the derived category, Q(m_i) = Q(v_i)^(-1) Q(u_i) Q(p_i), for all three
components including the quotient. This construction fixes that component
without choosing a completion of a triangle square or invoking a cone-to-quotient iso.

Use Q(p_i) followed by the source-row comparisons and apply Lg* to get e_i;
the target-row comparisons give e_i'. For i=1, the transposed coefficient
map r and the composite-adjunction counit formula identify the mate of
Q(v_i)^(-1) Q(u_i) with a.hom. For a local open W, perform the same calculation
on its inverse-image square. The sectionwise open counit equation identifies
the restricted coefficient map with the one in relativeMVLocalArrow W.
Take W=U and W=V and use biproduct extensionality for i=2; take W=U intersection V
for i=3. Naturality of the Hom equivalence moves Q(p_i) and the vertex comparisons
across these equations, giving precisely the three displayed mate identities.
Empty opens have zero local terms; repeated opens give split restriction rows;
zero coefficients give acyclic representatives and phi=0 can be represented
by the zero chain map r. Source replacements occur on S; G need not preserve
quasi-isomorphisms. Source for the unbounded computation: Stacks Tag 0D5T,
with the right-derived unit compatibility in the cited acyclicity theorem. -/
theorem relativeMV_direct_image_rows
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (P : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ))
      (P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P'.map F)
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁) ≫ e₁'.hom =
        e₁.hom ≫ a.hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂) ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  classical
  dsimp only
  have hrows := relativeMV_direct_image_rows_preoverlap f f' g g' hpull K K' φ U V hcover
  rcases hrows with ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hdata⟩
  have hP := hdata.1
  have hP' := hdata.2.1
  have h₁ := hdata.2.2.1
  have h₂ := hdata.2.2.2.1
  have h₃ := hdata.2.2.2.2
  refine ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', h₁, h₂, ?_⟩
  exact relativeMV_direct_image_rows_overlap_mate f f' g g' hpull K K' φ U V
    P P' m e₃ e₃' h₃

end AlgebraicGeometry
