/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.SpaceChangeBase
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Data.Finsupp.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Etale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Polynomial generators for an affine étale chart algebra

Source: Stacks Project, Spaces Cohomology, Tag 07V6, proof before the H¹ argument;
Properties of Spaces, Tag 03M1; Spaces, Tag 04SG
(blueprint: lem-sfb-space-affine-etale-polynomial-generators).

The witness records the algebra structure on the specified module direct image, normalized
on every chart, and the polynomial algebra by its monomial coproduct universal property.
Thus the evaluation is an algebra map with the specified values, not an arbitrary module
surjection. Neither finite type nor cohomological vanishing is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Regard a space over an arbitrary scheme as a space over the integers. The selected
extension is fixed up to its unique compatible isomorphism by the sigma formula, its
restrictions and projection in `exists_spaceChangeBase`; that theorem also identifies
its small étale ringed site with the original one, retaining every scheme chart.
Source: Stacks, Spaces, Tag 04SG
(blueprint: lem-sfb-space-affine-etale-polynomial-generators). -/
def absoluteBaseChangeToIntegers {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  ((Classical.choose (exists_spaceChangeBase (specULiftZIsTerminal.from S))).obj X).left

/-- The complete witness of the polynomial-generator assertion. `F` is the direct-image
algebra, with its given module direct image and every chart projection retained. `P` is
precisely the free commutative algebra on `m` global variables: its monomials, including
1, exhibit its underlying module as the coproduct of copies of the structure module.
This specifies the free algebra up to its unique variable-preserving isomorphism.
`evaluationModule` is normalized on every section of the algebra map `evaluation`.
Source: Stacks, Spaces Cohomology, Tag 07V6, proof before the H¹ argument; Properties
of Spaces, Tag 03M1 (blueprint: lem-sfb-space-affine-etale-polynomial-generators). -/
structure PolynomialAtlasPresentation {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : Over S) (p : schemeSpace U ⟶ X) where
  /-- The direct-image algebra, retaining commutative multiplication. -/
  F : X.CommAlgebraSheaf
  /-- Its underlying module is the specified canonical direct image. -/
  underlying : F.toModule ≅
    (moduleDirectImage p).obj (SheafOfModules.unit (schemeSpace U).structureSheaf)
  /-- The actual chart projections are ring homomorphisms. -/
  projection (T : X.EtaleSite) (q : ModuleChart p T) :
    F.right.obj.obj (op T) →+* Scheme.Γ.obj (op ((schemeSpace U).etaleForget.obj q.left))
  /-- These ring maps are exactly the existing direct-image projections. -/
  projection_eq (T : X.EtaleSite) (q : ModuleChart p T)
      (a : F.toModule.val.obj (op T)) :
    projection T q a =
      ((moduleDirectImageModel p).projection
        (SheafOfModules.unit (schemeSpace U).structureSheaf) T).app (op q)
        (underlying.hom.val.app (op T) a)
  /-- The canonical global-sections identification with the affine chart ring. -/
  globals : Scheme.Γ.obj (op U.left) ≃ F.toModule.sections
  /-- A function on U restricts to that same function on every chart over U. -/
  globals_eq (b : Scheme.Γ.obj (op U.left)) (T : X.EtaleSite) (q : ModuleChart p T) :
    projection T q ((globals b).val (op T)) =
      (yoneda.preimage q.left.obj.hom).left.appTop b
  /-- Quasi-coherence of the module direct image. -/
  quasiCoherent :
    ((moduleDirectImage p).obj
      (SheafOfModules.unit (schemeSpace U).structureSheaf)).IsQuasicoherent
  /-- Zero generators are permitted. -/
  m : ℕ
  /-- The chosen global functions on the affine chart. -/
  g : Fin m → Scheme.Γ.obj (op U.left)
  /-- The polynomial algebra sheaf. -/
  P : X.CommAlgebraSheaf
  /-- Its specified global variables. -/
  z : Fin m → P.toModule.sections
  /-- Inclusions of the copies of the structure module indexed by monomials. -/
  monomial : (Fin m →₀ ℕ) → (SheafOfModules.unit X.structureSheaf ⟶ P.toModule)
  /-- Each monomial inclusion has precisely its usual polynomial value. -/
  monomial_eq (d : Fin m →₀ ℕ) (T : X.EtaleSite)
      (a : X.structureSheaf.obj.obj (op T)) :
    (monomial d).val.app (op T) a =
      P.hom.hom.app (op T) a *
        d.prod (fun i n ↦ (@id (P.right.obj.obj (op T)) ((z i).val (op T))) ^ n)
  /-- The polynomial module is the coproduct of its monomials, as sheaves. -/
  monomial_isColimit : IsColimit (Cofan.mk P.toModule monomial)
  /-- Evaluation as a map of sheaves of commutative O_X-algebras. -/
  evaluation : P ⟶ F
  /-- The same map on the underlying module sheaves. -/
  evaluationModule : P.toModule ⟶ F.toModule
  /-- Its components are the given algebra evaluation, on all local sections. -/
  evaluationModule_eq (T : X.EtaleSite) (a : P.toModule.val.obj (op T)) :
    evaluationModule.val.app (op T) a = evaluation.right.hom.app (op T) a
  /-- Each variable maps to its chosen function, through the canonical identification. -/
  evaluation_z (i : Fin m) : SheafOfModules.sectionsMap evaluationModule (z i) = globals (g i)
  /-- Surjectivity in the sense of sheaves, allowing local lifts. -/
  surjective : Presheaf.IsLocallySurjective X.etaleTopology evaluation.right.hom
  /-- The kernel of evaluation into the specified module direct image is quasi-coherent. -/
  kernel_quasiCoherent : (kernel (evaluationModule ≫ underlying.hom)).IsQuasicoherent

/-- An affine surjective étale chart of a space separated over an affine scheme has
finitely many global polynomial generators for its direct-image structure algebra,
with quasi-coherent direct image and kernel. The original base scheme is arbitrary;
`absoluteBaseChangeToIntegers` retains its small étale ringed site by Tag 04SG.
Source: Stacks, Spaces Cohomology, Tag 07V6, proof before H¹; Properties of Spaces,
Tag 03M1 (blueprint: lem-sfb-space-affine-etale-polynomial-generators).

Proof:
1. By lem-trf-space-separated-affine-chart-overlap, R = U ×_X U is affine and closed
   in U ×_V U. The affine fibre-product description
   (lem-weil-pbc-fibre-product-affine-spectra) gives B tensor_A B onto C = Gamma(R).
2. Both schemes R and U are affine. Thus p0 is affine
   (lem-weil-pbc-morphism-affine-schemes-affine), and affine locality
   (lem-sfb-space-affine-locality) makes p affine. It is quasi-compact separated, so
   lem-trf-space-qc-separated-quasi-coherent-pushforward gives quasi-coherence of F.
3. The étale map p0 makes C finitely presented over B, by
   lem-weil-pbc-etale-algebra-finite-presentation-localization. Lift finitely many
   generators through the tensor-product surjection and collect their second entries.
   Their images under p1 generate C over p0(B); allow an empty list.
4. The limit projections of def-trf-space-etale-module-functors give F its unique
   componentwise algebra operations. Restriction gives Gamma(X,F) = Gamma(U,O_U).
   Form the free commutative algebra P on the chosen global variables, and evaluate.
5. By lem-trf-space-etale-module-pushforward-restriction, over an affine étale test
   Spec D of U, evaluation is the polynomial map to C tensor_B D with the selected
   generators. It is surjective since C is generated by their images over B.
6. Pull the atlas back to any test scheme, and cover it by affine opens, using
   lem-trf-space-fibre-products-etale-covers, lem-weil-pbc-affine-opens-basis and
   lem-weil-pbc-open-immersion-etale. Chartwise permanence
   (lem-trf-space-chartwise-etale-permanence) makes this an étale cover. The preceding
   lifts prove local surjectivity, equivalently sheaf surjectivity by
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective.
7. P is the direct sum of copies of O_X indexed by monomials. The direct-sum and kernel
   assertions of lem-sfb-space-qcoh-kernels-colimits imply quasi-coherence of P and of
   the evaluation kernel. No cohomological vanishing or finite-type assumption occurs. -/
theorem affine_etale_polynomial_generators {S : Scheme.{u}} (X : AlgebraicSpace S)
    (V : Scheme.{u}) [IsAffine V]
    (f : absoluteBaseChangeToIntegers X ⟶
      schemeSpace (Over.mk (specULiftZIsTerminal.from V)))
    (hf : IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left)
      (Limits.pullback.diagonal f.hom.hom))
    (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [IsAffine U.left]
    (p : schemeSpace U ⟶ absoluteBaseChangeToIntegers X)
    (hp : IsEtale p.hom.hom) (hs : IsSurjective p.hom.hom) :
    Nonempty (PolynomialAtlasPresentation U p) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
