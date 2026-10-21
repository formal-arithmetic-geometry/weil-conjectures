/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
/-! # Continuity for modules with one finite constructible stratification
Source: the classicality detail of blueprint constructible comparison; Stacks 09AK.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Finite local systems on one finite constructible partition give continuity.
Source: blueprint sk-thm-pe-constructible-comparison-classical, Stacks Tag 09AK
(blueprint: lem-pe-coefficient-stratified-continuity).

Proof: constant-scalar restriction keeps the additive sheaf, and its scalar action
extends uniquely back across the locally bijective constant-ring sheafification
unit. Over a Noetherian ring each finite local model is finitely presented. The
finite-presentation local-system comparison makes its restriction to each stratum
an etale inverse image. Localize first on affine open subsets; restriction pulls
back the same finite partition and its models. On each affine, induct on the
finite constructible partition, using affine
shrinking to expose a nonempty open stratum. The open-closed exact sequence has
etale antecedents for extension by zero and closed direct image, by comparison
with these two operations. The classical subcategory is closed under extensions,
so the remaining closed partition and the open stratum give an etale antecedent
for the restricted module. Etale origin is Zariski local, so these local
antecedents descend to the entire module. Empty strata can first be removed, and the empty partition
on the empty scheme gives the zero sheaf. On an affine presentation, etale sections
of an inverse image form the prescribed filtered colimit by finite-presentation
factorization of maps into etale schemes. This identifies the canonical
continuity map, including its A-action, with a colimit comparison isomorphism.
All this takes place on the equivalent coefficient-sized sites: an object and a
cover retain their underlying scheme, and AsSmall sends every projection to that
same projection. Hence it gives exactly the map displayed below. -/
theorem coefficientStratified_continuity (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
    (S : Scheme.Stratification X)
    (hS : ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
      (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} (S.immersion a) A).obj
        ((coefficientModelFixedScalars _ A).obj F))) :
    ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I),
      IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          ((coefficientModelFixedScalars _ A).obj F).obj)) := by sorry
end AlgebraicGeometry.ProEtale
