/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction

/-!
# Finite-stage models for a Cartesian open after weakly contractible testing

Source: the principal-open exhaustion in Steps 2--8 of
`lem-exc-proetale-cartesian-open-injective-acyclic`, extracted from the blueprint
`prop-exc-base-change-proper`, Steps 2--4.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- After testing on an affine weakly contractible object, an arbitrary Cartesian
open extension has a filtered model with a common lower bound and acyclic finite
stages. This gives a model before applying bounded continuity, rather than asserting
vanishing for its colimit.

Source: the principal-open exhaustion in Steps 2--8 of
`lem-exc-proetale-cartesian-open-injective-acyclic`; blueprint
`prop-exc-base-change-proper`, Steps 2--4; Stacks Tags 09AE, 09BN and 0946.
(blueprint: lem-exc-cartesian-open-finite-stage-hypercohomology-model).

Proof:
1. Put P = Q times_T V. Properness over affine Q makes P quasi-compact and
quasi-separated. Restriction along the site-object maps P to V and U_Q to U
preserves injectives. The inverse-image/restriction and open-base-change
comparisons identify the restricted input with k_Q! J_Q.
2. Write Q = Spec B. Index by finite subsets E of the set of b in B with
D(b) contained in W_Q. Include the empty subset and order by inclusion; union
makes this a small filtered category. Put W_E = union of D(b), for b in E,
and U_E = P times_Q W_E. Both open immersions are quasi-compact, and the
proper morphism U_E to W_E is a base change of p. Restrict J_Q to U_E;
restriction preserves its injectivity.
3. For inclusions E subset E', the open-extension adjunction gives the
transition morphism from the extension of J_Q restricted to U_E to that
for U_E'. These maps compose by the adjunction bijection. Take their
complexes concentrated in degree zero as K. Their common lower bound is zero.
4. The finite-stage proper/open acyclicity theorem gives zero positive higher
images for every stage. Exact evaluation on the weakly contractible terminal
object of Q identifies this with positive hypercohomology on P. The terminal
object stays weakly contractible under the slice-site equivalence: lift its
identity section through any epimorphism and retain the map to Q.
5. The union of the U_E is U_Q. The open-extension adjunction and sheaf gluing
on this cover identify colim K with k_Q! J_Q concentrated in degree zero.
Restriction of an injective resolution computes sections over P, so the
restriction comparison in step 1 yields the displayed hypercohomology
isomorphism for every integer q. No continuity of hypercohomology is used in
constructing this model. Empty opens use E = empty and the zero sheaf; whole
opens and the zero coefficient ring obey the same construction.
-/
theorem exists_cartesianOpen_finiteStage_hypercohomology_model
    (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsProper p] [IsOpenImmersion i]
    (J : proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)) [Injective J]
    (Q : T.ProEt) [IsAffine Q.left]
    (hQ : ∀ (F G : Sheaf (ProEt.topology T) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (Opposite.op Q))) :
    let P := ((proEtaleBaseChange p).obj Q).left
    let R := (sheafCompose (ProEt.topology P)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing P A)
    let U : P.ProEt := ProEt.mk (𝟙 P)
    CompactSpace P ∧ QuasiSeparatedSpace P ∧
      ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
        (K : I ⥤ CochainComplex (ringedSiteModules.{u + 1} R) ℤ),
        (∀ (a : I) (b : ℤ), b < 0 → IsZero ((K.obj a).X b)) ∧
        (∀ (a : I) (q : ℕ), 0 < q →
          IsZero ((ProEt.ringHypercohomology P R U (q : ℤ)).obj (K.obj a))) ∧
        (∀ q : ℤ, Nonempty
          (((ProEt.ringHypercohomology V
            ((sheafCompose (ProEt.topology V)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (proEtaleConstantRing V A)) ((proEtaleBaseChange p).obj Q) q).obj
              ((CochainComplex.singleFunctor
                (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj
                  ((sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J))) ≅
            (ProEt.ringHypercohomology P R U q).obj (colimit K))) := by
  sorry

end AlgebraicGeometry.Scheme
