/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.GerbeModuliMap
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness and universal point-space homeomorphisms of gerbes

Source: Stacks Project, stacks-morphisms.tex, Tags 0DN8, 06QI, 06R9 and 06QE
(blueprint: lem-sfb-gerbe-smooth-universal-homeomorphism).

Smoothness is stated on every smooth scheme atlas. Surjectivity and the universal
homeomorphism refer to the canonical maps on the existing field-object quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- An algebraic gerbe over a space is surjective and smooth, with surjective flat
locally finitely presented atlas composites, and is universally a homeomorphism.
Source: Stacks Project, Tags 0DN8, 06QI, 06R9, 06QE, 075V and 04ZT
(blueprint: lem-sfb-gerbe-smooth-universal-homeomorphism).

Proof:
1. The gerbe condition is preserved by scheme and stack base change (06QE).
   Algebraicity of the products is lem-sfb-algebraic-stack-fibre-products. For a field
   object, choose a nonempty member of its fppf lifting cover, a point, and its residue
   field. This proves surjectivity, also after every stack base change.
2. For any smooth surjective atlas U and etale target chart V, trivialize the gerbe
   on an fppf cover V_i of V. Its section V_i to the gerbe is representable, surjective,
   flat and locally finitely presented by lem-sfb-neutral-gerbe-section-fppf.
   Pulling back the atlas gives W_i to V_i smooth and W_i to U_i fppf, using
   lem-sfb-stack-chartwise-smooth-etale-calculus.
3. An etale scheme chart Z_i of W_i makes Z_i to U_i fppf and Z_i to V_i smooth.
   Apply lem-sbc-smooth-flat-surjective-source-descent, then
   lem-sfb-space-smooth-surjective-fppf-locality, to obtain smoothness over V.
   This holds for every atlas and target chart. The chartwise calculus gives flatness
   and local finite presentation; field lifting through the gerbe and atlas gives
   surjectivity of each composite. No smoothness of the gerbe section is used.
4. For an arbitrary stack base change, equal target point classes admit representatives
   over a common field with an isomorphism. The gerbe's local connectedness gives a
   compatible isomorphism of the source objects after a further field extension.
   The triple description of the 2-fibre product proves injectivity on point classes.
5. Continuity is lem-sfb-stack-point-topology-flat-lfp-open. Choose a smooth atlas A
   of the new target and an atlas Z of its pullback gerbe. The map Z to A is flat
   and locally finitely presented by steps 2--3, hence open by that same topology lemma.
   For open O in the source, the inverse image in A of its image is the image in A
   of its inverse image in Z. The reverse inclusion uses common-field representatives,
   their isomorphism, the 2-fibre-product triple, and a field lift through Z.
   The atlas topology therefore makes the projection open. A continuous open bijection
   is a homeomorphism, with inverse the inverse of this same projection map. -/
theorem gerbe_smooth_universal_homeomorphism {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (Q : AlgebraicSpace S)
    (p : BasedFunctor F (discreteModuli Q.obj.obj))
    (hF : IsAlgebraicModuliStack F) (hp : IsGerbeModuliMap p) :
    Function.Surjective (moduliPointMap p) ∧
    (∀ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a →
        ModuliSpaceTest @Smooth (a.comp p) ∧
        Function.Surjective (moduliPointMap (a.comp p)) ∧
        ModuliSpaceTest @Flat (a.comp p) ∧
        ModuliSpaceTest @LocallyOfFinitePresentation (a.comp p)) ∧
    (∀ (T : BasedCategory.{v₂, w₂} (Over S)), IsAlgebraicModuliStack T →
      ∀ t : BasedFunctor T (discreteModuli Q.obj.obj),
        IsHomeomorph (moduliPointMap (moduliTwoFiberSnd p t))) := by
  sorry

end CategoryTheory
