/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.SingletonStackFlatLfpFieldCover
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.FlatInertiaAlgebraicSpaceQuotient
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.LocallyNoetherianFppfDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Reduced locally Noetherian singleton stacks are gerbes

Source: Stacks Project, stacks-morphisms.tex, Tags 06QK and 06QC
(blueprint: lem-sfb-noetherian-singleton-gerbe).

The two gerbe clauses are written out using fppf covering sieves. Objects over a scheme
are expressed as functors from its representable discrete fibred groupoid. By the fibred
Yoneda equivalence these are the objects of the fibre; their 2-isomorphisms are the fibre
isomorphisms. Since the target space has discrete fibres, an isomorphism between two
objects above the same section is automatically an isomorphism over that section.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A reduced locally Noetherian algebraic stack with exactly one point is a gerbe
over a reduced locally Noetherian algebraic space with exactly one point.
Source: Stacks Project, Tags 06QK (lemma-noetherian-singleton-stack-gerbe) and 06QC
(definition-gerbe) (blueprint: lem-sfb-noetherian-singleton-gerbe).

Proof:
1. Apply lem-sfb-singleton-stack-flat-lfp-field-cover to the reduced locally
   Noetherian smooth atlas and the nonempty singleton point space. Obtain a representable
   surjective flat locally finitely presented map Spec K to F, for a field K.
2. By lem-sfb-inertia-locally-finite-type, the inertia over F is representable and
   locally of finite type. Base change to Spec K using
   lem-sfb-stack-chartwise-smooth-etale-calculus. On every etale scheme chart it is flat
   by lem-pc-flat-field, and locally finitely presented by pqf-lem-lft-fp-locnoeth,
   since a field is Noetherian.
3. Descend these two properties of inertia along Spec K to F by
   lem-sfb-representable-flat-lfp-fppf-descent.
4. Apply lem-sfb-flat-inertia-algebraic-space-quotient to the fppf sheafification Q of
   fibrewise isomorphism classes. Its projection p is smooth and surjective. The local
   representatives of lem-weil-pbc-site-sheafification-sections-local supply objects
   over every section of Q after an fppf cover. Its local equality clause supplies
   isomorphisms after an fppf cover for any two objects over that section. Discreteness
   of the target fibres makes these isomorphisms relative to the section.
5. By lem-sfb-gerbe-smooth-universal-homeomorphism, p identifies point spaces, so Q
   has exactly one point. The reduced locally Noetherian smooth scheme atlas U of F
   composes to a surjective flat locally finitely presented morphism U to Q.
6. Choose a surjective etale scheme atlas W of Q. Its pullback V = U times_Q W is
   a scheme, etale over U and surjective flat locally finitely presented over W, by
   lem-sfb-stack-chartwise-smooth-etale-calculus. The former map gives reducedness
   and local Noetherianity of V by lem-trf-smooth-reduced-dense-pullback. Apply
   lem-sfb-scheme-locnoeth-fppf-descent to V to W to obtain local Noetherianity of W.
7. For w in W, choose z in V above it. The local-ring map is flat by
   def-weil-flat-morphism and faithfully flat by lem-weil-pbc-flat-local-hom-faithfully-flat.
   Apply lem-weil-pbc-faithfully-flat-ideal-contraction to the zero ideal to get injectivity.
   Any nilpotent in the stalk of W maps to zero in the reduced stalk of V, hence is zero.
   Thus W is reduced by def-pc-reduced-scheme, giving the required etale atlas of Q. -/
theorem exists_noetherian_singleton_gerbe {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (hatlas : ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ IsReduced U.left ∧ IsLocallyNoetherian U.left)
    (hsingleton : Nonempty (ModuliPoints F) ∧ Subsingleton (ModuliPoints F)) :
    ∃ (Q : AlgebraicSpace S) (p : BasedFunctor F (discreteModuli Q.obj.obj)),
      (∃ (U : Over S) (a : yoneda.obj U ⟶ Q.obj.obj),
        AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
          IsReduced U.left ∧ IsLocallyNoetherian U.left) ∧
      (Nonempty (AlgebraicSpace.Point Q.obj.obj) ∧
        Subsingleton (AlgebraicSpace.Point Q.obj.obj)) ∧
      (∀ (T : Over S) (q : yoneda.obj T ⟶ Q.obj.obj),
        ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
          ∀ (U : Over S) (g : U ⟶ T), R g →
            ∃ x : BasedFunctor (discreteModuli (yoneda.obj U)) F,
              Nonempty (ModuliTwoIso (x.comp p)
                (discreteModuliMap (yoneda.map g ≫ q)))) ∧
      (∀ (T : Over S) (q : yoneda.obj T ⟶ Q.obj.obj)
        (x y : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        Nonempty (ModuliTwoIso (x.comp p) (discreteModuliMap q)) →
        Nonempty (ModuliTwoIso (y.comp p) (discreteModuliMap q)) →
        ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over S) T ∧
          ∀ (U : Over S) (g : U ⟶ T), R g →
            Nonempty (ModuliTwoIso
              ((discreteModuliMap (yoneda.map g)).comp x)
              ((discreteModuliMap (yoneda.map g)).comp y))) := by
  sorry

end CategoryTheory
