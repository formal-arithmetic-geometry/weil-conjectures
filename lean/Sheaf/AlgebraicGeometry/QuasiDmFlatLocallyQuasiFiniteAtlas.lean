/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Sheaf.AlgebraicGeometry.FieldGroupoidStabilizerDimension
import Mathlib.AlgebraicGeometry.Limits

/-! # Flat locally quasi-finite scheme atlases of quasi-DM stacks

Source: Stacks Project, stacks-morphisms.tex, Tag 06MF (theorem-quasi-DM), (1)--(2)
(blueprint: lem-sfb-quasidm-flat-locally-quasifinite-atlas).

The relative diagonal is the existing relative diagonal of the structural map to S.
All morphism properties use the existing algebraic-space scheme tests. Surjectivity
is field-extension lifting with a vertical 2-isomorphism, not a chosen point bijection.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An algebraic stack has locally quasi-finite relative diagonal exactly when it
admits a representable surjective flat locally finitely presented locally quasi-finite
scheme atlas. Source: Stacks Project, stacks-morphisms.tex, Tag 06MF, (1)--(2)
(blueprint: lem-sfb-quasidm-flat-locally-quasifinite-atlas).

Proof, following the six steps of the node:
1. Given q : W -> F, its product W x_S W -> F x_S F is a composite of base changes
of q, hence surjective, flat and locally finitely presented. The diagonal pulls back
there to j : W x_F W -> W x_S W. Its composite with projection to W is a base change
of q and is locally quasi-finite. Cancellation for spaces makes j locally quasi-finite;
fppf target descent gives the diagonal property. Use
lem-sfb-representable-lqf-calculus-descent, lem-sfb-stack-chartwise-smooth-etale-calculus,
and lem-sfb-algebraic-stack-fibre-products.
2. Conversely take a finite-type point x and an affine smooth chart U -> F with a
closed point u over x. Put k = kappa(u), R = u x_F u and E = U x_F u. Then E is smooth
over k and R is a locally finite type field groupoid. Scheme and space maps to F are
representable by its diagonal. Use lem-sfb-stack-finite-type-smooth-closed-chart,
lem-sfb-stack-chartwise-smooth-etale-calculus and
lem-sfb-stack-diagonal-space-source-representability.
3. The stabilizer G of R is a base change of the diagonal, hence locally quasi-finite.
Its etale scheme charts have relative dimension zero over k, so dim G = 0 and the
field-groupoid dimension lemma gives dim R = 0. The identity of R gives a k-rational
point z of E above u and identifies R with E x_U u. Use
lem-sfb-representable-lqf-calculus-descent,
lem-trf-locally-quasi-finite-relative-dimension-zero and
lem-sfb-field-groupoid-stabilizer-dimension.
4. Apply lem-sfb-smooth-fibre-image-parameters at z: on an affine neighbourhood U'
of u it supplies functions f_1,...,f_d regular at an etale lift of z, whose zero
scheme Z has dim_z(Z x_F u) = 0. The open restriction U' -> F stays smooth, hence
flat and locally finitely presented. By lem-sfb-stack-fibre-regular-slice-flat,
after shrinking around u the map Z -> F is flat and locally finitely presented;
z and its dimension-zero property survive. Use also
lem-sfb-stack-chartwise-smooth-etale-calculus.
5. Local finite presentation implies local finite type. Apply
lem-sfb-stack-quasifinite-fibre-neighbourhood to z and restrict Z to the resulting
open neighbourhood of u. This retains the point over x and yields Z_x -> F locally
quasi-finite, flat and locally finitely presented. Use open-source locality from
lem-sfb-stack-chartwise-smooth-etale-calculus.
6. Fix a smooth surjective atlas U_0 -> F. Field-extension lifting bounds the index
set of finite-type points by the point set of U_0. Thus W = coproduct_x Z_x is a
scheme in the chosen universe, by def-weil-size-convention and
lem-weil-pbc-scheme-coproduct-family. Stack descent glues the maps on the disjoint
open summands; the diagonal makes this scheme map representable. Open-source locality
gives flatness, local finite presentation and local quasi-finiteness. Its image
contains every finite-type point, so lem-sfb-stack-flat-lfp-finite-type-surjectivity
makes it surjective. Use def-sfb-algebraic-moduli-stack,
lem-sfb-stack-diagonal-space-source-representability,
lem-sfb-stack-chartwise-smooth-etale-calculus and
lem-sfb-representable-lqf-calculus-descent. For an empty stack take the empty coproduct. -/
theorem locallyQuasiFiniteModuliDiagonal_iff_flatLocallyQuasiFiniteAtlas
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) :
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite
        (moduliRelativeDiagonal (moduliBaseStructure F)) ↔
      ∃ (W : Over S) (q : BasedFunctor (discreteModuli (yoneda.obj W)) F),
        IsRepresentableByAlgebraicSpaces q ∧ IsSurjectiveModuliMap q ∧
          ModuliSpaceTest @Flat q ∧ ModuliSpaceTest @LocallyOfFinitePresentation q ∧
          ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite q := by
  sorry

end CategoryTheory
