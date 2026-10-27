/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.SfOpenClosedTriangleData

/-! # Sheaf normalization of the supplied integral recollement maps -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The supplied integral counit and unit are the exact completed sheaf kernel
inclusion and closed unit, through natural identifications of their outer functors.
This statement concerns only the two maps and their sheaf models; it makes no
assertion about distinguished triangles, connecting maps, or Hom vanishing.

Source: current blueprint prop-functor-package.proof.md, clause (3), source
recollement; prop-sf-open-closed-triangle-all-stages.proof.md, integral-stage
sheaf sequence and normalization of the adjunction maps; Stacks 09AH and 015F.
(blueprint: lem-sf-package-integral-recollement-normalization).

Proof: use integral-support-functor-normalization and the completed immersion
pullback comparisons. The datum's pullbacks equal the recorded completed
pullbacks. Its open realization and the normalized support comparison identify
its open extension with ordinary exact open extension. Uniqueness of left
adjoints to this same pullback gives an adjunction-compatible identification;
use this identification, rather than an arbitrary isomorphism of the functors,
to carry the supplied counit to the ordinary counit. For the closed immersion,
use the datum's completed direct-image realization and the normalized ordinary
pullback comparison. Uniqueness of right adjoints identifies the supplied
closed adjunction with the restricted ordinary adjunction and carries its unit.
The ordinary open/closed short exact sequence identifies the open composite
and its counit with the kernel and kernel inclusion of that same closed unit.
Localize these exact module functors termwise, with their standard derived
factorizations. The adjunction-compatible isomorphisms give the two natural
isomorphisms in SfIntegralRecollementNormalization. On the image of every
complex, localization of the module counit and unit is precisely the displayed
factorization formula in that predicate. Thus the two required equations hold
for every representative complex. Fullness of the constructible inclusions
restricts these identifications without changing the maps. All constructions
use adjunctions and the sheaf exact sequence, so also apply to empty strata. -/
theorem sfPackageIntegralRecollementNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    {Z U X : SixFunctorSpace D} [IsSeparated X.obj.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.hom.left]
    (hj : IsOpenImmersion j.hom.left)
    (hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ) :
    letI : LocallyOfFiniteType X.obj.hom := X.property.1
    letI : QuasiCompact X.obj.hom := X.property.2
    let P : SfRecollementPresentation (sfIntegralConstructibleCategory C.l E X.obj.left) :=
      ⟨S.higher.integral.pull j ⋙ S.higher.integral.openExtension j hj,
        S.higher.integral.pull i ⋙ S.higher.integral.direct i,
        (S.higher.integral.openAdjunction j hj).counit,
        (S.higher.integral.pullDirectAdjunction i).unit⟩
    SfIntegralRecollementNormalization C.l E i.hom.left
      (sfRecollementNoetherian D.k X.obj.left) P := by sorry

end WeilConjectures
